# Partial fractions.

# long division of polynomials given by coefficient vectors (constant first)
function _polydivrem(n::Vector{Term}, d::Vector{Term})
    dn = length(d) - 1
    n = vcat(n, _tzeros(max(0, dn - length(n))))
    q = _tzeros(max(length(n) - dn, 1))
    for k in (length(n)-1):-1:dn
        c = cancel(n[k+1] / d[end])
        iszero(c) && continue
        q[k-dn+1] = c
        for j in 0:dn
            n[k-dn+j+1] = cancel(n[k-dn+j+1] - c * d[j+1])
        end
    end
    r = n[1:max(dn, 1)]
    return q, r
end

_frompoly(cs::Vector{Term}, x::Sym) = _add(Term[_mul((c, _pow(x, Num(k - 1)))) for (k, c) in enumerate(cs)])

"""
    apart(f, x)

The partial-fraction decomposition of the rational function `f` in `x`, over
the factors of its denominator that `factor` finds (linear and irreducible
quadratic factors, with multiplicity). Other symbols are parameters.

    apart(1/(n*(K - n)), n)        # 1/(K*n) + 1/(K*(K - n))
"""
function apart(f, x::Sym)
    f = cancel(toterm(f))
    num, den = numerator(f), denominator(f)
    has(den, x) || return expand(f)
    nc, dc = polycoeffs(num, x), polycoeffs(den, x)
    (nc === nothing || dc === nothing) && throw(ArgumentError("apart: $f is not a rational function of $x"))
    q, r = _polydivrem(nc, dc)
    poly = _frompoly(q, x)
    all(iszero, r) && return poly
    c, fs = factor_list(den)
    scalar = c
    xf = Pair{Term,Int}[]
    for (g, k) in fs
        if has(g, x)
            push!(xf, g => k)
        else
            scalar = scalar * _pow(g, Num(k))
        end
    end
    length(xf) == 1 && xf[1].second == 1 && return poly + _frompoly(r, x) / den
    # ansatz: Σ Σ N_ij(x) / g_i^j with deg N_ij < deg g_i
    unknowns = Sym[]
    pieces = Tuple{Vector{Sym},Term,Int}[]   # (coefficient symbols, g, j)
    prodall = _mul(Term[_pow(g, Num(k)) for (g, k) in xf])
    for (g, k) in xf
        m = degree(g, x)
        for j in 1:k
            as = [Sym(gensym(:A), SymInfo(false, false, nothing, false, nothing, false)) for _ in 1:m]
            append!(unknowns, as)
            push!(pieces, (as, g, j))
        end
    end
    lhs = _add(Term[_mul((_frompoly(Term[a for a in as], x), cancel(prodall / _pow(g, Num(j))))) for (as, g, j) in pieces])
    target = cancel(_frompoly(r, x) / scalar)
    lc = polycoeffs(expand(lhs), x)
    tc = polycoeffs(expand(target), x)
    nrow = max(length(lc), length(tc))
    lc = vcat(lc, _tzeros(nrow - length(lc)))
    tc = vcat(tc, _tzeros(nrow - length(tc)))
    A = Term[coeff(lc[i], u, 1) for i in 1:nrow, u in unknowns]
    sol = linsolve(A, tc)
    sol === nothing && throw(ArgumentError("apart: no decomposition found for $f"))
    vals = Dict{Term,Term}(u => s for (u, s) in zip(unknowns, sol))
    parts = Term[poly]
    for (as, g, j) in pieces
        numj = cancel(subs(_frompoly(Term[a for a in as], x), vals))
        iszero(numj) && continue
        push!(parts, _mul((numj, _pow(g, Num(-j)))))
    end
    return _add(parts)
end
