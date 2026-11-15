# Integration of rational functions (complete): the polynomial part directly,
# the rational part by Hermite reduction (Mack's linear version), the
# logarithmic part by the Lazard–Rioboo–Trager resultant algorithm, with
# conjugate pairs of complex residues turned into real logarithms and
# arctangents of polynomials (Rioboo), so no spurious discontinuities appear.
# Coefficients live in ℚ(parameters). References: M. Bronstein, *Symbolic
# Integration I*, ch. 2.

const _TSYM = Sym(:_t, SymInfo(false, false, nothing, false, nothing, false))

# rational in x, with x-free generators otherwise
function _isratfun(f::Term, x::Sym)
    g = _safe(y -> _collect_gens!(Gens(), _inner(cancel, y)), f)
    g === nothing && return false
    return all(t -> t == x || !has(t, x), g.list) && any(t -> t == x, g.list)
end

"""
    _ratint(f, x) -> Term or nothing

An antiderivative of the rational function `f` of `x` (other symbols and
x-free generators are parameters).
"""
function _ratint(f::Term, x::Sym)
    n, d, g, _ = ratfun(f)
    haskey(g.idx, x) || return _mul((f, x))
    for t in g.list
        t != x && has(t, x) && return nothing
    end
    ix = g.idx[x]
    nv = nvars(g)
    z = nv == 1 ? Q(0) : rfconst(nv, 0)
    N = _mp2up(n, ix, z)
    D = _mp2up(d, ix, z)
    out = Term[]
    q, r = udivrem(N, D)
    push!(out, _polyint_up(q, x, g))
    iszero(r) && return _add(out)
    # Hermite reduction
    parts, A, Dr = _hermite(r, D)
    for (B, V, j) in parts
        iszero(B) && continue
        push!(out, _mul((_up2term(B, x, g), _pow(_up2term(V, x, g), Num(-j)))))
    end
    q2, A = udivrem(A, Dr)
    push!(out, _polyint_up(q2, x, g))
    if !iszero(A)
        G = ugcd(A, Dr)
        if udeg(G) > 0
            A = udiv(A, G)
            Dr = udiv(Dr, G)
        end
        L = _lrt(A, Dr, x, ix, g)
        if L === nothing || has(L, _TSYM)
            At, Dt = _up2term(A, x, g), _up2term(Dr, x, g)
            L2 = _logpart_real(At, Dt, x)
            if L2 !== nothing && _verify(L2, At / Dt, x)
                L = L2
            end
        end
        L === nothing && return nothing
        push!(out, L)
    end
    return _add(out)
end

function _polyint_up(p::UP, x::Sym, g)
    iszero(p) && return ZERO
    return _add(Term[_mul((_coefterm(c, g), Num(Q(1) // k), _pow(x, Num(k)))) for (k, c) in enumerate(p.c) if !iszero(c)])
end

# Hermite reduction: ∫ A/D = Σ B/V^j + ∫ A'/D' with D' square-free
function _hermite(A::UP, D::UP)
    parts = Tuple{typeof(A),typeof(A),Int}[]
    fs = usqfree(D)
    for i in 2:length(fs)
        V = fs[i]
        udeg(V) > 0 || continue
        U = udiv(D, V^i)
        dV = uderiv(V)
        for j in (i-1):-1:1
            rhs = uscale(A, inv(one(A.z) * (-j)))
            bc = udiophant(U * dV, V, rhs)
            bc === nothing && error("Hermite reduction: no solution")
            B, C = bc
            push!(parts, (B, V, j))
            A = uscale(C, one(A.z) * (-j)) - U * uderiv(B)
        end
        D = U * V
    end
    return (parts, A, D)
end

# the logarithmic part Σ_{Q(α)=0} α log(S(α, x)) of ∫ A/D, D square-free,
# deg A < deg D
function _lrt(A::UP, D::UP, x::Sym, ix::Int, g)
    nv = nvars(g)
    nt = nv + 1
    Am = _up2mp(A, ix, nt)
    Dm = _up2mp(D, ix, nt)
    # Am/Dm = κ A/D for a constant κ (denominators were cleared separately);
    # the log part of A/D is that of Am/Dm divided by κ
    κ = _field_of(lc(Am, ix), A.z) / ulc(A) / (_field_of(lc(Dm, ix), A.z) / ulc(D))
    tv = mpvar(nt, nt)
    Bm = Am - tv * deriv(Dm, ix)
    sr = _subresultant(Dm, Bm, ix)
    sr === nothing && return nothing
    R, seq = sr
    iszero(R) && return nothing
    deg(R, nt) > 0 || return nothing
    R = divexact(R, content_in(R, nt))
    gt = Gens(vcat(g.list, Term[_TSYM]), merge(g.idx, Dict{Term,Int}(_TSYM => nt)))
    degD = udeg(D)
    out = Term[]
    for (Qi, i) in yun(R, nt)
        deg(Qi, nt) > 0 || continue
        if i == degD
            S = Dm
        else
            k = findfirst(s -> !iszero(s) && deg(s, ix) == i, seq)
            k === nothing && return nothing
            S = seq[k]
            lcS = lc(S, ix)
            if deg(lcS, nt) > 0
                lcp = divexact(lcS, content_in(lcS, nt))
                for (Aj, j) in yun(lcp, nt)
                    gg = pgcd(Aj, Qi)
                    deg(gg, nt) > 0 || continue
                    gg = divexact(gg, content_in(gg, nt))
                    S2 = divexact(S, gg^j)
                    S2 === nothing && return nothing
                    S = S2
                end
            end
        end
        _, fs = factor_poly(Qi)
        St = _mp2term(S, gt)
        for (P, _) in fs
            deg(P, nt) > 0 || continue
            r = _lrt_term(_mp2term(P, gt), St, x, deg(P, nt))
            r === nothing && return nothing
            push!(out, r)
        end
    end
    return _mul((_pow(_coefterm(κ, g), MONE), _add(out)))
end

# an MP in nt variables whose extra variables do not occur, as a field element
_field_of(p::MP, z::Q) = constval(p)
_field_of(p::MP, z::RF) = rf(MP(z.n.nv, Dict(e[1:z.n.nv] => c for (e, c) in p.t)))

# Σ_{P(α)=0} α log(S(α, x)) for one irreducible factor P of the resultant
function _lrt_term(P::Term, S::Term, x::Sym, dP::Int)
    t = _TSYM
    cs = polycoeffs(P, t)
    cs === nothing && return nothing
    if dP == 1
        α = cancel(-cs[1] / cs[2])
        return _mul((α, _log(_lognice(subs(S, t => α), x))))
    elseif dP == 2
        c, b, a = cs
        Δ = simplify(b^2 - 4 * a * c)
        Z = Sym(gensym(:Z), SymInfo(false, false, nothing, false, nothing, false))
        Sz = expand(subs(S, t => (-b + Z) / (2a)))
        zc = polycoeffs(Sz, Z)
        zc === nothing && return nothing
        U = cancel(_add(Term[_mul((zc[k+1], _pow(Δ, Num(k ÷ 2)))) for k in 0:2:length(zc)-1]))
        V = cancel(_add(Term[_mul((zc[k+1], _pow(Δ, Num(k ÷ 2)))) for k in 1:2:length(zc)-1]))
        p = cancel(-b / (2a))
        sΔ = sign_of(Δ)
        if (sΔ & (POS | CPX)) == 0 && sΔ != ZER
            w = simplify(sqrt(-Δ))
            # clear parameter denominators (scaling U and V together changes
            # the logarithm by a constant and the arctangent not at all)
            dn = cancel(denominator(cancel(U + Z * V)))
            U2, V2 = cancel(U * dn), cancel(V * dn)
            lg = iszero(p) ? ZERO : _mul((p, _log(_lognice(cancel(U2^2 + _mul((MONE, Δ, V2^2))), x))))
            at = _logtoatan(U2, cancel(w * V2), x)
            at === nothing && return nothing
            return lg + _mul((w, _pow(2a, MONE), at))
        end
        sq = simplify(sqrt(Δ))
        lg = iszero(p) ? ZERO : _mul((p, _log(_lognice(cancel(U^2 - Δ * V^2), x))))
        return lg + _mul((sq, _pow(2a, MONE), _log(_lognice(U + sq * V, x)) - _log(_lognice(U - sq * V, x))))
    end
    # higher degree: a sum over the roots
    out = Term[]
    for k in 1:dP
        α = RootOf(P, t, k)
        push!(out, _mul((α, _log(cancel(subs(S, t => α))))))
    end
    return _add(out)
end

# a tidy argument for a logarithm of a polynomial in x: the numerator, with
# rational content and sign removed
function _lognice(a::Term, x::Sym)
    a = cancel(a)
    n = numerator(a)
    cs = polycoeffs(n, x)
    if cs !== nothing && all(c -> c isa Num && c.val isa Q, cs)
        nums = BigInt[numerator(c.val) for c in cs if !iszero(c)]
        dens = BigInt[denominator(c.val) for c in cs if !iszero(c)]
        k = Q(gcd(nums), lcm(dens))
        cs[end].val < 0 && (k = -k)
        n = cancel(n / k)
    elseif cs !== nothing && !iszero(cs[end]) && !has(cs[end], x)
        n = cancel(n / cs[end])
    end
    s = sign_of(n)
    (s & (POS | CPX)) == 0 && s != ZER && (n = cancel(-n))
    return n
end

# Rioboo: a sum of arctangents of polynomials with the derivative of
# i log((A + iB)/(A - iB)); A, B polynomials in x
function _logtoatan(A::Term, B::Term, x::Sym)
    r = _terms2ups(Term[A, B], x)
    r === nothing && return nothing
    (ua, ub), g = r
    acc = Term[]
    _l2a!(acc, ua, ub, x, g, 0)
    return _add(acc)
end
function _l2a!(acc, A::UP, B::UP, x, g, depth)
    depth > 50 && error("LogToAtan: no termination")
    iszero(B) && return
    q, r = udivrem(A, B)
    if iszero(r)
        udeg(q) > 0 && push!(acc, _mul((TWO, _fncall(:atan, Term[_up2term(q, x, g)]))))
        return
    end
    if udeg(A) < udeg(B)
        return _l2a!(acc, -B, A, x, g, depth + 1)
    end
    D, C, G = ugcdex(B, -A)
    num = udiv(A * D + B * C, G)
    udeg(num) > 0 && push!(acc, _mul((TWO, _fncall(:atan, Term[_up2term(num, x, g)]))))
    return _l2a!(acc, D, C, x, g, depth + 1)
end

# ---- real factorisations the rational factorisation leaves whole ---------------

# a square-free polynomial in x with rational coefficients that is a
# biquadratic quartic or a binomial cubic, as real factors of degree ≤ 2
function _realsplit(g::Term, x::Sym)
    cs = polycoeffs(g, x)
    (cs === nothing || !all(c -> c isa Num && c.val isa Q, cs)) && return nothing
    n = length(cs) - 1
    cs = Term[cancel(c / cs[end]) for c in cs]
    if n == 4 && iszero(cs[2]) && iszero(cs[4])
        q, p = cs[1], cs[3]
        disc = p^2 - 4q
        if disc.val >= 0
            sq = sqrt(disc)
            return Term[x^2 - (-p + sq) / 2, x^2 - (-p - sq) / 2]
        elseif q.val > 0
            rq = sqrt(q)
            r = sqrt(2rq - p)
            return Term[x^2 - r * x + rq, x^2 + r * x + rq]
        end
    elseif n == 3 && iszero(cs[2]) && iszero(cs[3])
        q = cs[1]
        r = q.val > 0 ? cbrt(q) : -cbrt(-q)
        return Term[x + r, x^2 - r * x + r^2]
    end
    return nothing
end

# ∫ A/D for D square-free, by partial fractions over real factors of degree ≤ 2
function _logpart_real(A::Term, D::Term, x::Sym)
    _, fs = factor_list(D)
    facs = Term[]
    for (g, k) in fs
        has(g, x) || continue
        k == 1 || return nothing
        d = degree(g, x)
        d === nothing && return nothing
        if d <= 2
            push!(facs, g)
        else
            s = _realsplit(g, x)
            s === nothing && return nothing
            append!(facs, s)
        end
    end
    prodall = _mul(facs)
    κ = cancel(D / prodall)
    has(κ, x) && return nothing
    unknowns = Sym[]
    nums = Term[]
    for g in facs
        m = degree(g, x)
        as = Sym[_isym(:A) for _ in 1:m]
        append!(unknowns, as)
        push!(nums, _add(Term[_mul((a, _pow(x, Num(k - 1)))) for (k, a) in enumerate(as)]))
    end
    lhs = _add(Term[_mul(Term[nums[i]; [facs[j] for j in eachindex(facs) if j != i]]) for i in eachindex(facs)])
    sol = _undetermined(lhs - A / κ, unknowns, x)
    sol === nothing && return nothing
    out = Term[]
    for (g, N) in zip(facs, nums)
        cg = polycoeffs(g, x)
        cn = polycoeffs(simplify(subs(N, sol)), x)
        cn === nothing && return nothing
        if length(cg) == 2
            push!(out, _mul((cn[1], _pow(cg[2], MONE), _log(g))))
        else
            C = cn[1]
            B = length(cn) >= 2 ? cn[2] : ZERO
            push!(out, _int_quadpiece(B, C, cg[3], cg[2], cg[1], g, x))
        end
    end
    return _add(out)
end

# ∫ (B x + C)/(a x² + b x + c) dx
function _int_quadpiece(B, C, a, b, c, g, x)
    out = Term[]
    iszero(B) || push!(out, _mul((B, _pow(2a, MONE), _log(g))))
    k = simplify(C - B * b / (2a))
    iszero(k) && return _add(out)
    Δ = simplify(4 * a * c - b^2)
    s = sign_of(Δ)
    if (s & (NEG | ZER | CPX)) == 0
        sq = simplify(sqrt(Δ))
        push!(out, _mul((k, TWO, _pow(sq, MONE), _fncall(:atan, Term[expand((2a * x + b) / sq)]))))
    else
        sq = simplify(sqrt(-Δ))
        push!(out, _mul((k, _pow(sq, MONE), _log(2a * x + b - sq) - _log(2a * x + b + sq))))
    end
    return _add(out)
end
