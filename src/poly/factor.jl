# Factorisation over ℚ.
#
# Complete for what textbook models produce, heuristic beyond it:
#   1. rational content and monomial factors come out;
#   2. content with respect to each variable splits off (recursively factored);
#   3. square-free decomposition (Yun) in one variable;
#   4. each square-free part is split by finding factors linear in some
#      variable (candidates from the divisors of the leading and trailing
#      coefficients), quadratics whose discriminant is a perfect square, and
#      polynomials in x^k for k > 1.
# Irreducible univariate polynomials of degree ≥ 3 without rational roots are
# returned whole unless they split this way; full Zassenhaus is on the roadmap.

function yun(p::MP, v::Int)
    out = Pair{MP,Int}[]
    dp = deriv(p, v)
    a = pgcd(p, dp)
    b = divexact(p, a)
    c = divexact(dp, a)
    d = c - deriv(b, v)
    i = 1
    while deg(b, v) > 0
        ai = pgcd(b, d)
        b = divexact(b, ai)
        c = divexact(d, ai)
        d = c - deriv(b, v)
        deg(ai, v) > 0 && push!(out, ai => i)
        i += 1
        i > 200 && break
    end
    return out
end

"""
    factor_poly(p) -> (c, [f₁ => k₁, …])

`p = c * ∏ fᵢ^kᵢ` with `c` rational and each `fᵢ` a primitive integer
polynomial with positive leading coefficient.
"""
function factor_poly(p::MP)
    iszero(p) && return (Q(0), Pair{MP,Int}[])
    c = qcontent(p)
    q = scale(p, inv(c))
    out = Pair{MP,Int}[]
    # monomial factors
    m = [mindeg(q, i) for i in 1:q.nv]
    if any(>(0), m)
        for i in 1:q.nv
            m[i] > 0 && push!(out, mpvar(q.nv, i) => m[i])
        end
        q = MP(q.nv, Dict(e .- m => v for (e, v) in q.t))
    end
    _factor_rec!(out, q, 1)
    # merge equal factors, fix the constant
    merged = Dict{MP,Int}()
    for (f, k) in out
        merged[f] = get(merged, f, 0) + k
    end
    facs = [f => k for (f, k) in merged]
    prodf = mpconst(p.nv, 1)
    for (f, k) in facs
        prodf = prodf * f^k
    end
    cc = divexact(p, prodf)
    cval = (cc !== nothing && isconst(cc)) ? constval(cc) : c
    sort!(facs; by = fk -> (totaldeg(fk.first), nterms(fk.first), string(sort!(collect(keys(fk.first.t))))))
    return (cval, facs)
end

function _factor_rec!(out, p::MP, mult::Int)
    isconst(p) && return
    p = mpnormalize(p)
    vs = vars_in(p)
    if totaldeg(p) == 1
        push!(out, p => mult)
        return
    end
    for v in vs
        cv = content_in(p, v)
        if !isconst(cv)
            _factor_rec!(out, cv, mult)
            _factor_rec!(out, mpnormalize(divexact(p, cv)), mult)
            return
        end
    end
    v = vs[argmin([deg(p, w) for w in vs])]
    sq = yun(p, v)
    if length(sq) > 1 || (length(sq) == 1 && sq[1].second > 1)
        rest = p
        for (q, k) in sq
            _factor_rec!(out, mpnormalize(q), mult * k)
            rest = divexact(rest, q^k)
        end
        rest !== nothing && !isconst(rest) && _factor_rec!(out, mpnormalize(rest), mult)
        return
    end
    for q in _split_sqfree(p)
        push!(out, mpnormalize(q) => mult)
    end
end

function _intdivisors(n::BigInt; cap::Int = 400)
    n = abs(n)
    iszero(n) && return BigInt[1]
    n > big(10)^12 && return BigInt[1, n]
    ds = BigInt[]
    i = big(1)
    while i * i <= n
        if n % i == 0
            push!(ds, i)
            i * i != n && push!(ds, div(n, i))
            length(ds) > cap && break
        end
        i += 1
    end
    return sort!(ds)
end

# polynomial divisors (up to sign and rational scaling) of p, which is free of v
function _poly_divisors(p::MP; cap::Int = 300)
    c, facs = factor_poly(p)
    ints = _intdivisors(numerator(abs(c)))
    divs = MP[mpconst(p.nv, 1)]
    for (f, k) in facs
        new = MP[]
        for d in divs, j in 0:k
            push!(new, d * f^j)
            length(new) > cap && break
        end
        divs = new
    end
    out = MP[]
    for d in divs, n in ints
        push!(out, scale(d, n))
        length(out) > cap && break
    end
    return out
end

function _split_sqfree(p::MP)
    totaldeg(p) <= 1 && return [p]
    vs = vars_in(p)
    degs = [deg(p, w) for w in vs]
    v = vs[argmin(degs)]
    d = deg(p, v)
    d == 1 && return [p]
    # a polynomial in v^g
    g = reduce(gcd, (e[v] for e in keys(p.t)); init = 0)
    if g > 1
        q = deflate(p, v, g)
        parts = _split_sqfree(q)
        if length(parts) > 1
            return reduce(vcat, (_split_sqfree(mpnormalize(inflate(f, v, g))) for f in parts))
        end
    end
    if d == 2
        r = _split_quadratic(p, v)
        r !== nothing && return r
        length(vs) == 1 && return [p]
    end
    # linear factors a*v + b with a | lc, b | tc
    cs = coeffs(p, v)
    lcp, tcp = cs[end], cs[1]
    if !iszero(tcp)
        A = _poly_divisors(lcp)
        B = _poly_divisors(tcp)
        tries = 0
        for a in A, b in B, s in (1, -1)
            tries += 1
            tries > 4000 && break
            f = mpvar(p.nv, v) * a + scale(b, s)
            q = divexact(p, f)
            if q !== nothing
                return vcat([mpnormalize(f)], _split_sqfree(mpnormalize(q)))
            end
        end
    end
    # other variables, if any, may expose a split
    for w in vs
        w == v && continue
        deg(p, w) == 2 || continue
        r = _split_quadratic(p, w)
        r !== nothing && return r
    end
    return [p]
end

function _split_quadratic(p::MP, v::Int)
    cs = coeffs(p, v)
    length(cs) == 3 || return nothing
    c, b, a = cs
    D = b * b - scale(a * c, 4)
    s = mpsqrt(D)
    s === nothing && return nothing
    x = mpvar(p.nv, v)
    f1 = scale(a * x, 2) + b - s
    f2 = scale(a * x, 2) + b + s
    pp(f) = (cc = content_in(f, v); mpnormalize(divexact(f, cc)))
    return [pp(f1), pp(f2)]
end
