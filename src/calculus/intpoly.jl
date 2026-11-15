# Algebra for the integrators: the coefficient field ℚ(y₁, …, yₖ) of the
# parameters, univariate polynomials over a field, subresultants over a
# polynomial ring, and sparse exact linear systems.

# ---- rational functions in the parameters ----------------------------------------

"""
    RF(n, d)

An element `n/d` of ℚ(y₁, …, yₖ): `n` and `d` are coprime polynomials (`MP`)
and `d` is primitive with integer coefficients and a positive leading
coefficient, so equal elements are structurally equal.
"""
struct RF
    n::MP
    d::MP
end
function rf(n::MP, d::MP)
    iszero(d) && throw(DivideError())
    iszero(n) && return RF(MP(n.nv), mpconst(n.nv, 1))
    if !isconst(d) && !isconst(n)
        g = pgcd(n, d)
        if !isconst(g)
            n = divexact(n, g)
            d = divexact(d, g)
        end
    end
    c = qcontent(d)
    isone(c) && return RF(n, d)
    return RF(scale(n, inv(c)), scale(d, inv(c)))
end
rf(n::MP) = RF(n, mpconst(n.nv, 1))
rfconst(nv::Int, c) = RF(mpconst(nv, c), mpconst(nv, 1))
Base.zero(a::RF) = rfconst(a.n.nv, 0)
Base.one(a::RF) = rfconst(a.n.nv, 1)
Base.iszero(a::RF) = iszero(a.n)
Base.isone(a::RF) = a.n == a.d
Base.:(==)(a::RF, b::RF) = a.n == b.n && a.d == b.d
Base.hash(a::RF, h::UInt) = hash(a.d, hash(a.n, h))
function Base.:+(a::RF, b::RF)
    iszero(a) && return b
    iszero(b) && return a
    a.d == b.d && return rf(a.n + b.n, a.d)
    return rf(a.n * b.d + b.n * a.d, a.d * b.d)
end
Base.:-(a::RF) = RF(-a.n, a.d)
Base.:-(a::RF, b::RF) = a + (-b)
function Base.:*(a::RF, b::RF)
    (iszero(a) || iszero(b)) && return zero(a)
    return rf(a.n * b.n, a.d * b.d)
end
Base.inv(a::RF) = rf(a.d, a.n)
Base.:/(a::RF, b::RF) = rf(a.n * b.d, a.d * b.n)
Base.:*(a::RF, k::Integer) = RF(scale(a.n, k), a.d)
Base.:*(k::Integer, a::RF) = a * k
Base.:/(a::RF, k::Integer) = rf(a.n, scale(a.d, k))

# coefficient (polynomial in the parameters, as an MP) -> field element
_tocoef(z::Q, p::MP) = constval(p)
_tocoef(z::RF, p::MP) = rf(p)
_coefterm(c::Q, g) = Num(c)
_coefterm(c::RF, g) = _quot(_mp2term(c.n, g), _mp2term(c.d, g))

# ---- univariate polynomials over a field ----------------------------------------

"""
    UP{C}

A univariate polynomial with coefficients in a field `C` (`Q` or `RF`),
constant term first, without trailing zeros; `z` is the field's zero.
"""
struct UP{C}
    c::Vector{C}
    z::C
    function UP(c::Vector{C}, z::C) where {C}
        n = length(c)
        while n > 0 && iszero(c[n])
            n -= 1
        end
        return new{C}(n == length(c) ? c : c[1:n], z)
    end
end
udeg(p::UP) = length(p.c) - 1
Base.iszero(p::UP) = isempty(p.c)
ulc(p::UP) = p.c[end]
ucoef(p::UP, k::Int) = k + 1 <= length(p.c) ? p.c[k+1] : p.z
uconst(z, a) = UP([a], z)
uone(z) = UP([one(z)], z)
Base.:(==)(a::UP, b::UP) = a.c == b.c

function Base.:+(a::UP, b::UP)
    n = max(length(a.c), length(b.c))
    return UP([ucoef(a, k) + ucoef(b, k) for k in 0:n-1], a.z)
end
Base.:-(a::UP) = UP([-c for c in a.c], a.z)
function Base.:-(a::UP, b::UP)
    n = max(length(a.c), length(b.c))
    return UP([ucoef(a, k) - ucoef(b, k) for k in 0:n-1], a.z)
end
function Base.:*(a::UP, b::UP)
    (iszero(a) || iszero(b)) && return UP(typeof(a.z)[], a.z)
    r = fill(a.z, length(a.c) + length(b.c) - 1)
    for (i, x) in enumerate(a.c)
        iszero(x) && continue
        for (j, y) in enumerate(b.c)
            iszero(y) && continue
            r[i+j-1] = r[i+j-1] + x * y
        end
    end
    return UP(r, a.z)
end
uscale(a::UP, c) = iszero(c) ? UP(typeof(a.z)[], a.z) : UP([c * x for x in a.c], a.z)
function Base.:^(a::UP, n::Integer)
    r = uone(a.z)
    for _ in 1:n
        r = r * a
    end
    return r
end
uderiv(a::UP) = length(a.c) <= 1 ? UP(typeof(a.z)[], a.z) : UP([a.c[k+1] * k for k in 1:length(a.c)-1], a.z)
umonic(a::UP) = iszero(a) ? a : uscale(a, inv(ulc(a)))
# x^k * a
ushift(a::UP, k::Int) = iszero(a) ? a : UP(vcat(fill(a.z, k), a.c), a.z)

function udivrem(a::UP, b::UP)
    iszero(b) && throw(DivideError())
    db = udeg(b)
    r = copy(a.c)
    length(r) <= db && return (UP(typeof(a.z)[], a.z), a)
    lb = ulc(b)
    q = fill(a.z, length(r) - db)
    for k in (length(r)-1):-1:db
        c = r[k+1]
        iszero(c) && continue
        c = c / lb
        q[k-db+1] = c
        for j in 0:db
            r[k-db+j+1] = r[k-db+j+1] - c * b.c[j+1]
        end
    end
    return (UP(q, a.z), UP(r[1:db], a.z))
end
udiv(a::UP, b::UP) = udivrem(a, b)[1]

function ugcd(a::UP, b::UP)
    while !iszero(b)
        a, b = b, udivrem(a, b)[2]
    end
    return umonic(a)
end

# (s, t, g) with s a + t b = g = gcd(a, b), monic
function ugcdex(a::UP, b::UP)
    z = a.z
    zero_ = UP(typeof(z)[], z)
    r0, r1 = a, b
    s0, s1 = uone(z), zero_
    t0, t1 = zero_, uone(z)
    while !iszero(r1)
        q, r = udivrem(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    end
    iszero(r0) && return (s0, t0, r0)
    k = inv(ulc(r0))
    return (uscale(s0, k), uscale(t0, k), uscale(r0, k))
end

# (s, t) with s a + t b = c and deg s < deg b (gcd(a, b) must divide c)
function udiophant(a::UP, b::UP, c::UP)
    s, t, g = ugcdex(a, b)
    q, r = udivrem(c, g)
    iszero(r) || return nothing
    s = s * q
    t = t * q
    if !iszero(s) && udeg(s) >= udeg(b)
        q2, s = udivrem(s, b)
        t = t + q2 * a
    end
    return (s, t)
end

# Yun's square-free factorisation: [f₁, f₂, …] with a = lc(a) ∏ fᵢ^i
function usqfree(a::UP)
    out = typeof(a)[]
    udeg(a) <= 0 && return out
    b = uderiv(a)
    c = ugcd(a, b)
    w = udiv(a, c)
    y = udiv(b, c)
    z = y - uderiv(w)
    while udeg(w) > 0
        g = ugcd(w, z)
        push!(out, g)
        w = udiv(w, g)
        y = udiv(z, g)
        z = y - uderiv(w)
        length(out) > 500 && break
    end
    return out
end

# polynomial (MP over the generators g) in variable ix -> UP over the field of z
function _mp2up(p::MP, ix::Int, z)
    cs = coeffs(p, ix)
    return UP([_tocoef(z, c) for c in cs], z)
end

# UP -> polynomial term in x
_up2term(p::UP, x::Term, g) =
    _add(Term[_mul((_coefterm(c, g), _pow(x, Num(k - 1)))) for (k, c) in enumerate(p.c) if !iszero(c)])

# UP -> MP in nvt variables (the coefficients' variables, then extra ones), with
# x as variable ix, denominators cleared
_embed(p::MP, nvt::Int) = p.nv == nvt ? p : MP(nvt, Dict(vcat(e, zeros(Int, nvt - p.nv)) => c for (e, c) in p.t))
function _up2mp(p::UP, ix::Int, nvt::Int)
    iszero(p) && return MP(nvt)
    if p.z isa Q
        L = reduce(lcm, (denominator(c) for c in p.c); init = big(1))
        r = MP(nvt)
        for (k, c) in enumerate(p.c)
            iszero(c) && continue
            r = r + scale(mpvar(nvt, ix, k - 1), c * L)
        end
        return r
    end
    L = p.c[1].d
    for c in p.c
        iszero(c) && continue
        L = divexact(L * c.d, pgcd(L, c.d))
    end
    r = MP(nvt)
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        m = divexact(L, c.d) * c.n
        r = r + _embed(m, nvt) * mpvar(nvt, ix, k - 1)
    end
    return r
end

# Term polynomials in x -> UPs over one shared field (generators other than x
# must be free of x); nothing if one is not a polynomial in x
function _terms2ups(ps::Vector{Term}, x::Sym)
    ys = Term[_inner(cancel, p) for p in ps]
    g = Gens()
    _gen!(g, x)
    for y in ys
        _collect_gens!(g, y)
    end
    for t in g.list
        t != x && has(t, x) && return nothing
    end
    nv = nvars(g)
    ix = g.idx[x]
    z = nv == 1 ? Q(0) : rfconst(nv, 0)
    ups = UP[]
    for y in ys
        n, d = _rf(y, g)
        deg(d, ix) > 0 && return nothing
        u = _mp2up(n, ix, z)
        dc = _tocoef(z, d)
        push!(ups, uscale(u, inv(dc)))
    end
    return (ups, g)
end

# ---- subresultants --------------------------------------------------------------

# lc(b)^(δ+1) a mod b in variable v, δ = deg a - deg b
function _pprem(a::MP, b::MP, v::Int)
    db = deg(b, v)
    lb = lc(b, v)
    δ = deg(a, v) - db
    r = a
    steps = 0
    while !iszero(r) && deg(r, v) >= db
        dr = deg(r, v)
        lr = lc(r, v)
        r = lb * r - lr * mpvar(a.nv, v, dr - db) * b
        steps += 1
    end
    return steps <= δ ? r * lb^(δ + 1 - steps) : r
end

"""
    _subresultant(A, B, v) -> (resultant, [R₀, R₁, …, Rₖ])

The subresultant PRS of `A` and `B` (polynomials over ℚ[other variables],
deg A ≥ deg B in `v`) and their resultant (Bronstein, *Symbolic Integration I*,
§1.5).
"""
function _subresultant(A::MP, B::MP, v::Int)
    nv = A.nv
    R = MP[A, B]                 # R[i+1] = R_i
    rs = MP[]                    # rs[i] = r_i
    βs = MP[]
    δs = Int[]
    γ = mpconst(nv, -1)
    δ = deg(A, v) - deg(B, v)
    push!(δs, δ)
    push!(βs, mpconst(nv, isodd(δ + 1) ? -1 : 1))
    i = 1
    while !iszero(R[i+1])
        ri = lc(R[i+1], v)
        push!(rs, ri)
        rem = _pprem(R[i], R[i+1], v)
        Rn = divexact(rem, βs[i])
        Rn === nothing && return nothing
        push!(R, Rn)
        i += 1
        δp = δs[i-1]
        num = (-rs[i-1])^δp
        if δp <= 1
            γ = num * γ^(1 - δp)
        else
            γ = divexact(num, γ^(δp - 1))
            γ === nothing && return nothing
        end
        δi = deg(R[i], v) - deg(R[i+1], v)
        push!(δs, δi)
        push!(βs, -rs[i-1] * γ^max(δi, 0))
    end
    k = i - 1
    seq = R[1:k+1]
    deg(R[k+1], v) > 0 && return (MP(nv), seq)
    deg(R[k], v) == 1 && return (R[k+1], seq)
    s = 1
    c = rfconst(nv, 1)
    for j in 1:k-1
        isodd(deg(R[j], v)) && isodd(deg(R[j+1], v)) && (s = -s)
        f = rf(βs[j], rs[j]^(1 + δs[j]))
        dj = deg(R[j+1], v)
        for _ in 1:dj
            c = c * f
        end
        e = deg(R[j], v) - deg(R[j+2], v)
        rj = rf(rs[j])
        if e >= 0
            for _ in 1:e
                c = c * rj
            end
        else
            for _ in 1:(-e)
                c = c / rj
            end
        end
    end
    res = c * rf(R[k+1]^deg(R[k], v))
    isconst(res.d) || return nothing
    return (scale(res.n, s * inv(constval(res.d))), seq)
end

# ---- sparse linear systems ------------------------------------------------------

"""
    _sparse_solve(rows, ncols, z) -> Vector or nothing

Solve the linear system whose equations are `rows` (each a `Dict` from column to
coefficient, column 0 holding the right-hand side) over the field of `z`, with
free unknowns set to zero; `nothing` if it is inconsistent.
"""
function _sparse_solve(rows, ncols::Int, z)
    pivots = Dict{Int,Dict{Int,typeof(z)}}()
    rank = Dict{Int,Int}()              # pivot column -> creation index
    order = Int[]
    for r0 in rows
        r = copy(r0)
        while true
            best = 0
            bi = typemax(Int)
            for (c, v) in r
                c == 0 && continue
                iszero(v) && continue
                k = get(rank, c, 0)
                if k > 0 && k < bi
                    bi = k
                    best = c
                end
            end
            best == 0 && break
            f = r[best]
            for (c, v) in pivots[best]
                nv = get(r, c, z) - f * v
                if iszero(nv)
                    delete!(r, c)
                else
                    r[c] = nv
                end
            end
            delete!(r, best)
        end
        filter!(p -> !iszero(p.second), r)
        isempty(r) && continue
        cols = [c for c in keys(r) if c != 0]
        isempty(cols) && return nothing          # 0 = nonzero
        pc = minimum(cols)
        inv_ = inv(r[pc])
        for c in collect(keys(r))
            r[c] = r[c] * inv_
        end
        pivots[pc] = r
        push!(order, pc)
        rank[pc] = length(order)
    end
    sol = fill(z, ncols)
    for c in reverse(order)
        r = pivots[c]
        v = get(r, 0, z)
        for (j, a) in r
            (j == 0 || j == c) && continue
            iszero(sol[j]) && continue
            v = v - a * sol[j]
        end
        sol[c] = v
    end
    return sol
end

# value of a parameter polynomial at a point
function _mpeval(p::MP, vals::Vector{Q})
    s = Q(0)
    for (e, c) in p.t
        t = c
        for (i, k) in enumerate(e)
            k == 0 && continue
            t *= vals[i]^k
        end
        s += t
    end
    return s
end
