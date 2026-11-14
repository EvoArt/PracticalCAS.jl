# Sparse multivariate polynomials over ℚ.
#
# An `MP` holds a fixed number of variables (indices into a generator list kept
# by the caller) and a dictionary from exponent vectors to coefficients. Monomials
# are ordered lexicographically on the exponent vectors (variable 1 most
# significant). GCDs use the recursive primitive PRS, which is plenty for the
# sizes of textbook models.

struct MP
    nv::Int
    t::Dict{Vector{Int},Q}
end
MP(nv::Int) = MP(nv, Dict{Vector{Int},Q}())
mpconst(nv::Int, c) = iszero(c) ? MP(nv) : MP(nv, Dict(zeros(Int, nv) => Q(c)))
function mpvar(nv::Int, i::Int, k::Int = 1)
    e = zeros(Int, nv)
    e[i] = k
    return MP(nv, Dict(e => Q(1)))
end

Base.iszero(p::MP) = isempty(p.t)
Base.copy(p::MP) = MP(p.nv, copy(p.t))
Base.:(==)(a::MP, b::MP) = a.t == b.t
Base.hash(a::MP, h::UInt) = hash(a.t, h)
nterms(p::MP) = length(p.t)
isconst(p::MP) = all(e -> all(iszero, e), keys(p.t))
constval(p::MP) = iszero(p) ? Q(0) : p.t[zeros(Int, p.nv)]

function _addto!(d::Dict{Vector{Int},Q}, e::Vector{Int}, c::Q)
    v = get(d, e, Q(0)) + c
    if iszero(v)
        delete!(d, e)
    else
        d[e] = v
    end
end

function Base.:+(a::MP, b::MP)
    r = copy(a.t)
    for (e, c) in b.t
        _addto!(r, e, c)
    end
    return MP(a.nv, r)
end
Base.:-(a::MP) = MP(a.nv, Dict(e => -c for (e, c) in a.t))
Base.:-(a::MP, b::MP) = a + (-b)
function Base.:*(a::MP, b::MP)
    r = Dict{Vector{Int},Q}()
    for (ea, ca) in a.t, (eb, cb) in b.t
        _addto!(r, ea .+ eb, ca * cb)
    end
    return MP(a.nv, r)
end
scale(a::MP, c) = iszero(c) ? MP(a.nv) : MP(a.nv, Dict(e => v * Q(c) for (e, v) in a.t))
function Base.:^(a::MP, n::Integer)
    n == 0 && return mpconst(a.nv, 1)
    r = a
    for _ in 2:n
        r = r * a
    end
    return r
end

deg(p::MP, i::Int) = iszero(p) ? -1 : maximum(e[i] for e in keys(p.t))
totaldeg(p::MP) = iszero(p) ? -1 : maximum(sum(e) for e in keys(p.t))
vars_in(p::MP) = [i for i in 1:p.nv if any(e -> e[i] > 0, keys(p.t))]
mindeg(p::MP, i::Int) = iszero(p) ? 0 : minimum(e[i] for e in keys(p.t))

# coefficients in variable i: cs[k+1] is the coefficient of x_i^k
function coeffs(p::MP, i::Int)
    d = deg(p, i)
    cs = [MP(p.nv) for _ in 0:max(d, 0)]
    for (e, c) in p.t
        k = e[i]
        f = copy(e)
        f[i] = 0
        cs[k+1].t[f] = c
    end
    return cs
end
lc(p::MP, i::Int) = coeffs(p, i)[end]

function from_coeffs(cs::Vector{MP}, i::Int)
    nv = cs[1].nv
    r = Dict{Vector{Int},Q}()
    for (k, c) in enumerate(cs), (e, v) in c.t
        f = copy(e)
        f[i] += k - 1
        _addto!(r, f, v)
    end
    return MP(nv, r)
end

function deriv(p::MP, i::Int)
    r = Dict{Vector{Int},Q}()
    for (e, c) in p.t
        e[i] == 0 && continue
        f = copy(e)
        f[i] -= 1
        _addto!(r, f, c * e[i])
    end
    return MP(p.nv, r)
end

leadexp(p::MP) = maximum(keys(p.t))

"""
    divexact(a, b) -> MP or nothing

`a / b` if `b` divides `a` exactly, otherwise `nothing`.
"""
function divexact(a::MP, b::MP)
    iszero(b) && throw(DivideError())
    iszero(a) && return MP(a.nv)
    lb = leadexp(b)
    cb = b.t[lb]
    q = Dict{Vector{Int},Q}()
    r = copy(a.t)
    steps = 0
    while !isempty(r)
        lr = maximum(keys(r))
        all(lr .>= lb) || return nothing
        e = lr .- lb
        c = r[lr] / cb
        _addto!(q, e, c)
        for (eb, vb) in b.t
            _addto!(r, e .+ eb, -c * vb)
        end
        steps += 1
        steps > 100_000 && return nothing
    end
    return MP(a.nv, q)
end

# pseudo-remainder of a by b in variable i
function prem(a::MP, b::MP, i::Int)
    db = deg(b, i)
    lb = lc(b, i)
    r = a
    while !iszero(r) && deg(r, i) >= db
        dr = deg(r, i)
        lr = lc(r, i)
        r = lb * r - lr * mpvar(a.nv, i, dr - db) * b
    end
    return r
end

# rational content (positive, or the sign of the leading coefficient) and the
# primitive integer polynomial
function qcontent(p::MP)
    iszero(p) && return Q(1)
    nums = BigInt[numerator(c) for c in values(p.t)]
    dens = BigInt[denominator(c) for c in values(p.t)]
    c = Q(gcd(nums), lcm(dens))
    p.t[leadexp(p)] < 0 && (c = -c)
    return c
end
mpnormalize(p::MP) = iszero(p) ? p : scale(p, inv(qcontent(p)))

# content in variable i: the gcd of the coefficients (polynomials in the others)
function content_in(p::MP, i::Int)
    cs = filter(!iszero, coeffs(p, i))
    g = mpnormalize(cs[1])
    for c in cs[2:end]
        isconst(g) && return g
        g = pgcd(g, c)
    end
    return g
end

function pgcd(a::MP, b::MP)
    iszero(a) && return mpnormalize(b)
    iszero(b) && return mpnormalize(a)
    va, vb = vars_in(a), vars_in(b)
    (isempty(va) || isempty(vb)) && return mpconst(a.nv, 1)
    v = maximum(union(va, vb))
    v in va || return pgcd(a, content_in(b, v))
    v in vb || return pgcd(content_in(a, v), b)
    ca, cb = content_in(a, v), content_in(b, v)
    pa, pb = divexact(a, ca), divexact(b, cb)
    g = pgcd(ca, cb)
    deg(pa, v) < deg(pb, v) && ((pa, pb) = (pb, pa))
    r0, r1 = pa, pb
    while true
        r = prem(r0, r1, v)
        iszero(r) && break
        if deg(r, v) == 0
            return mpnormalize(g)
        end
        r0, r1 = r1, divexact(r, content_in(r, v))
    end
    return mpnormalize(g * r1)
end

function evalvar(p::MP, i::Int, val::Q)
    r = Dict{Vector{Int},Q}()
    for (e, c) in p.t
        f = copy(e)
        f[i] = 0
        _addto!(r, f, c * val^e[i])
    end
    return MP(p.nv, r)
end

# square root of a polynomial, or nothing if it is not a perfect square
function mpsqrt(p::MP)
    iszero(p) && return p
    le = leadexp(p)
    all(iseven, le) || return nothing
    c = p.t[le]
    c > 0 || return nothing
    sn, sd = isqrt(numerator(c)), isqrt(denominator(c))
    (sn^2 == numerator(c) && sd^2 == denominator(c)) || return nothing
    l = div.(le, 2)
    lcoef = Q(sn, sd)
    s = MP(p.nv, Dict(l => lcoef))
    r = p - s * s
    iters = 0
    while !iszero(r)
        lr = leadexp(r)
        all(lr .>= l) || return nothing
        e = lr .- l
        e < l || return nothing
        t = MP(p.nv, Dict(e => r.t[lr] / (2 * lcoef)))
        s = s + t
        r = p - s * s
        iters += 1
        iters > nterms(p) + 4 && return nothing
    end
    return s
end

# substitute x_i -> x_i^(1/g) where every exponent of x_i is a multiple of g
function deflate(p::MP, i::Int, g::Int)
    r = Dict{Vector{Int},Q}()
    for (e, c) in p.t
        f = copy(e)
        f[i] = div(f[i], g)
        r[f] = c
    end
    return MP(p.nv, r)
end
inflate(p::MP, i::Int, g::Int) = MP(p.nv, Dict(begin
    f = copy(e)
    f[i] *= g
    f
end => c for (e, c) in p.t))
