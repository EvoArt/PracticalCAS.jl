# Between terms and polynomials / rational functions.
#
# A term is viewed as a rational function in "generators": symbols, constants,
# function applications and non-integer powers (sqrt(x) is a generator, raised to
# an integer power). Generators are collected first so every polynomial in one
# computation shares the same variables.

struct Gens
    list::Vector{Term}
    idx::Dict{Term,Int}
end
Gens() = Gens(Term[], Dict{Term,Int}())
function _gen!(g::Gens, x::Term)
    haskey(g.idx, x) && return g.idx[x]
    push!(g.list, x)
    g.idx[x] = length(g.list)
end
nvars(g::Gens) = length(g.list)

# a power b^e as (generator-ish base, integer exponent) when it can be
_genpow(b::Term, e::Term) = begin
    if isint(e)
        return (b, Int(numerator(e.val)))
    elseif e isa Num && e.val isa Q
        p, q = numerator(e.val), denominator(e.val)
        return (Pow(b, Num(Q(1) // q)), Int(p))
    elseif e isa Add && !iszero(e.c) && e.c isa Q && _isint(e.c)
        return nothing   # split by _rf into b^c * b^(rest)
    end
    return (Pow(b, e), 1)
end

function _collect_gens!(g::Gens, x::Term)
    if x isa Num
        return g
    elseif x isa Add
        foreach(p -> _collect_gens!(g, p.first), x.terms)
    elseif x isa Mul
        foreach(p -> _collect_gens_pow!(g, p.first, p.second), x.factors)
    elseif x isa Pow
        _collect_gens_pow!(g, x.base, x.exp)
    else
        _gen!(g, x)
    end
    return g
end
function _collect_gens_pow!(g::Gens, b::Term, e::Term)
    if e == ONE
        _collect_gens!(g, b)
    elseif isint(e)
        _collect_gens!(g, b)
    elseif e isa Add && e.c isa Q && !iszero(e.c) && _isint(e.c)
        _collect_gens!(g, b)
        rest = _add(Term[_scale(t, k) for (t, k) in e.terms])
        _gen!(g, Pow(b, rest))
    else
        bb, _ = _genpow(b, e)
        _gen!(g, bb)
    end
    return g
end

# term -> (numerator, denominator) polynomials in the generators
function _rf(x::Term, g::Gens)::Tuple{MP,MP}
    nv = nvars(g)
    if x isa Num
        v = x.val isa Q ? x.val : Q(x.val)
        return (mpconst(nv, v), mpconst(nv, 1))
    elseif x isa Add
        n, d = mpconst(nv, x.c isa Q ? x.c : Q(x.c)), mpconst(nv, 1)
        for (t, k) in x.terms
            tn, td = _rf(t, g)
            tn = scale(tn, k isa Q ? k : Q(k))
            if td == d
                n = n + tn
            else
                gg = pgcd(d, td)
                a, b = divexact(td, gg), divexact(d, gg)
                n = n * a + tn * b
                d = d * a
            end
        end
        return (n, d)
    elseif x isa Mul
        n, d = mpconst(nv, x.c isa Q ? x.c : Q(x.c)), mpconst(nv, 1)
        for (b, e) in x.factors
            fn, fd = _rfpow(b, e, g)
            n, d = n * fn, d * fd
        end
        return (n, d)
    elseif x isa Pow
        return _rfpow(x.base, x.exp, g)
    end
    return (mpvar(nv, g.idx[x]), mpconst(nv, 1))
end

function _rfpow(b::Term, e::Term, g::Gens)
    nv = nvars(g)
    e == ONE && return _rf(b, g)
    if isint(e)
        n, d = _rf(b, g)
        k = Int(numerator(e.val))
        return k >= 0 ? (n^k, d^k) : (d^(-k), n^(-k))
    elseif e isa Add && e.c isa Q && !iszero(e.c) && _isint(e.c)
        n, d = _rfpow(b, Num(e.c), g)
        rest = _add(Term[_scale(t, k) for (t, k) in e.terms])
        return (n * mpvar(nv, g.idx[Pow(b, rest)]), d)
    end
    bb, k = _genpow(b, e)
    i = g.idx[bb]
    return k >= 0 ? (mpvar(nv, i, k), mpconst(nv, 1)) : (mpconst(nv, 1), mpvar(nv, i, -k))
end

function _mp2term(p::MP, g::Gens; float::Bool = false)::Term
    iszero(p) && return ZERO
    ts = Term[]
    for (e, c) in p.t
        fs = Term[Num(float ? Float64(c) : c)]
        for (i, k) in enumerate(e)
            k == 0 && continue
            push!(fs, _pow(g.list[i], Num(k)))
        end
        push!(ts, _mul(fs))
    end
    return _add(ts)
end

_hasfloat(x::Num) = x.val isa Float64
_hasfloat(x::Add) = x.c isa Float64 || any(p -> p.second isa Float64 || _hasfloat(p.first), x.terms)
_hasfloat(x::Mul) = x.c isa Float64 || any(p -> _hasfloat(p.first) || _hasfloat(p.second), x.factors)
_hasfloat(x::Pow) = _hasfloat(x.base) || _hasfloat(x.exp)
_hasfloat(x::Fn) = any(_hasfloat, x.args)
_hasfloat(::Term) = false

# apply f inside the generators (function arguments, non-integer power bases and
# symbolic exponents), so that equal generators are recognised
function _inner(f, x::Term)::Term
    if x isa Union{Num,Const,Sym}
        return x
    elseif x isa Add || x isa Mul
        return _map(y -> _inner(f, y), x)
    elseif x isa Pow
        isint(x.exp) && return _pow(_inner(f, x.base), x.exp)
        return _pow(f(x.base), f(x.exp))
    elseif x isa Fn
        return _fncall(x.head, Term[f(a) for a in x.args])
    end
    return x
end

"""
    ratfun(x) -> (n, d, gens, float)

`x` as a quotient of coprime polynomials in its generators.
"""
function ratfun(x::Term; inner = cancel)
    y = _inner(inner, x)
    g = _collect_gens!(Gens(), y)
    n, d = _rf(y, g)
    gg = pgcd(n, d)
    if !isconst(gg)
        n, d = divexact(n, gg), divexact(d, gg)
    end
    c = qcontent(d)
    n, d = scale(n, inv(c)), scale(d, inv(c))
    return (n, d, g, _hasfloat(x))
end
