# Term types.
#
# Every expression is a `Term`, in a canonical form maintained by the smart
# constructors in arith.jl: sums are a constant plus `term => coefficient` pairs,
# products are a coefficient plus `base => exponent` pairs, both sorted by the
# total order `_cmp`, so structurally equal means equal. Hashes are computed once,
# at construction. The raw constructors below do no simplification; code outside
# core/ should build terms with `+`, `*`, `^` and the function constructors.

const Q = Rational{BigInt}
const NumVal = Union{Q,Float64}

"""
    Term <: Number

Supertype of symbolic expressions: numbers ([`Num`](@ref)), constants (`π`, `im`,
`∞`), symbols ([`Sym`](@ref)), sums, products, powers, function applications and
derivatives. Terms are immutable and compare structurally after canonicalisation.
"""
abstract type Term <: Number end

const SALT = 0x9e3779b97f4a7c15

"""
    Num(x)

An exact rational (`Rational{BigInt}`) or a `Float64`, as a term.
"""
struct Num <: Term
    val::NumVal
    h::UInt
    Num(v::Q) = new(v, hash(v, SALT))
    Num(v::Float64) = new(v, hash(v, SALT))
end
Num(x::Integer) = Num(Q(x))
Num(x::Rational) = Num(Q(x))
Num(x::AbstractFloat) = Num(Float64(x))
Num(x::Num) = x

"""
    Const(name)

A named constant: `:π`, `:I` (the imaginary unit, printed `im`) or `:∞`.
"""
struct Const <: Term
    name::Symbol
    h::UInt
    Const(n::Symbol) = new(n, hash(n, SALT + 1))
end

"""
    SymInfo

What is assumed about a symbol: whether it is real, whether it is an integer, and
optional bounds `lo`/`hi` (each open or closed). Unbounded sides are `nothing`.
"""
struct SymInfo
    real::Bool
    integer::Bool
    lo::Union{Nothing,Q}
    lo_open::Bool
    hi::Union{Nothing,Q}
    hi_open::Bool
end
Base.:(==)(a::SymInfo, b::SymInfo) =
    a.real == b.real && a.integer == b.integer && a.lo == b.lo &&
    a.lo_open == b.lo_open && a.hi == b.hi && a.hi_open == b.hi_open
Base.hash(a::SymInfo, h::UInt) =
    hash((a.real, a.integer, a.lo, a.lo_open, a.hi, a.hi_open), h)

"""
    Sym

A symbol, with the assumptions in its [`SymInfo`](@ref). Two symbols with the same
name but different assumptions are different symbols. Create with [`@syms`](@ref)
or [`sym`](@ref).
"""
struct Sym <: Term
    name::Symbol
    info::SymInfo
    h::UInt
    Sym(n::Symbol, i::SymInfo) = new(n, i, hash((n, i), SALT + 2))
end

struct Add <: Term
    c::NumVal
    terms::Vector{Pair{Term,NumVal}}
    h::UInt
    function Add(c::NumVal, terms::Vector{Pair{Term,NumVal}})
        h = hash(c, SALT + 3)
        for (t, k) in terms
            h = hash(k, hash(t, h))
        end
        new(c, terms, h)
    end
end

struct Mul <: Term
    c::NumVal
    factors::Vector{Pair{Term,Term}}
    h::UInt
    function Mul(c::NumVal, factors::Vector{Pair{Term,Term}})
        h = hash(c, SALT + 4)
        for (b, e) in factors
            h = hash(e, hash(b, h))
        end
        new(c, factors, h)
    end
end

struct Pow <: Term
    base::Term
    exp::Term
    h::UInt
    Pow(b::Term, e::Term) = new(b, e, hash(e, hash(b, SALT + 5)))
end

"""
    Fn

A function applied to arguments: a known function (`exp`, `log`, `sin`, …) or an
undefined one made with [`@funs`](@ref) (`n(t)`).
"""
struct Fn <: Term
    head::Symbol
    args::Vector{Term}
    h::UInt
    function Fn(head::Symbol, args::Vector{Term})
        h = hash(head, SALT + 6)
        for a in args
            h = hash(a, h)
        end
        new(head, args, h)
    end
end

"""
    Deriv

The derivative of an undefined function application, `D(n(t), t)`.
"""
struct Deriv <: Term
    f::Term
    vars::Vector{Pair{Sym,Int}}
    h::UInt
    function Deriv(f::Term, vars::Vector{Pair{Sym,Int}})
        h = hash(f, SALT + 7)
        for (v, k) in vars
            h = hash(k, hash(v, h))
        end
        new(f, vars, h)
    end
end

# ---- equality and hashing ---------------------------------------------------

Base.hash(x::Term, h::UInt) = hash(x.h, h)
Base.:(==)(a::Term, b::Term) = a.h == b.h && _eq(a, b)
Base.isequal(a::Term, b::Term) = a == b
Base.isequal(::Term, ::Number) = false
Base.isequal(::Number, ::Term) = false

_eq(::Term, ::Term) = false
_eq(a::Num, b::Num) = a.val == b.val
_eq(a::Const, b::Const) = a.name === b.name
_eq(a::Sym, b::Sym) = a.name === b.name && a.info == b.info
_eq(a::Add, b::Add) = a.c == b.c && a.terms == b.terms
_eq(a::Mul, b::Mul) = a.c == b.c && a.factors == b.factors
_eq(a::Pow, b::Pow) = a.base == b.base && a.exp == b.exp
_eq(a::Fn, b::Fn) = a.head === b.head && a.args == b.args
_eq(a::Deriv, b::Deriv) = a.f == b.f && a.vars == b.vars

# ---- canonical total order ----------------------------------------------------

_rank(::Num) = 0
_rank(::Const) = 1
_rank(::Sym) = 2
_rank(::Pow) = 3
_rank(::Mul) = 4
_rank(::Add) = 5
_rank(::Fn) = 6
_rank(::Deriv) = 7

function _cmp(a::Term, b::Term)::Int
    a === b && return 0
    ra, rb = _rank(a), _rank(b)
    ra != rb && return ra < rb ? -1 : 1
    return _cmpsame(a, b)
end

_cmpnum(a, b) = a < b ? -1 : (b < a ? 1 : 0)
_cmpsame(a::Num, b::Num) = _cmpnum(a.val, b.val)
_cmpsame(a::Const, b::Const) = cmp(String(a.name), String(b.name))
function _cmpsame(a::Sym, b::Sym)
    c = cmp(String(a.name), String(b.name))
    c != 0 && return c
    a.info == b.info && return 0
    return _cmpnum(hash(a.info), hash(b.info))
end
function _cmpsame(a::Pow, b::Pow)
    c = _cmp(a.base, b.base)
    c != 0 ? c : _cmp(a.exp, b.exp)
end
function _cmpvec(xs, ys, f)
    for (x, y) in zip(xs, ys)
        c = f(x, y)
        c != 0 && return c
    end
    return _cmpnum(length(xs), length(ys))
end
_cmppair(p, q) = (c = _cmp(p.first, q.first); c != 0 ? c : _cmp(p.second, q.second))
_cmppairn(p, q) = (c = _cmp(p.first, q.first); c != 0 ? c : _cmpnum(p.second, q.second))
function _cmpsame(a::Mul, b::Mul)
    c = _cmpvec(a.factors, b.factors, _cmppair)
    c != 0 ? c : _cmpnum(a.c, b.c)
end
function _cmpsame(a::Add, b::Add)
    c = _cmpvec(a.terms, b.terms, _cmppairn)
    c != 0 ? c : _cmpnum(a.c, b.c)
end
function _cmpsame(a::Fn, b::Fn)
    c = cmp(String(a.head), String(b.head))
    c != 0 ? c : _cmpvec(a.args, b.args, _cmp)
end
function _cmpsame(a::Deriv, b::Deriv)
    c = _cmp(a.f, b.f)
    c != 0 && return c
    return _cmpvec(a.vars, b.vars, (p, q) -> (d = _cmp(p.first, q.first); d != 0 ? d : _cmpnum(p.second, q.second)))
end

_lt(a::Term, b::Term) = _cmp(a, b) < 0

# ---- constants ----------------------------------------------------------------

const ZERO = Num(Q(0))
const ONE = Num(Q(1))
const MONE = Num(Q(-1))
const TWO = Num(Q(2))
const HALF = Num(Q(1) // 2)
const IM = Const(:I)
const PI = Const(:π)
const INF = Const(:∞)

_tzeros(n::Integer) = Term[ZERO for _ in 1:n]
