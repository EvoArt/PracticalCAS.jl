# Equations (`lhs ~ rhs`) and conditions (`a < b`, `&`, `|`).

"""
    Eqn(lhs, rhs)

The equation `lhs = rhs`, written `lhs ~ rhs`.
"""
struct Eqn
    lhs::Term
    rhs::Term
end
Base.:~(a::Term, b::Term) = Eqn(a, b)
Base.:~(a::Term, b::Number) = Eqn(a, toterm(b))
Base.:~(a::Number, b::Term) = Eqn(toterm(a), b)
Base.:(==)(a::Eqn, b::Eqn) = a.lhs == b.lhs && a.rhs == b.rhs
Base.hash(a::Eqn, h::UInt) = hash(a.rhs, hash(a.lhs, h))
lhs(e::Eqn) = e.lhs
rhs(e::Eqn) = e.rhs
subs(e::Eqn, args...) = Eqn(subs(e.lhs, args...), subs(e.rhs, args...))

"""
    Cond

A relation between terms ([`Rel`](@ref)) or a combination of conditions with `&`
(`And`), `|` (`Or`) and `!`. Comparing terms with `<`, `<=`, `>`, `>=` builds a
`Rel`; [`decide`](@ref) and [`simplify`](@ref) evaluate it under the
assumptions.
"""
abstract type Cond end

struct Rel <: Cond
    op::Symbol
    lhs::Term
    rhs::Term
end
struct And <: Cond
    args::Vector{Cond}
end
struct Or <: Cond
    args::Vector{Cond}
end

Base.:(==)(a::Rel, b::Rel) = a.op === b.op && a.lhs == b.lhs && a.rhs == b.rhs
Base.hash(a::Rel, h::UInt) = hash(a.op, hash(a.rhs, hash(a.lhs, h)))
Base.:(==)(a::And, b::And) = Set(a.args) == Set(b.args)
Base.:(==)(a::Or, b::Or) = Set(a.args) == Set(b.args)
Base.hash(a::And, h::UInt) = hash(Set(a.args), hash(:and, h))
Base.hash(a::Or, h::UInt) = hash(Set(a.args), hash(:or, h))

const CondLike = Union{Bool,Cond}

function _rel(op::Symbol, a::Term, b::Term)
    if a isa Num && b isa Num
        return op === :< ? a.val < b.val : op === :<= ? a.val <= b.val :
               op === :> ? a.val > b.val : op === :>= ? a.val >= b.val :
               op === :(==) ? a.val == b.val : a.val != b.val
    end
    return Rel(op, a, b)
end
for (op, f) in ((:<, :<), (:<=, :<=), (:>, :>), (:>=, :>=))
    @eval Base.$f(a::Term, b::Term) = _rel($(QuoteNode(op)), a, b)
    @eval Base.$f(a::Term, b::Number) = _rel($(QuoteNode(op)), a, toterm(b))
    @eval Base.$f(a::Number, b::Term) = _rel($(QuoteNode(op)), toterm(a), b)
end

"""
    eq(a, b)
    neq(a, b)

The conditions `a == b` and `a ≠ b` (Julia's `==` on terms is structural
equality and returns a `Bool`).
"""
eq(a, b) = _rel(:(==), toterm(a), toterm(b))
neq(a, b) = _rel(:!=, toterm(a), toterm(b))

const _NEGOP = Dict(:< => :>=, :<= => :>, :> => :<=, :>= => :<, :(==) => :!=, :!= => :(==))
const _FLIPOP = Dict(:< => :>, :<= => :>=, :> => :<, :>= => :<=, :(==) => :(==), :!= => :!=)

Base.:!(a::Rel) = Rel(_NEGOP[a.op], a.lhs, a.rhs)
Base.:!(a::And) = _or(Cond[!c for c in a.args])
Base.:!(a::Or) = _and(Cond[!c for c in a.args])

function _and(xs)
    out = Cond[]
    for x in xs
        x === true && continue
        x === false && return false
        if x isa And
            append!(out, x.args)
        else
            push!(out, x)
        end
    end
    unique!(out)
    isempty(out) && return true
    length(out) == 1 && return out[1]
    return And(out)
end
function _or(xs)
    out = Cond[]
    for x in xs
        x === false && continue
        x === true && return true
        if x isa Or
            append!(out, x.args)
        else
            push!(out, x)
        end
    end
    unique!(out)
    isempty(out) && return false
    length(out) == 1 && return out[1]
    return Or(out)
end

Base.:&(a::Cond, b::CondLike) = _and((a, b))
Base.:&(a::Bool, b::Cond) = _and((a, b))
Base.:|(a::Cond, b::CondLike) = _or((a, b))
Base.:|(a::Bool, b::Cond) = _or((a, b))

subs(c::Rel, args...) = _rel(c.op, subs(c.lhs, args...), subs(c.rhs, args...))
subs(c::And, args...) = _and([subs(a, args...) for a in c.args])
subs(c::Or, args...) = _or([subs(a, args...) for a in c.args])
