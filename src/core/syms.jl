# Symbols, their assumptions, and the `@syms` / `@funs` macros.

_q(x::Real) = isinf(x) ? nothing : Q(x)
_q(::Nothing) = nothing
_q(x::Num) = x.val isa Q ? x.val : Q(x.val)

"""
    sym(name; real = true, positive, negative, nonnegative, nonpositive,
        integer, complex, lo, hi, lo_open = true, hi_open = true)

A symbol with assumptions. Symbols are **real by default** (pass `complex = true`
to opt out). `lo`/`hi` bound it (open by default): `sym(:p; lo = 0, hi = 1)` is
`p ∈ (0, 1)`.
"""
function sym(name::Symbol; real::Bool = true, complex::Bool = false,
    positive::Bool = false, negative::Bool = false, nonnegative::Bool = false,
    nonpositive::Bool = false, integer::Bool = false, natural::Bool = false,
    lo = nothing, hi = nothing, lo_open::Bool = true, hi_open::Bool = true)
    if complex
        return Sym(name, SymInfo(false, false, nothing, false, nothing, false))
    end
    l, lopen = _q(lo), lo_open
    h, hopen = _q(hi), hi_open
    natural && (integer = true; nonnegative = true)
    positive && ((l === nothing || l < 0 || (l == 0 && !lopen)) && (l = Q(0); lopen = true))
    nonnegative && ((l === nothing || l < 0) && (l = Q(0); lopen = false))
    negative && ((h === nothing || h > 0 || (h == 0 && !hopen)) && (h = Q(0); hopen = true))
    nonpositive && ((h === nothing || h > 0) && (h = Q(0); hopen = false))
    l === nothing && (lopen = false)
    h === nothing && (hopen = false)
    return Sym(name, SymInfo(true, integer, l, lopen, h, hopen))
end

const _FLAGS = Dict(:positive => :positive, :negative => :negative,
    :nonnegative => :nonnegative, :nonneg => :nonnegative,
    :nonpositive => :nonpositive, :nonpos => :nonpositive, :real => :real,
    :complex => :complex, :integer => :integer, :natural => :natural)

function _spec_kwargs(spec)
    if spec isa Symbol
        haskey(_FLAGS, spec) || error("@syms: unknown assumption `$spec`")
        f = _FLAGS[spec]
        return f === :real ? Any[] : Any[Expr(:kw, f, true)]
    elseif spec isa Expr && spec.head === :tuple && all(a -> a isa Symbol && haskey(_FLAGS, a), spec.args)
        return reduce(vcat, (_spec_kwargs(a) for a in spec.args); init = Any[])
    elseif spec isa Expr && spec.head === :tuple && length(spec.args) == 2
        return Any[Expr(:kw, :lo, esc(spec.args[1])), Expr(:kw, :hi, esc(spec.args[2]))]
    elseif spec isa Expr && spec.head === :vect && length(spec.args) == 2
        return Any[Expr(:kw, :lo, esc(spec.args[1])), Expr(:kw, :hi, esc(spec.args[2])),
            Expr(:kw, :lo_open, false), Expr(:kw, :hi_open, false)]
    end
    error("@syms: cannot read the assumption `$spec`")
end

"""
    @syms x y::positive p::(0, 1) q::[0, 1] n::integer z::complex

Create symbols and bind them to variables of the same names. Symbols are real
unless declared `complex`. Assumptions: `positive`, `negative`, `nonnegative`
(`nonneg`), `nonpositive` (`nonpos`), `integer`, `natural` (nonnegative
integer), `complex`, a tuple of these (`(positive, integer)`), an open interval
`(lo, hi)` or a closed one `[lo, hi]` (use `Inf` for an unbounded side).
Returns the symbols as a tuple.
"""
macro syms(xs...)
    out = Expr(:block)
    names = Any[]
    for x in xs
        if x isa Symbol
            name, kws = x, Any[]
        elseif x isa Expr && x.head === :(::)
            name, kws = x.args[1], _spec_kwargs(x.args[2])
        else
            error("@syms: cannot read `$x`")
        end
        call = Expr(:call, sym, Expr(:parameters, kws...), QuoteNode(name))
        push!(out.args, Expr(:(=), esc(name), call))
        push!(names, esc(name))
    end
    push!(out.args, Expr(:tuple, names...))
    return out
end

"""
    @funs n u

Create undefined functions (see [`UFun`](@ref)): `n(t)` is then a term that
[`diff`](@ref) and [`dsolve`](@ref) understand.
"""
macro funs(xs...)
    out = Expr(:block)
    for x in xs
        x isa Symbol || error("@funs: expected names")
        push!(out.args, Expr(:(=), esc(x), Expr(:call, UFun, QuoteNode(x))))
    end
    push!(out.args, Expr(:tuple, map(esc, xs)...))
    return out
end

# ---- facts beyond single-symbol bounds ----------------------------------------
#
# A fact says that some expression g has a known sign (`V < C` is the fact that
# C - V is positive). Facts are stored normalised (leading coefficient 1) so a
# query can match a positive or negative multiple of g.

const FACTS = Tuple{Term,UInt8}[]

"""
    assume!(conds...)

Add facts such as `V < C` or `a + b > 1` to the global assumptions, used by
[`simplify`](@ref), [`decide`](@ref) and the sign engine. See also
[`assuming`](@ref) and [`forget!`](@ref).
"""
function assume!(conds...)
    for c in conds
        _addfact!(c)
    end
    return nothing
end

"""
    forget!()

Clear all facts added with [`assume!`](@ref).
"""
forget!() = (empty!(FACTS); nothing)

"""
    assuming(f, conds...)

Run `f()` with the extra facts `conds` (see [`assume!`](@ref)), then remove them.

    assuming(V < C) do
        ess(hawk_dove)
    end
"""
function assuming(f::Function, conds...)
    n = length(FACTS)
    try
        assume!(conds...)
        return f()
    finally
        resize!(FACTS, n)
    end
end

const _OPMASK = Dict(:> => 0x04, :>= => 0x06, :< => 0x01, :<= => 0x03, :!= => 0x05, :(==) => 0x02)

function _addfact!(c)
    if c isa And
        foreach(_addfact!, c.args)
        return
    end
    c isa Bool && return
    c isa Rel || throw(ArgumentError("assume!: expected a relation such as `a < b`, got $c"))
    g = _add((c.lhs, _mul((MONE, c.rhs))))
    g isa Num && return
    k, gn = _normlead(g)
    m = _OPMASK[c.op]
    push!(FACTS, (gn, k > 0 ? m : _flipmask(m)))
    return
end
