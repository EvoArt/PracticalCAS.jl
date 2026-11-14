# Walking terms: rebuilding with new children, substitution, free symbols.

"""
    _map(f, x)

Apply `f` to the immediate children of `x` and rebuild through the smart
constructors (so the result is canonical).
"""
_map(f, x::Union{Num,Const,Sym}) = x
_map(f, x::Add) = _add(Term[Num(x.c); [_mul((Num(k), f(t))) for (t, k) in x.terms]])
_map(f, x::Mul) = _mul(Term[Num(x.c); [_pow(f(b), f(e)) for (b, e) in x.factors]])
_map(f, x::Pow) = _pow(f(x.base), f(x.exp))
_map(f, x::Fn) = _fncall(x.head, Term[f(a) for a in x.args])
function _map(f, x::Deriv)
    g = f(x.f)
    g == x.f && return x
    r = g
    for (v, k) in x.vars
        r = diff(r, v, k)
    end
    return r
end

"""
    subs(x, old => new, ...)
    subs(x, d::AbstractDict)

Replace subterms (usually symbols, or undefined-function applications such as
`n(t)`) and re-simplify. Works elementwise on arrays, equations and conditions.
"""
subs(x::Term, ps::Pair...) = subs(x, Dict{Term,Term}(toterm(p.first) => toterm(p.second) for p in ps))
subs(x::Term, d::AbstractDict) = _subs(x, d isa Dict{Term,Term} ? d : Dict{Term,Term}(toterm(k) => toterm(v) for (k, v) in d))
subs(x::Number, args...) = x
subs(x::AbstractArray, args...) = map(y -> subs(y, args...), x)
function _subs(x::Term, d::Dict{Term,Term})::Term
    haskey(d, x) && return d[x]
    x isa Union{Num,Const,Sym} && return x
    return _map(y -> _subs(y, d), x)
end

"""
    free_symbols(x) -> Vector{Sym}

The symbols in `x`, sorted by name.
"""
function free_symbols(x)
    s = Set{Sym}()
    _syms!(s, x)
    return sort!(collect(s); by = v -> String(v.name))
end
_syms!(s, x::Sym) = push!(s, x)
_syms!(s, ::Union{Num,Const}) = s
_syms!(s, x::Add) = (foreach(p -> _syms!(s, p.first), x.terms); s)
_syms!(s, x::Mul) = (foreach(p -> (_syms!(s, p.first); _syms!(s, p.second)), x.factors); s)
_syms!(s, x::Pow) = (_syms!(s, x.base); _syms!(s, x.exp); s)
_syms!(s, x::Fn) = (foreach(a -> _syms!(s, a), x.args); s)
_syms!(s, x::Deriv) = (_syms!(s, x.f); foreach(p -> push!(s, p.first), x.vars); s)
_syms!(s, x::AbstractArray) = (foreach(y -> _syms!(s, y), x); s)
_syms!(s, ::Number) = s

"""
    has(x, y) -> Bool

Whether the term `y` occurs in `x` (as a subterm, or as a symbol anywhere).
"""
function has(x::Term, y::Term)::Bool
    x == y && return true
    x isa Union{Num,Const,Sym} && return false
    x isa Add && return any(p -> has(p.first, y), x.terms)
    x isa Mul && return any(p -> has(p.first, y) || has(p.second, y), x.factors)
    x isa Pow && return has(x.base, y) || has(x.exp, y)
    x isa Fn && return any(a -> has(a, y), x.args)
    x isa Deriv && return has(x.f, y) || any(p -> p.first == y, x.vars)
    return false
end
has(::Number, ::Term) = false
has(x::AbstractArray, y::Term) = any(z -> has(z, y), x)

# subterms satisfying a predicate, collected once each
function _collect_sub!(out::Vector{Term}, pred, x::Term)
    pred(x) && !(x in out) && push!(out, x)
    x isa Add && foreach(p -> _collect_sub!(out, pred, p.first), x.terms)
    x isa Mul && foreach(p -> (_collect_sub!(out, pred, p.first); _collect_sub!(out, pred, p.second)), x.factors)
    x isa Pow && (_collect_sub!(out, pred, x.base); _collect_sub!(out, pred, x.exp))
    x isa Fn && foreach(a -> _collect_sub!(out, pred, a), x.args)
    x isa Deriv && _collect_sub!(out, pred, x.f)
    return out
end

"""
    complexity(x) -> Int

A size measure (roughly the number of nodes), used to choose the simplest of
several equivalent forms.
"""
complexity(x::Num) = x.val isa Q ? (isone(denominator(x.val)) ? 1 : 2) + (x.val < 0 ? 1 : 0) : 1
complexity(::Union{Const,Sym}) = 1
complexity(x::Add) = (iszero(x.c) ? 0 : complexity(Num(x.c))) + sum(complexity(t) + (isone(abs(k)) ? 0 : 1) + 1 for (t, k) in x.terms)
complexity(x::Mul) = (isone(abs(x.c)) ? 0 : complexity(Num(x.c))) + sum(complexity(b) + (e == ONE ? 0 : complexity(e)) + 1 for (b, e) in x.factors)
complexity(x::Pow) = complexity(x.base) + complexity(x.exp) + 1
complexity(x::Fn) = 2 + sum(complexity, x.args; init = 0)
complexity(x::Deriv) = 2 + complexity(x.f)
complexity(x::Number) = 1
