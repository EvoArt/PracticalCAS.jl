# Differentiation.

"""
    diff(f, x)
    diff(f, x, n)
    diff(f, x, y, ...)

The derivative of `f` with respect to the symbol `x` (`n` times, or with respect
to each of `x, y, …` in turn). Undefined functions (`n(t)`, see [`@funs`](@ref))
differentiate to `D(n(t), t)`.
"""
Base.diff(f::Term, x::Sym) = _d(f, x)
function Base.diff(f::Term, x::Sym, n::Integer)
    for _ in 1:n
        f = _d(f, x)
    end
    return f
end
Base.diff(f::Term, x::Sym, y::Sym, zs::Sym...) = foldl(_d, (y, zs...); init = _d(f, x))
Base.diff(f::Number, ::Sym, args...) = ZERO

_depends(f::Term, x::Sym) = has(f, x)

function _d(f::Term, x::Sym)::Term
    _depends(f, x) || return ZERO
    f == x && return ONE
    if f isa Add
        return _add(Term[_mul((Num(k), _d(t, x))) for (t, k) in f.terms])
    elseif f isa Mul
        out = Term[]
        n = length(f.factors)
        for i in 1:n
            b, e = f.factors[i]
            di = _dpow(b, e, x)
            di == ZERO && continue
            others = Term[_powraw(f.factors[j]) for j in 1:n if j != i]
            push!(out, _mul(vcat(Term[Num(f.c), di], others)))
        end
        return _add(out)
    elseif f isa Pow
        return _dpow(f.base, f.exp, x)
    elseif f isa Fn
        return _dfn(f, x)
    elseif f isa Deriv
        any(a -> a == x, f.f isa Fn ? f.f.args : Term[]) || throw(ArgumentError("diff: cannot differentiate $f with respect to $x"))
        vars = copy(f.vars)
        i = findfirst(p -> p.first == x, vars)
        if i === nothing
            push!(vars, x => 1)
        else
            vars[i] = x => vars[i].second + 1
        end
        return Deriv(f.f, vars)
    end
    return ZERO
end

function _dpow(b::Term, e::Term, x::Sym)::Term
    e == ONE && return _d(b, x)
    db, de = _depends(b, x), _depends(e, x)
    if db && !de
        return _mul((e, _pow(b, _add((e, MONE))), _d(b, x)))
    elseif de && !db
        return _mul((_pow(b, e), _log(b), _d(e, x)))
    elseif db && de
        return _mul((_pow(b, e), _add((_mul((_d(e, x), _log(b))), _mul((e, _d(b, x), _pow(b, MONE)))))))
    end
    return ZERO
end

function _dfn(f::Fn, x::Sym)::Term
    h = f.head
    if !isknownfn(h)
        all(a -> a isa Sym || !_depends(a, x), f.args) ||
            throw(ArgumentError("diff: the chain rule through the undefined function $h is not supported; differentiate $h with plain symbol arguments"))
        any(a -> a == x, f.args) || return ZERO
        return Deriv(f, [x => 1])
    end
    u = f.args[1]
    du = _d(u, x)
    du == ZERO && return ZERO
    outer = if h === :exp
        f
    elseif h === :log
        _pow(u, MONE)
    elseif h === :sin
        _cos(u)
    elseif h === :cos
        _mul((MONE, _sin(u)))
    elseif h === :tan
        _add((ONE, _pow(_tan(u), TWO)))
    elseif h === :asin
        _pow(_add((ONE, _mul((MONE, _pow(u, TWO))))), Num(Q(-1) // 2))
    elseif h === :acos
        _mul((MONE, _pow(_add((ONE, _mul((MONE, _pow(u, TWO))))), Num(Q(-1) // 2))))
    elseif h === :atan
        _pow(_add((ONE, _pow(u, TWO))), MONE)
    elseif h === :sinh
        _fncall(:cosh, Term[u])
    elseif h === :cosh
        _fncall(:sinh, Term[u])
    elseif h === :tanh
        _add((ONE, _mul((MONE, _pow(_fncall(:tanh, Term[u]), TWO)))))
    elseif h === :abs
        _sign(u)
    elseif h === :sign
        return ZERO
    else
        throw(ArgumentError("diff: no derivative known for $h"))
    end
    return _mul((outer, du))
end

"""
    D(f, x, n = 1)

The derivative term: for an undefined-function application `n(t)` the
unevaluated `D(n(t), t)`, otherwise the same as `diff(f, x, n)`.
"""
D(f::Term, x::Sym, n::Integer = 1) = diff(f, x, n)

"""
    gradient(f, xs)

The vector of partial derivatives of `f` with respect to the symbols `xs`.
"""
gradient(f, xs::AbstractVector) = Term[diff(toterm(f), x) for x in xs]

"""
    jacobian(F, xs)

The matrix `∂Fᵢ/∂xⱼ`.
"""
jacobian(F::AbstractVector, xs::AbstractVector) = Term[diff(toterm(f), x) for f in F, x in xs]

"""
    hessian(f, xs)

The matrix of second partial derivatives of `f`.
"""
hessian(f, xs::AbstractVector) = Term[diff(diff(toterm(f), x), y) for x in xs, y in xs]
