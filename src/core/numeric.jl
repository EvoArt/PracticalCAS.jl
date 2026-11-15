# Numeric evaluation and compilation to Julia functions.

"""
    evalf(x, old => value, ...)

Evaluate `x` numerically (as `Float64`, or `ComplexF64` when the value is not
real) after substituting the given values. Every symbol must get a value.
Works elementwise on arrays.
"""
evalf(x::Term, ps::Pair...) = _clean(_ev(isempty(ps) ? x : subs(x, ps...)))
evalf(x::Number, ps::Pair...) = x
evalf(x::AbstractArray, ps::Pair...) = map(y -> evalf(y, ps...), x)
evalf(x::Eqn, ps::Pair...) = evalf(x.lhs, ps...) ~ evalf(x.rhs, ps...)

_clean(z::Complex) = abs(imag(z)) <= 1e-14 * max(1.0, abs(real(z))) ? real(z) : z
_clean(z) = z

_ev(x::Num) = Float64(x.val)
function _ev(x::Const)
    x.name === :π && return Float64(π)
    x.name === :I && return im * 1.0
    x.name === :∞ && return Inf
    error("N: unknown constant $(x.name)")
end
_ev(x::Sym) = throw(ArgumentError("N: no value for the symbol $(x.name)"))
_ev(x::Add) = Float64(x.c) + sum(Float64(k) * _ev(t) for (t, k) in x.terms)
_ev(x::Mul) = Float64(x.c) * prod(_cpow(_ev(b), _ev(e)) for (b, e) in x.factors)
_ev(x::Pow) = _cpow(_ev(x.base), _ev(x.exp))
_cpow(b::Real, e::Real) = (b < 0 && !isinteger(e)) ? Complex(b)^e : (isinteger(e) ? b^Int(e) : b^e)
_cpow(b, e) = b^e
_cl(v::Real, f, g) = f(v)
function _ev(x::Fn)
    h = x.head
    if h === :RootOf
        p, v, k = x.args
        cs = polycoeffs(p, v)
        cs === nothing && error("N: RootOf needs a polynomial")
        r = _numroots([_ev(c) for c in cs])
        return r[Int(_ev(k))]
    end
    h === :Integral && error("N: cannot evaluate an unevaluated integral")
    h in (:Sum, :Product) && return _evsum(x)
    a = [_ev(y) for y in x.args]
    h === :binomial && return _nbinomial(a[1], a[2])
    v = a[1]
    h === :factorial && return _nfactorial(v)
    h === :gamma && return _ngamma(v)
    h === :exp && return exp(v)
    h === :log && return (v isa Real && v < 0) ? log(Complex(v)) : log(v)
    h === :sin && return sin(v)
    h === :cos && return cos(v)
    h === :tan && return tan(v)
    h === :asin && return (v isa Real && abs(v) > 1) ? asin(Complex(v)) : asin(v)
    h === :acos && return (v isa Real && abs(v) > 1) ? acos(Complex(v)) : acos(v)
    h === :atan && return atan(v)
    h === :sinh && return sinh(v)
    h === :cosh && return cosh(v)
    h === :tanh && return tanh(v)
    h === :erf && return _nerf(v)
    h === :erfi && return _nerfi(v)
    h === :Ei && return _nEi(v)
    h === :Si && return _nSi(v)
    h === :Ci && return _nCi(v)
    h === :abs && return abs(v)
    h === :sign && return sign(v)
    h === :conj && return conj(v)
    h === :re && return real(v)
    h === :im && return imag(v)
    throw(ArgumentError("N: cannot evaluate the undefined function $h"))
end
_ev(x::Deriv) = throw(ArgumentError("N: cannot evaluate the derivative $x"))

# an unevaluated sum or product with numeric bounds, term by term; an infinite
# sum stops once the terms are negligible
function _evsum(x::Fn)
    f, k, a, b = x.args
    lo, hi = _ev(a), _ev(b)
    (isfinite(lo) && isinteger(lo)) || throw(ArgumentError("N: the lower bound of $x is not an integer"))
    issum = x.head === :Sum
    acc = issum ? 0.0 : 1.0
    i = Int(lo)
    small = 0
    while hi == Inf || i <= hi
        v = _ev(subs(f, k => i))
        acc = issum ? acc + v : acc * v
        if hi == Inf
            small = abs(v) <= 1e-17 * max(abs(acc), 1e-300) ? small + 1 : 0
            (small >= 10 || i - lo > 1_000_000) && break
        end
        i += 1
    end
    return acc
end

# roots of the polynomial with coefficients cs (constant first), via the
# companion matrix, sorted by real part then imaginary part
function _numroots(cs::Vector)
    while length(cs) > 1 && iszero(cs[end])
        pop!(cs)
    end
    n = length(cs) - 1
    n < 1 && return ComplexF64[]
    C = zeros(ComplexF64, n, n)
    for i in 1:n-1
        C[i+1, i] = 1
    end
    for i in 1:n
        C[i, n] = -cs[i] / cs[end]
    end
    r = LinearAlgebra.eigvals(C)
    return sort!(map(_clean, r); by = z -> (real(z), imag(z)))
end

# ---- compilation -------------------------------------------------------------------

_jl(x::Num, env) = x.val isa Q ? (isone(denominator(x.val)) ? Int(numerator(x.val)) : Float64(x.val)) : x.val
function _jl(x::Const, env)
    x.name === :π && return :(π)
    x.name === :I && return :(im)
    return :(Inf)
end
_jl(x::Sym, env) = haskey(env, x) ? env[x] : throw(ArgumentError("lambdify: $(x.name) is not an argument"))
_jl(x::Add, env) = Expr(:call, :+, _jl(Num(x.c), env), (:($(_jl(Num(k), env)) * $(_jl(t, env))) for (t, k) in x.terms)...)
_jl(x::Mul, env) = Expr(:call, :*, _jl(Num(x.c), env), (_jlpow(b, e, env) for (b, e) in x.factors)...)
_jl(x::Pow, env) = _jlpow(x.base, x.exp, env)
function _jlpow(b, e, env)
    e == ONE && return _jl(b, env)
    e == HALF && return :(sqrt($(_jl(b, env))))
    return :($(_jl(b, env))^$(_jl(e, env)))
end
function _jl(x::Fn, env)
    isknownfn(x.head) && x.head ∉ (:RootOf, :Integral, :re, :im) ||
        throw(ArgumentError("lambdify: cannot compile $(x.head)"))
    h = x.head in SPECIAL_FUNCTIONS || x.head in (:factorial, :gamma, :binomial) ? Symbol("_n", x.head) : x.head
    x.head in (:Sum, :Product) && throw(ArgumentError("lambdify: cannot compile the unevaluated $(x.head)"))
    return Expr(:call, h, (_jl(a, env) for a in x.args)...)
end
_jl(x::Deriv, env) = throw(ArgumentError("lambdify: cannot compile the derivative $x"))

"""
    lambdify(x, vars) -> Function

A compiled Julia function of the symbols `vars` that computes `x` (a term or an
array of terms). `lambdify(r*n*(1 - n/K), [n, r, K])(10.0, 1.0, 100.0)`.
"""
function lambdify(x, vars::AbstractVector)
    args = [Symbol("_x", i) for i in eachindex(vars)]
    env = Dict{Sym,Any}(v => a for (v, a) in zip(vars, args))
    body = x isa AbstractArray ? Expr(:vect, (_jl(toterm(y), env) for y in x)...) : _jl(toterm(x), env)
    if x isa AbstractMatrix
        body = :(reshape($body, $(size(x))))
    end
    f = Core.eval(@__MODULE__, Expr(:->, Expr(:tuple, args...), body))
    return (xs...) -> Base.invokelatest(f, xs...)
end
