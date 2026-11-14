# Elementary functions and undefined functions.
#
# Each known function has a smart constructor that evaluates the cases that are
# always valid (exp(0) = 1, exp(log x) = x, log(exp x) = x for real x, sin(kπ) = 0,
# odd/even symmetry) and floats numerically; otherwise it returns an `Fn`.

const KNOWN_FUNCTIONS = (:exp, :log, :sin, :cos, :tan, :asin, :acos, :atan,
    :sinh, :cosh, :tanh, :abs, :sign, :conj, :re, :im, :RootOf, :Integral)

isknownfn(h::Symbol) = h in KNOWN_FUNCTIONS

_isfloat(x::Term) = x isa Num && x.val isa Float64
_fl(x::Num) = Float64(x.val)

# a number times π, if x is one
function _pi_multiple(x::Term)
    x == PI && return Q(1)
    if x isa Mul && length(x.factors) == 1 && x.factors[1] == (PI => ONE) && x.c isa Q
        return x.c
    end
    return nothing
end

# whether a term "looks negative": a negative number, or a product with a
# negative coefficient (used for odd/even symmetries)
_looks_negative(x::Num) = x.val < 0
_looks_negative(x::Mul) = x.c < 0
_looks_negative(x::Add) = (isempty(x.terms) ? x.c < 0 : x.terms[1].second < 0)
_looks_negative(::Term) = false

function _exp(x::Term)::Term
    x == ZERO && return ONE
    _isfloat(x) && return Num(exp(_fl(x)))
    x isa Fn && x.head === :log && return x.args[1]
    if x isa Mul
        for (i, (b, e)) in enumerate(x.factors)
            if b isa Fn && b.head === :log && e == ONE
                rest = _mul((Num(x.c), _from_factors_except(x.factors, i)))
                return _pow(b.args[1], rest)
            end
        end
    end
    if x isa Add
        logs = Term[]
        rest = Term[Num(x.c)]
        for (t, k) in x.terms
            if t isa Fn && t.head === :log && k isa Q
                push!(logs, _pow(t.args[1], Num(k)))
            else
                push!(rest, _scale(t, k))
            end
        end
        if !isempty(logs)
            return _mul(vcat(logs, Term[_exp(_add(rest))]))
        end
    end
    return Fn(:exp, Term[x])
end

function _from_factors_except(f, i::Int)::Term
    g = Pair{Term,Term}[f[j] for j in eachindex(f) if j != i]
    isempty(g) && return ONE
    return _from_factors(g)
end

function _log(x::Term)::Term
    x == ONE && return ZERO
    if _isfloat(x)
        v = _fl(x)
        return v >= 0 ? Num(log(v)) : toterm(log(Complex(v)))
    end
    x == INF && return INF
    if x isa Fn && x.head === :exp
        a = x.args[1]
        _isreal_struct(a) && return a
    end
    if x isa Pow && x.base isa Fn && x.base.head === :exp && _isreal_struct(x.base.args[1]) && _isreal_struct(x.exp)
        return _mul((x.exp, x.base.args[1]))
    end
    return Fn(:log, Term[x])
end

function _sin(x::Term)::Term
    x == ZERO && return ZERO
    _isfloat(x) && return Num(sin(_fl(x)))
    k = _pi_multiple(x)
    if k !== nothing
        _isint(k) && return ZERO
        if denominator(k) == 2
            return isodd(div(numerator(k) - 1, 2)) ? MONE : ONE
        end
    end
    x isa Fn && x.head === :asin && return x.args[1]
    _looks_negative(x) && return _mul((MONE, _sin(_mul((MONE, x)))))
    return Fn(:sin, Term[x])
end

function _cos(x::Term)::Term
    x == ZERO && return ONE
    _isfloat(x) && return Num(cos(_fl(x)))
    k = _pi_multiple(x)
    if k !== nothing
        _isint(k) && return iseven(numerator(k)) ? ONE : MONE
        denominator(k) == 2 && return ZERO
    end
    x isa Fn && x.head === :acos && return x.args[1]
    _looks_negative(x) && return _cos(_mul((MONE, x)))
    return Fn(:cos, Term[x])
end

function _tan(x::Term)::Term
    x == ZERO && return ZERO
    _isfloat(x) && return Num(tan(_fl(x)))
    k = _pi_multiple(x)
    k !== nothing && _isint(k) && return ZERO
    x isa Fn && x.head === :atan && return x.args[1]
    _looks_negative(x) && return _mul((MONE, _tan(_mul((MONE, x)))))
    return Fn(:tan, Term[x])
end

function _simplefn(h::Symbol, f::Function, x::Term; odd::Bool = false, zero = nothing)::Term
    zero !== nothing && x == ZERO && return zero
    _isfloat(x) && return Num(f(_fl(x)))
    if odd && _looks_negative(x)
        return _mul((MONE, _simplefn(h, f, _mul((MONE, x)); odd = odd, zero = zero)))
    end
    return Fn(h, Term[x])
end

function _abs(x::Term)::Term
    x isa Num && return Num(abs(x.val))
    x == PI && return PI
    s = _signset(x)
    s & (NEG | CPX) == 0 && return x
    s & (POS | CPX) == 0 && return _mul((MONE, x))
    if x isa Mul
        return _mul(Term[Num(abs(x.c)); [_abs(_powraw(p)) for p in x.factors]])
    end
    if x isa Pow && _isreal_struct(x.exp) && _isreal_struct(x.base)
        isint(x.exp) && iseven(numerator(x.exp.val)) && return x
        return _pow(_abs(x.base), x.exp)
    end
    x isa Fn && x.head === :abs && return x
    x == IM && return ONE
    return Fn(:abs, Term[x])
end

function _sign(x::Term)::Term
    x isa Num && return Num(sign(x.val))
    s = _signset(x)
    s == POS && return ONE
    s == NEG && return MONE
    s == ZER && return ZERO
    return Fn(:sign, Term[x])
end

function _conj(x::Term)::Term
    _isreal_struct(x) && return x
    x == IM && return _mul((MONE, IM))
    x isa Add && return _add(Term[Num(x.c); [_mul((Num(k), _conj(t))) for (t, k) in x.terms]])
    x isa Mul && return _mul(Term[Num(x.c); [_pow(_conj(b), e) for (b, e) in x.factors]])
    x isa Pow && _isreal_struct(x.exp) && return _pow(_conj(x.base), x.exp)
    x isa Fn && x.head in (:exp, :sin, :cos, :tan, :sinh, :cosh, :tanh) && return _fncall(x.head, Term[_conj(x.args[1])])
    return Fn(:conj, Term[x])
end

"""
    reim(x) -> (re, im)

Real and imaginary parts of `x`, treating the symbols as having the domains
they were declared with (real by default). Throws if a part cannot be separated.
"""
function reim(x::Term)
    _isreal_struct(x) && return (x, ZERO)
    y = expand(x)
    re, ims = Term[], Term[]
    for t in _summands(y)
        if _isreal_struct(t)
            push!(re, t)
        else
            q = _mul((t, _pow(IM, MONE)))
            if _isreal_struct(q)
                push!(ims, q)
            else
                return (Fn(:re, Term[x]), Fn(:im, Term[x]))
            end
        end
    end
    return (_add(re), _add(ims))
end
reim(x::Number) = (toterm(real(x)), toterm(imag(x)))

_summands(x::Add) = Term[(iszero(x.c) ? Term[] : Term[Num(x.c)]); [_scale(t, k) for (t, k) in x.terms]]
_summands(x::Term) = Term[x]

# rebuild a function application through its smart constructor
function _fncall(h::Symbol, args)::Term
    length(args) == 1 || return Fn(h, args)
    x = args[1]
    h === :exp && return _exp(x)
    h === :log && return _log(x)
    h === :sin && return _sin(x)
    h === :cos && return _cos(x)
    h === :tan && return _tan(x)
    h === :asin && return _simplefn(:asin, asin, x; odd = true, zero = ZERO)
    h === :acos && return _simplefn(:acos, acos, x)
    h === :atan && return _simplefn(:atan, atan, x; odd = true, zero = ZERO)
    h === :sinh && return _simplefn(:sinh, sinh, x; odd = true, zero = ZERO)
    h === :cosh && return _simplefn(:cosh, cosh, x; zero = ONE)
    h === :tanh && return _simplefn(:tanh, tanh, x; odd = true, zero = ZERO)
    h === :abs && return _abs(x)
    h === :sign && return _sign(x)
    h === :conj && return _conj(x)
    return Fn(h, args)
end

Base.exp(x::Term) = _exp(x)
Base.log(x::Term) = _log(x)
Base.log(b::Number, x::Term) = _log(x) / _log(toterm(b))
Base.log(b::Term, x::Number) = _log(toterm(x)) / _log(b)
Base.log(b::Term, x::Term) = _log(x) / _log(b)
Base.sqrt(x::Term) = _pow(x, HALF)
Base.cbrt(x::Term) = _pow(x, Num(Q(1) // 3))
Base.sin(x::Term) = _sin(x)
Base.cos(x::Term) = _cos(x)
Base.tan(x::Term) = _tan(x)
Base.asin(x::Term) = _fncall(:asin, Term[x])
Base.acos(x::Term) = _fncall(:acos, Term[x])
Base.atan(x::Term) = _fncall(:atan, Term[x])
Base.sinh(x::Term) = _fncall(:sinh, Term[x])
Base.cosh(x::Term) = _fncall(:cosh, Term[x])
Base.tanh(x::Term) = _fncall(:tanh, Term[x])
Base.abs(x::Term) = _abs(x)
Base.sign(x::Term) = _sign(x)
Base.conj(x::Term) = _conj(x)
Base.adjoint(x::Term) = _conj(x)
Base.transpose(x::Term) = x
Base.real(x::Term) = reim(x)[1]
Base.imag(x::Term) = reim(x)[2]
Base.isreal(x::Term) = _isreal_struct(x)

"""
    UFun(name)

An undefined function: `n = UFun(:n)`, then `n(t)` is the term `n(t)`, which
[`diff`](@ref) differentiates to `D(n(t), t)`. Usually made with [`@funs`](@ref).
"""
struct UFun
    name::Symbol
end
(f::UFun)(args...) = Fn(f.name, Term[toterm(a) for a in args])
Base.show(io::IO, f::UFun) = print(io, f.name)

"""
    RootOf(p, x, k)

The `k`-th root (in the order of `roots` on the numeric polynomial) of the
polynomial `p` in `x`, for roots that have no closed form here.
"""
RootOf(p::Term, x::Sym, k::Integer) = Fn(:RootOf, Term[p, x, Num(k)])
