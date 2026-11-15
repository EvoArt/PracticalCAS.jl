# Elementary functions and undefined functions.
#
# Each known function has a smart constructor that evaluates the cases that are
# always valid (exp(0) = 1, exp(log x) = x, log(exp x) = x for real x, sin(kπ) = 0,
# odd/even symmetry) and floats numerically; otherwise it returns an `Fn`.

const KNOWN_FUNCTIONS = (:exp, :log, :sin, :cos, :tan, :asin, :acos, :atan,
    :sinh, :cosh, :tanh, :abs, :sign, :conj, :re, :im, :RootOf, :Integral,
    :erf, :erfi, :Ei, :Si, :Ci, :factorial, :gamma, :binomial, :Sum, :Product)

# the special functions integration produces
const SPECIAL_FUNCTIONS = (:erf, :erfi, :Ei, :Si, :Ci)

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

# x = mπ/2 + rest with an integer m ≠ 0 (from a π term of a sum, or a
# number times π times a sum), or nothing
function _pi_split(x::Term)
    k, rest = nothing, x
    if x isa Add
        i = findfirst(p -> p.first == PI, x.terms)
        i === nothing && return nothing
        k = x.terms[i].second
        rest = _add(Term[Num(x.c); [_scale(t, c) for (j, (t, c)) in enumerate(x.terms) if j != i]])
    elseif x isa Mul && length(x.factors) == 2 && x.c isa Q
        (b1, e1), (b2, e2) = x.factors
        pf, af = b1 == PI && e1 == ONE ? (b1, b2) : b2 == PI && e2 == ONE ? (b2, b1) : (nothing, nothing)
        (pf === nothing || !(af isa Add) || (b1 == PI ? e2 : e1) != ONE || !(af.c isa Q) || iszero(af.c)) && return nothing
        k = x.c * af.c
        rest = _mul((Num(x.c), PI, _add(Term[_scale(t, c) for (t, c) in af.terms])))
    end
    (k isa Q && _isint(2k)) || return nothing
    m = Int(mod(numerator(2k), 4))
    return (m, rest)
end

function _sin(x::Term)::Term
    x == ZERO && return ZERO
    s = _pi_split(x)
    if s !== nothing
        m, r = s
        m == 0 && return _sin(r)
        m == 1 && return _cos(r)
        m == 2 && return _mul((MONE, _sin(r)))
        return _mul((MONE, _cos(r)))
    end
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
    s = _pi_split(x)
    if s !== nothing
        m, r = s
        m == 0 && return _cos(r)
        m == 1 && return _mul((MONE, _sin(r)))
        m == 2 && return _mul((MONE, _cos(r)))
        return _sin(r)
    end

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
    _isfloat(x) && return toterm(f(_fl(x)))
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

function _reim(x::Term)
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
_reim(x::Number) = (toterm(real(x)), toterm(imag(x)))

const _REIMDOC = """
    reim(x) -> (re, im)

Real and imaginary parts of the term `x`, treating the symbols as having the
domains they were declared with (real by default). A part that cannot be
separated is returned as `re(x)` / `im(x)`.
"""
# newer Julia has Base.reim: extend it for terms instead of clashing with it
@static if isdefined(Base, :reim)
    import Base: reim
end
@doc _REIMDOC reim(x::Term) = _reim(x)


_summands(x::Add) = Term[(iszero(x.c) ? Term[] : Term[Num(x.c)]); [_scale(t, k) for (t, k) in x.terms]]
_summands(x::Term) = Term[x]

# asin, acos, atan at the standard values
function _invtrig_exact(h::Symbol, x::Term)
    s3, s2 = _pow(Num(3), HALF), _pow(Num(2), HALF)
    neg = _looks_negative(x)
    y = neg ? _mul((MONE, x)) : x
    v = if h === :atan
        y == ONE ? Q(1, 4) : y == s3 ? Q(1, 3) : y == _mul((Num(Q(1, 3)), s3)) ? Q(1, 6) : nothing
    else
        y == ONE ? Q(1, 2) : y == HALF ? Q(1, 6) : y == _mul((HALF, s2)) ? Q(1, 4) :
        y == _mul((HALF, s3)) ? Q(1, 3) : nothing
    end
    v === nothing && return nothing
    if h === :acos
        # acos(y) = π/2 - asin(y), acos(-y) = π/2 + asin(y)
        return _mul((PI, Num(neg ? Q(1, 2) + v : Q(1, 2) - v)))
    end
    return _mul((PI, Num(neg ? -v : v)))
end

# rebuild a function application through its smart constructor
function _fncall(h::Symbol, args)::Term
    h === :binomial && length(args) == 2 && return _binomial(args[1], args[2])
    length(args) == 1 || return Fn(h, args)
    x = args[1]
    h === :exp && return _exp(x)
    h === :log && return _log(x)
    h === :sin && return _sin(x)
    h === :cos && return _cos(x)
    h === :tan && return _tan(x)
    if h in (:asin, :acos, :atan)
        v = _invtrig_exact(h, x)
        v !== nothing && return v
    end
    h === :asin && return _simplefn(:asin, asin, x; odd = true, zero = ZERO)
    h === :acos && return _simplefn(:acos, acos, x)
    h === :atan && return _simplefn(:atan, atan, x; odd = true, zero = ZERO)
    h === :sinh && return _simplefn(:sinh, sinh, x; odd = true, zero = ZERO)
    h === :cosh && return _simplefn(:cosh, cosh, x; zero = ONE)
    h === :tanh && return _simplefn(:tanh, tanh, x; odd = true, zero = ZERO)
    h === :erf && return _simplefn(:erf, _nerf, x; odd = true, zero = ZERO)
    h === :erfi && return _simplefn(:erfi, _nerfi, x; odd = true, zero = ZERO)
    h === :Si && return _simplefn(:Si, _nSi, x; odd = true, zero = ZERO)
    h === :Ei && return _simplefn(:Ei, _nEi, x)
    h === :Ci && return _simplefn(:Ci, _nCi, x)
    h === :factorial && return _factorial(x)
    h === :gamma && return _gamma(x)
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

"""
    erf(x), erfi(x)

The error function `erf(x) = 2/√π ∫₀ˣ exp(-t²) dt` and the imaginary error
function `erfi(x) = -i erf(ix) = 2/√π ∫₀ˣ exp(t²) dt`. Symbolic on terms,
numeric (Float64) on numbers.
"""
erf(x::Term) = _fncall(:erf, Term[x])
erf(x::Number) = _nerf(x)
erfi(x::Term) = _fncall(:erfi, Term[x])
erfi(x::Number) = _nerfi(x)
@doc (@doc erf) erfi

"""
    Ei(x), Si(x), Ci(x)

The exponential integral `Ei(x) = ∫ exp(t)/t dt` (principal value, from -∞),
the sine integral `Si(x) = ∫₀ˣ sin(t)/t dt` and the cosine integral
`Ci(x) = γ + log(x) + ∫₀ˣ (cos(t) - 1)/t dt`. Symbolic on terms, numeric on
numbers.
"""
Ei(x::Term) = _fncall(:Ei, Term[x])
Ei(x::Number) = _nEi(x)
Si(x::Term) = _fncall(:Si, Term[x])
Si(x::Number) = _nSi(x)
Ci(x::Term) = _fncall(:Ci, Term[x])
Ci(x::Number) = _nCi(x)
@doc (@doc Ei) Si
@doc (@doc Ei) Ci
Base.sign(x::Term) = _sign(x)
Base.conj(x::Term) = _conj(x)
Base.adjoint(x::Term) = _conj(x)
Base.transpose(x::Term) = x
Base.real(x::Term) = _reim(x)[1]
Base.imag(x::Term) = _reim(x)[2]
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

# ---- factorials, the gamma function, binomial coefficients -------------------------

_natural(x::Term) = x isa Num && x.val isa Q && _isint(x.val) && x.val >= 0

function _factorial(x::Term)::Term
    _natural(x) && return Num(Q(factorial(numerator(x.val))))
    _isfloat(x) && return Num(_nfactorial(_fl(x)))
    return Fn(:factorial, Term[x])
end

# Γ(n) = (n - 1)! at positive integers, Γ(n + 1/2) = (2n)! √π / (4ⁿ n!)
function _gamma(x::Term)::Term
    if x isa Num && x.val isa Q
        v = x.val
        _isint(v) && v > 0 && return Num(Q(factorial(numerator(v) - 1)))
        if denominator(v) == 2 && v > 0
            n = numerator(v - Q(1, 2))
            return _mul((Num(Q(factorial(2n), 4^n * factorial(n))), _pow(PI, HALF)))
        end
    end
    _isfloat(x) && return Num(_ngamma(_fl(x)))
    return Fn(:gamma, Term[x])
end

# binomial(n, k) for a natural number k is the polynomial n(n-1)⋯(n-k+1)/k!,
# for any n; negative integer k gives 0
function _binomial(n::Term, k::Term)::Term
    if k isa Num && k.val isa Q && _isint(k.val)
        k.val < 0 && return ZERO
        if n isa Num && n.val isa Q && _isint(n.val)
            return Num(Q(binomial(numerator(n.val), numerator(k.val))))
        end
        kk = Int(numerator(k.val))
        kk <= 12 && return _mul(Term[Num(Q(1, factorial(big(kk)))); [_add((n, Num(-j))) for j in 0:kk-1]])
    end
    (_isfloat(n) || _isfloat(k)) && n isa Num && k isa Num && return Num(_nbinomial(n.val, k.val))
    return Fn(:binomial, Term[n, k])
end

Base.factorial(x::Term) = _factorial(x)
Base.binomial(n::Term, k::Term) = _binomial(n, k)
Base.binomial(n::Term, k::Integer) = _binomial(n, toterm(k))
Base.binomial(n::Integer, k::Term) = _binomial(toterm(n), k)

"""
    gamma(x)

The gamma function `Γ(x) = ∫₀^∞ t^(x-1) e^(-t) dt`, with `Γ(n) = (n-1)!`.
Exact at positive integers and half-integers, numeric on floats, symbolic
otherwise. `factorial(x)` (`x!`) and `binomial(n, k)` also accept terms:
`binomial(n, 2)` is `n(n - 1)/2`.
"""
gamma(x::Term) = _gamma(x)
gamma(x::Number) = _ngamma(x)
