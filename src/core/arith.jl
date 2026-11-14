# Arithmetic: the smart constructors `_add`, `_mul`, `_pow` that keep terms in
# canonical form, and the Base operators on top of them.
#
# Automatic simplification is deliberately limited to rules that are always
# valid: like terms combine, x^a * x^b = x^(a+b), numbers fold, exact roots of
# numbers come out (sqrt(8) = 2*sqrt(2)), numeric factors distribute over a sum
# (2(x + y) = 2x + 2y, which is what makes cancellation automatic) and
# exp(a)*exp(b) = exp(a + b). Rules that need assumptions ((x^2)^(1/2) = x) ask
# the sign engine (assume.jl).

_isint(v::Q) = isone(denominator(v))
_isint(::Float64) = false
isint(x::Term) = x isa Num && _isint(x.val)

_nadd(a::Q, b::Q) = a + b
_nadd(a::NumVal, b::NumVal) = Float64(a) + Float64(b)
_nmul(a::Q, b::Q) = a * b
_nmul(a::NumVal, b::NumVal) = Float64(a) * Float64(b)

"""
    toterm(x)

Convert a Julia number (or term) to a term: integers and rationals exactly,
floats as floats, `π` and `ℯ` symbolically, complex numbers as `a + b*im`.
"""
toterm(x::Term) = x
toterm(x::Integer) = Num(x)
toterm(x::Rational) = Num(x)
toterm(x::AbstractFloat) = Num(x)
toterm(::Irrational{:π}) = PI
toterm(::Irrational{:ℯ}) = Fn(:exp, Term[ONE])
toterm(x::Complex) = _add((toterm(real(x)), _mul((toterm(imag(x)), IM))))
toterm(x::Number) = Num(Float64(x))

Base.convert(::Type{Term}, x::Number) = toterm(x)
Base.convert(::Type{Term}, x::Term) = x
Base.promote_rule(::Type{<:Term}, ::Type{<:Number}) = Term
Base.promote_rule(::Type{S}, ::Type{T}) where {S<:Term,T<:Term} = Term

Base.zero(::Type{<:Term}) = ZERO
Base.zero(::Term) = ZERO
Base.one(::Type{<:Term}) = ONE
Base.one(::Term) = ONE
Base.iszero(x::Num) = iszero(x.val)
Base.iszero(::Term) = false
Base.isone(x::Num) = isone(x.val)
Base.isone(::Term) = false

# split a term into numeric coefficient and the rest (coefficient 1)
function _split_coeff(x::Term)::Tuple{NumVal,Term}
    if x isa Mul && !isone(x.c)
        return (x.c, _from_factors(x.factors))
    end
    return (Q(1), x)
end

_base_exp(x::Pow) = (x.base, x.exp)
_base_exp(x::Term) = (x, ONE)

_powraw(p) = p.second == ONE ? p.first : Pow(p.first, p.second)
_from_factors(f)::Term = length(f) == 1 ? _powraw(f[1]) : Mul(Q(1), f)

# k * t, where t has coefficient 1 and is not a number
function _scale(t::Term, k::NumVal)::Term
    isone(k) && return t
    iszero(k) && return ZERO
    t isa Mul && return Mul(_nmul(k, t.c), t.factors)
    t isa Add && return _mul((Num(k), t))
    b, e = _base_exp(t)
    return Mul(k, Pair{Term,Term}[b => e])
end

# ---- sums ------------------------------------------------------------------------

function _add(xs)::Term
    c::NumVal = Q(0)
    d = Dict{Term,NumVal}()
    for x in xs
        if x isa Num
            c = _nadd(c, x.val)
        elseif x isa Add
            c = _nadd(c, x.c)
            for (t, k) in x.terms
                d[t] = _nadd(get(d, t, Q(0)), k)
            end
        else
            k, t = _split_coeff(x)
            d[t] = _nadd(get(d, t, Q(0)), k)
        end
    end
    terms = Pair{Term,NumVal}[t => k for (t, k) in d if !iszero(k)]
    isempty(terms) && return Num(c)
    if iszero(c) && length(terms) == 1
        return _scale(terms[1].first, terms[1].second)
    end
    sort!(terms; lt = (p, q) -> _cmp(p.first, q.first) < 0)
    return Add(iszero(c) ? Q(0) : c, terms)
end

# ---- products ----------------------------------------------------------------------

function _addexp!(d, b::Term, e::Term)
    d[b] = haskey(d, b) ? _add((d[b], e)) : e
    return d
end

const _IPOWS = (ONE, IM, MONE, Mul(Q(-1), Pair{Term,Term}[IM => ONE]))
_ipow(n::Integer) = _IPOWS[mod(n, 4)+1]

function _mul(xs)::Term
    c::NumVal = Q(1)
    d = Dict{Term,Term}()
    for x in xs
        if x isa Num
            c = _nmul(c, x.val)
        elseif x isa Mul
            c = _nmul(c, x.c)
            for (b, e) in x.factors
                _addexp!(d, b, e)
            end
        else
            b, e = _base_exp(x)
            _addexp!(d, b, e)
        end
    end
    iszero(c) && return Num(c)
    facs = Pair{Term,Term}[]
    extra = Term[]
    exps = Term[]
    for (b, e) in d
        e == ZERO && continue
        if b isa Num && e isa Num
            r = _pow_numnum(b.val, e.val)
            if r isa Num
                c = _nmul(c, r.val)
            elseif r isa Pow && r.base isa Num
                push!(facs, r.base => r.exp)
            else
                push!(extra, r)
            end
        elseif b == IM && isint(e)
            k = mod(numerator(e.val), 4)
            k >= 2 && (c = _nmul(c, Q(-1)))
            isodd(k) && push!(facs, IM => ONE)
        elseif b isa Fn && b.head === :exp && isint(e)
            push!(exps, e == ONE ? b.args[1] : _mul((e, b.args[1])))
        elseif b == ZERO && e isa Num && e.val > 0
            return ZERO
        else
            push!(facs, b => e)
        end
    end
    if !isempty(exps)
        ex = _exp(length(exps) == 1 ? exps[1] : _add(exps))
        if ex isa Fn && ex.head === :exp
            push!(facs, ex => ONE)
        else
            push!(extra, ex)
        end
    end
    sort!(facs; lt = (p, q) -> _cmppair(p, q) < 0)
    res = _build_mul(c, facs)
    isempty(extra) && return res
    return _mul(vcat(Term[res], extra))
end

function _build_mul(c::NumVal, facs)::Term
    isempty(facs) && return Num(c)
    if length(facs) == 1
        b, e = facs[1]
        isone(c) && return e == ONE ? b : Pow(b, e)
        if e == ONE && b isa Add
            return Add(_nmul(c, b.c), Pair{Term,NumVal}[t => _nmul(c, k) for (t, k) in b.terms])
        end
    end
    return Mul(c, facs)
end

# ---- powers --------------------------------------------------------------------------

# n = s^q * t with s as large as trial division (up to 10^5) finds
function _extract_power(n::BigInt, q::Int)
    s, t, rem = big(1), big(1), n
    p = 2
    while p * p <= rem && p <= 100_000
        if rem % p == 0
            m = 0
            while rem % p == 0
                rem = div(rem, p)
                m += 1
            end
            s *= big(p)^(m ÷ q)
            t *= big(p)^(m % q)
        end
        p += p == 2 ? 1 : 2
    end
    if rem > 1
        r = round(BigInt, BigFloat(rem)^(1 / q))
        for cand in (r - 1, r, r + 1)
            if cand > 1 && cand^q == rem
                return (s * cand, t)
            end
        end
        t *= rem
    end
    return (s, t)
end

function _pow_numnum(b::NumVal, e::NumVal)::Term
    if b isa Float64 || e isa Float64
        bf, ef = Float64(b), Float64(e)
        if bf < 0 && !isinteger(ef)
            return toterm(Complex(bf)^ef)
        end
        bf == 0 && ef < 0 && throw(DivideError())
        return Num(bf^ef)
    end
    if _isint(e)
        n = numerator(e)
        iszero(b) && n < 0 && throw(DivideError())
        return Num(n >= 0 ? b^Int(n) : inv(b)^Int(-n))
    end
    iszero(b) && return e > 0 ? ZERO : throw(DivideError())
    isone(b) && return ONE
    p, q = numerator(e), denominator(e)
    if b < 0
        q == 2 && return _mul((_ipow(p), _pow_numnum(-b, e)))
        b == -1 && return Pow(MONE, Num(e))
        return _mul((Pow(MONE, Num(e)), _pow_numnum(-b, e)))
    end
    qq = Int(q)
    a = fld(p, q)
    r = p - a * q
    coef = a >= 0 ? b^Int(a) : inv(b)^Int(-a)
    s1, t1 = _extract_power(numerator(b), qq)
    s2, t2 = _extract_power(denominator(b), qq)
    coef *= Q(s1)^Int(r) / Q(s2)^Int(r)
    xs = Term[]
    isone(coef) || push!(xs, Num(coef))
    isone(t1) || push!(xs, Pow(Num(Q(t1)), Num(Q(r) // q)))
    isone(t2) || push!(xs, Pow(Num(Q(t2)), Num(-Q(r) // q)))
    isempty(xs) && return ONE
    return length(xs) == 1 ? xs[1] : _mul(xs)
end

function _pow(b::Term, e::Term)::Term
    e == ZERO && return ONE
    e == ONE && return b
    b == ONE && return ONE
    b isa Num && e isa Num && return _pow_numnum(b.val, e.val)
    if b == ZERO
        e isa Num && e.val > 0 && return ZERO
        e isa Num && throw(DivideError())
        return Pow(b, e)
    end
    b == IM && isint(e) && return _ipow(numerator(e.val))
    if b isa Pow
        b0, e0 = b.base, b.exp
        if isint(e) || (_nonneg_struct(b0) && _isreal_struct(e0) && _isreal_struct(e))
            return _pow(b0, _mul((e0, e)))
        end
    end
    if b isa Mul
        if isint(e)
            xs = Term[_pow_numnum(b.c, e.val)]
            for (bi, ei) in b.factors
                push!(xs, _pow(bi, _mul((ei, e))))
            end
            return _mul(xs)
        end
        out = Term[]
        inside = Term[]
        if b.c > 0
            push!(out, _pow(Num(b.c), e))
        else
            push!(out, _pow(Num(-b.c), e))
            push!(inside, MONE)
        end
        for (bi, ei) in b.factors
            if _nonneg_struct(bi) && _isreal_struct(ei) && _isreal_struct(e)
                push!(out, _pow(bi, _mul((ei, e))))
            else
                push!(inside, _powraw(bi => ei))
            end
        end
        isempty(inside) && return _mul(out)
        length(inside) == length(b.factors) + (b.c > 0 ? 0 : 1) && isone(abs(b.c)) && return Pow(b, e)
        rest = _mul(inside)
        push!(out, rest isa Mul ? Pow(rest, e) : _pow(rest, e))
        return _mul(out)
    end
    if b isa Fn && b.head === :exp && (isint(e) || (_isreal_struct(b.args[1]) && _isreal_struct(e)))
        return _exp(_mul((e, b.args[1])))
    end
    # sqrt of something known negative: sqrt(-x) = im*sqrt(x)
    if e isa Num && e.val isa Q && denominator(e.val) == 2 && _isneg_struct(b)
        return _mul((_ipow(numerator(e.val)), _pow(_mul((MONE, b)), e)))
    end
    return Pow(b, e)
end

# ---- Base operators ------------------------------------------------------------------

Base.:+(a::Term, b::Term) = _add((a, b))
Base.:+(a::Term, b::Number) = _add((a, toterm(b)))
Base.:+(a::Number, b::Term) = _add((toterm(a), b))
Base.:+(a::Term) = a
Base.:-(a::Term) = _mul((MONE, a))
Base.:-(a::Term, b::Term) = _add((a, _mul((MONE, b))))
Base.:-(a::Term, b::Number) = _add((a, toterm(-b)))
Base.:-(a::Number, b::Term) = _add((toterm(a), _mul((MONE, b))))
Base.:*(a::Term, b::Term) = _mul((a, b))
Base.:*(a::Term, b::Number) = _mul((a, toterm(b)))
Base.:*(a::Number, b::Term) = _mul((toterm(a), b))
Base.:*(a::Bool, b::Term) = _mul((toterm(a), b))
Base.:*(a::Term, b::Bool) = _mul((a, toterm(b)))
Base.:/(a::Term, b::Term) = _mul((a, _pow(b, MONE)))
Base.:/(a::Term, b::Number) = _mul((a, _pow(toterm(b), MONE)))
Base.:/(a::Number, b::Term) = _mul((toterm(a), _pow(b, MONE)))
Base.://(a::Term, b::Number) = a / b
Base.://(a::Number, b::Term) = a / b
Base.://(a::Term, b::Term) = a / b
Base.inv(a::Term) = _pow(a, MONE)
Base.:^(a::Term, b::Term) = _pow(a, b)
Base.:^(a::Term, b::Integer) = _pow(a, Num(b))
Base.:^(a::Term, b::Rational) = _pow(a, Num(b))
Base.:^(a::Term, b::Number) = _pow(a, toterm(b))
Base.:^(a::Number, b::Term) = _pow(toterm(a), b)
Base.:^(a::Irrational{:ℯ}, b::Term) = _exp(b)

# muladd(x, y, z) on numbers promotes its arguments, which cannot work for terms
# (each converts to itself); generic matrix code calls it
for (X, Y, Z) in ((:Term, :Term, :Term), (:Term, :Term, :Number), (:Term, :Number, :Term),
                  (:Number, :Term, :Term), (:Term, :Number, :Number), (:Number, :Term, :Number),
                  (:Number, :Number, :Term))
    @eval Base.muladd(x::$X, y::$Y, z::$Z) = x * y + z
end
Base.muladd(x::T, y::T, z::T) where {T<:Term} = x * y + z

Base.Float64(x::Term) = Float64(real(evalf(x)))
Base.Rational(x::Num) = x.val isa Q ? x.val : Rational(x.val)
