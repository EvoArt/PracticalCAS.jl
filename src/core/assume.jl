# The sign engine: what is known about the sign of a term, from the symbols'
# assumptions, facts (assume!), the structure of the term, and interval
# arithmetic over the symbols' bounds.
#
# A sign set is a bitmask of the values a term can take: NEG, ZER, POS (real) and
# CPX (possibly non-real). These functions are cheap and purely structural; the
# simplify layer (sign_of) adds factorisation on top.

const NEG = 0x01
const ZER = 0x02
const POS = 0x04
const CPX = 0x08
const ALLR = 0x07
const ANYS = 0x0f

_flipmask(m::UInt8) = (m & ZER) | (m & CPX) | ((m & NEG) != 0 ? POS : 0x00) | ((m & POS) != 0 ? NEG : 0x00)

const _ADDTAB = Dict((NEG, NEG) => NEG, (NEG, ZER) => NEG, (NEG, POS) => ALLR,
    (ZER, ZER) => ZER, (ZER, POS) => POS, (POS, POS) => POS,
    (ZER, NEG) => NEG, (POS, NEG) => ALLR, (POS, ZER) => POS)
const _MULTAB = Dict((NEG, NEG) => POS, (NEG, ZER) => ZER, (NEG, POS) => NEG,
    (ZER, ZER) => ZER, (ZER, POS) => ZER, (POS, POS) => POS,
    (ZER, NEG) => ZER, (POS, NEG) => NEG, (POS, ZER) => ZER)

function _scomb(tab, a::UInt8, b::UInt8)
    ((a | b) & CPX) != 0 && return ANYS
    r = 0x00
    for sa in (NEG, ZER, POS), sb in (NEG, ZER, POS)
        if (a & sa) != 0 && (b & sb) != 0
            r |= tab[(sa, sb)]
        end
    end
    return r
end
_sadd(a, b) = _scomb(_ADDTAB, a, b)
_smul(a, b) = _scomb(_MULTAB, a, b)
_numsign(v) = v > 0 ? POS : (v < 0 ? NEG : ZER)

"""
    _signset(x) -> UInt8

The set of signs `x` can have, as a mask of NEG/ZER/POS/CPX.
"""
function _signset(x::Term)::UInt8
    s = _signstruct(x)
    (s == POS || s == NEG || s == ZER) && return s
    iv = _ival(x)
    if iv !== nothing
        t = s & _ivalmask(iv)
        t != 0 && (s = t)
    end
    if !isempty(FACTS) && !(x isa Num)
        k, g = _normlead(x)
        for (f, m) in FACTS
            if f == g
                mm = k > 0 ? m : _flipmask(m)
                t = s & mm
                t != 0 && (s = t)
            end
        end
    end
    return s
end

_signstruct(x::Num) = _numsign(x.val)
_signstruct(x::Const) = x.name === :I ? CPX : POS
function _signstruct(x::Sym)
    i = x.info
    i.real || return ANYS
    lo, hi = i.lo, i.hi
    m = 0x00
    (lo === nothing || lo < 0) && (m |= NEG)
    (hi === nothing || hi > 0) && (m |= POS)
    zl = lo === nothing || lo < 0 || (lo == 0 && !i.lo_open)
    zh = hi === nothing || hi > 0 || (hi == 0 && !i.hi_open)
    (zl && zh) && (m |= ZER)
    return m == 0 ? ALLR : m
end
function _signstruct(x::Add)
    s = _numsign(x.c)
    for (t, k) in x.terms
        s = _sadd(s, _smul(_numsign(k), _signset(t)))
        s == ANYS && return s
    end
    return s
end
function _signstruct(x::Mul)
    s = _numsign(x.c)
    for (b, e) in x.factors
        s = _smul(s, _powsign(b, e))
        s == ANYS && return s
    end
    return s
end
_signstruct(x::Pow) = _powsign(x.base, x.exp)
function _powsign(b::Term, e::Term)::UInt8
    e == ONE && return _signset(b)
    sb = _signset(b)
    if e isa Num && e.val isa Q
        if _isint(e.val)
            (sb & CPX) != 0 && return ANYS
            n = numerator(e.val)
            m = iseven(n) ? (((sb & (NEG | POS)) != 0 ? POS : 0x00) | (sb & ZER)) : sb
            n < 0 && (m &= ~ZER)
            return m == 0 ? POS : m
        end
        if (sb & (NEG | CPX)) == 0
            m = (sb & POS) | (e.val > 0 ? (sb & ZER) : 0x00)
            return m == 0 ? POS : m
        end
        return ANYS
    end
    if sb == POS && _isreal_struct(e)
        return POS
    end
    return ANYS
end
function _signstruct(x::Fn)
    h = x.head
    if h === :exp
        return _isreal_struct(x.args[1]) ? POS : ANYS
    elseif h === :log
        sa = _signset(x.args[1])
        return sa == POS ? ALLR : ANYS
    elseif h === :abs
        sa = _signset(x.args[1])
        return (sa & ZER) != 0 ? (POS | ZER) : POS
    elseif h in (:sin, :cos, :tan, :atan, :sinh, :tanh, :asin, :acos, :sign)
        r = _isreal_struct(x.args[1]) ? ALLR : ANYS
        h === :cosh && return r == ALLR ? POS : ANYS
        h === :acos && return r == ALLR ? (POS | ZER) : ANYS
        return r
    elseif h === :cosh
        return _isreal_struct(x.args[1]) ? POS : ANYS
    end
    return ANYS
end
_signstruct(::Deriv) = ANYS

_isreal_struct(x::Term) = (_signset(x) & CPX) == 0
_isreal_struct(x::Number) = isreal(x)
_nonneg_struct(x::Term) = (_signset(x) & (NEG | CPX)) == 0
_ispos_struct(x::Term) = _signset(x) == POS
_isneg_struct(x::Term) = _signset(x) == NEG

# normalise to leading coefficient 1: x = k * g
function _normlead(x::Term)
    if x isa Add
        k = x.terms[1].second
        return (k, isone(k) ? x : _mul((Num(_ninv(k)), x)))
    elseif x isa Mul
        return (x.c, _from_factors(x.factors))
    elseif x isa Num
        return (x.val, ONE)
    end
    return (Q(1), x)
end
_ninv(k::Q) = inv(k)
_ninv(k::Float64) = 1 / k

# ---- intervals over exact rationals with infinite endpoints ---------------------

const XR = Union{Q,Float64}      # Float64 only for ±Inf

struct Ival
    lo::XR
    lc::Bool
    hi::XR
    hc::Bool
end

_isinfx(a) = a isa Float64
function _xadd(a::XR, b::XR)
    if a isa Float64 && b isa Float64
        return a == b ? a : NaN
    end
    a isa Float64 && return a
    b isa Float64 && return b
    return a + b
end
function _xmul(a::XR, b::XR)
    (iszero(a) || iszero(b)) && return Q(0)
    if a isa Float64 || b isa Float64
        return sign(a) * sign(b) > 0 ? Inf : -Inf
    end
    return a * b
end
_xneg(a::XR) = -a

function _ivalmask(iv::Ival)::UInt8
    m = 0x00
    iv.lo < 0 && (m |= NEG)
    iv.hi > 0 && (m |= POS)
    lo0 = iv.lo < 0 || (iv.lo == 0 && iv.lc)
    hi0 = iv.hi > 0 || (iv.hi == 0 && iv.hc)
    (lo0 && hi0) && (m |= ZER)
    return m
end

const _REALLINE = Ival(-Inf, false, Inf, false)

function _iadd(a::Ival, b::Ival)
    lo = _xadd(a.lo, b.lo)
    hi = _xadd(a.hi, b.hi)
    ((lo isa Float64 && isnan(lo)) || (hi isa Float64 && isnan(hi))) && return nothing
    return Ival(lo, a.lc && b.lc && !_isinfx(lo), hi, a.hc && b.hc && !_isinfx(hi))
end

function _iscale(a::Ival, k::Q)
    iszero(k) && return Ival(Q(0), true, Q(0), true)
    k > 0 && return Ival(_xmul(a.lo, k), a.lc, _xmul(a.hi, k), a.hc)
    return Ival(_xmul(a.hi, k), a.hc, _xmul(a.lo, k), a.lc)
end

function _imul(a::Ival, b::Ival)
    cands = Tuple{XR,Bool}[]
    for (x, xc) in ((a.lo, a.lc), (a.hi, a.hc)), (y, yc) in ((b.lo, b.lc), (b.hi, b.hc))
        v = _xmul(x, y)
        closed = (xc && yc) || (iszero(x) && xc) || (iszero(y) && yc)
        push!(cands, (v, closed && !_isinfx(v)))
    end
    lo = minimum(first, cands)
    hi = maximum(first, cands)
    lc = any(c -> c[1] == lo && c[2], cands)
    hc = any(c -> c[1] == hi && c[2], cands)
    return Ival(lo, lc, hi, hc)
end

function _iinv(a::Ival)
    if a.lo > 0 || (a.lo == 0 && !a.lc)
        lo = a.hi isa Float64 ? Q(0) : inv(a.hi)
        hi = iszero(a.lo) ? Inf : inv(a.lo)
        return Ival(lo, a.hc && !(a.hi isa Float64), hi, a.lc && !iszero(a.lo))
    elseif a.hi < 0 || (a.hi == 0 && !a.hc)
        b = _iinv(Ival(-a.hi, a.hc, -a.lo, a.lc))
        b === nothing && return nothing
        return Ival(-b.hi, b.hc, -b.lo, b.lc)
    end
    return nothing
end

function _xpow(a::XR, n::Int)
    a isa Float64 && return (a > 0 || iseven(n)) ? Inf : -Inf
    return a^n
end

function _ipow_int(a::Ival, n::Int)
    n == 0 && return Ival(Q(1), true, Q(1), true)
    if n < 0
        p = _ipow_int(a, -n)
        return p === nothing ? nothing : _iinv(p)
    end
    if isodd(n) || a.lo >= 0
        return Ival(_xpow(a.lo, n), a.lc, _xpow(a.hi, n), a.hc)
    elseif a.hi <= 0
        return Ival(_xpow(a.hi, n), a.hc, _xpow(a.lo, n), a.lc)
    end
    m, mc = (-a.lo > a.hi) ? (_xpow(a.lo, n), a.lc) : (_xpow(a.hi, n), a.hc)
    return Ival(Q(0), true, m, mc)
end

function _ival(x::Num)
    v = x.val isa Q ? x.val : (isfinite(x.val) ? Q(x.val) : nothing)
    v === nothing && return nothing
    return Ival(v, true, v, true)
end
function _ival(x::Const)
    x.name === :π && return Ival(Q(3), false, Q(4), false)
    return nothing
end
function _ival(x::Sym)
    i = x.info
    i.real || return nothing
    lo = i.lo === nothing ? -Inf : i.lo
    hi = i.hi === nothing ? Inf : i.hi
    return Ival(lo, i.lo !== nothing && !i.lo_open, hi, i.hi !== nothing && !i.hi_open)
end
function _ival(x::Add)
    c = x.c isa Q ? x.c : Q(x.c)
    acc = Ival(c, true, c, true)
    for (t, k) in x.terms
        it = _ival(t)
        it === nothing && return nothing
        acc = _iadd(acc, _iscale(it, k isa Q ? k : Q(k)))
        acc === nothing && return nothing
    end
    return acc
end
function _ival(x::Mul)
    c = x.c isa Q ? x.c : Q(x.c)
    acc = Ival(c, true, c, true)
    for (b, e) in x.factors
        it = _ival_pow(b, e)
        it === nothing && return nothing
        acc = _imul(acc, it)
    end
    return acc
end
_ival(x::Pow) = _ival_pow(x.base, x.exp)
function _ival_pow(b::Term, e::Term)
    ib = _ival(b)
    ib === nothing && return nothing
    e == ONE && return ib
    if isint(e)
        n = numerator(e.val)
        abs(n) > 64 && return nothing
        return _ipow_int(ib, Int(n))
    end
    if e isa Num && ib.lo >= 0
        ev = e.val
        if ev > 0
            lo, lc = ib.lo > 0 ? (Q(0), false) : (Q(0), ib.lc)
            hi, hc = (ib.hi <= 1) ? (Q(1), ib.hi == 1 && ib.hc) : (Inf, false)
            return Ival(lo, lc, hi, hc)
        end
    end
    return nothing
end
function _ival(x::Fn)
    if x.head === :exp
        a = _ival(x.args[1])
        a === nothing && return Ival(Q(0), false, Inf, false)
        lo, lc = a.lo >= 0 ? (Q(1), a.lo == 0 && a.lc) : (Q(0), false)
        hi, hc = a.hi <= 0 ? (Q(1), a.hi == 0 && a.hc) : (Inf, false)
        return Ival(lo, lc, hi, hc)
    elseif x.head === :log
        a = _ival(x.args[1])
        (a === nothing || a.lo < 0 || (a.lo == 0 && a.lc)) && return nothing
        lo, lc = a.lo >= 1 ? (Q(0), a.lo == 1 && a.lc) : (-Inf, false)
        hi, hc = a.hi <= 1 ? (Q(0), a.hi == 1 && a.hc) : (Inf, false)
        return Ival(lo, lc, hi, hc)
    elseif x.head in (:sin, :cos)
        return _isreal_struct(x.args[1]) ? Ival(Q(-1), true, Q(1), true) : nothing
    elseif x.head === :abs
        return Ival(Q(0), true, Inf, false)
    end
    return nothing
end
_ival(::Term) = nothing
