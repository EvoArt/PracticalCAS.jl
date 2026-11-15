# Limits.
#
# A limit x → a is turned into a one-sided limit t → 0⁺ (x = a ± t, or x = ±1/t
# for a = ±∞). The term is then classified bottom-up as tending to a finite
# value, to 0 from above or below, or to ±∞; indeterminate forms (0/0, ∞/∞,
# 0·∞, ∞ - ∞) are resolved by cancelling, then L'Hôpital's rule.

const MINF = Mul(Q(-1), Pair{Term,Term}[INF => ONE])

# classes: :fin (value v), :zp / :zn (0 from above / below), :z (0, side
# unknown), :pinf, :minf, :ind (indeterminate), :unk
const _ZEROS = (:zp, :zn, :z)
const _INFS = (:pinf, :minf)

function _finclass(v::Term)
    c = _safe(cancel, v)
    c === nothing && return (:unk, v)
    iszero(c) && return (:z, ZERO)
    return (:fin, c)
end

function _lv(g::Term, t::Sym)::Tuple{Symbol,Term}
    has(g, t) || return g == INF ? (:pinf, ZERO) : g == MINF ? (:minf, ZERO) : _finclass(g)
    g == t && return (:zp, ZERO)
    if g isa Add
        cls = [_lv(_scale(u, k), t) for (u, k) in g.terms]
        push!(cls, (:fin, Num(g.c)))
        any(c -> c[1] in (:ind, :unk), cls) && return (:ind, ZERO)
        hasp = any(c -> c[1] === :pinf, cls)
        hasm = any(c -> c[1] === :minf, cls)
        hasp && hasm && return (:ind, ZERO)
        hasp && return (:pinf, ZERO)
        hasm && return (:minf, ZERO)
        v = _add(Term[c[2] for c in cls if c[1] === :fin])
        fc = _finclass(v)
        if fc[1] === :z
            zs = [c[1] for c in cls if c[1] in _ZEROS]
            nonz = [c for c in cls if c[1] === :fin && !iszero(c[2])]
            if isempty(nonz) && !isempty(zs) && all(==(zs[1]), zs)
                return (zs[1], ZERO)
            end
            return (:z, ZERO)
        end
        return fc
    elseif g isa Mul
        cls = Tuple{Symbol,Term}[(:fin, Num(g.c))]
        for (b, e) in g.factors
            push!(cls, _lvpow(b, e, t))
        end
        return _lvprod(cls)
    elseif g isa Pow
        return _lvpow(g.base, g.exp, t)
    elseif g isa Fn
        return _lvfn(g, t)
    end
    return (:unk, ZERO)
end

function _sgn_of_class(c)
    k = c[1]
    k in (:zp, :pinf) && return 1
    k in (:zn, :minf) && return -1
    if k === :fin
        s = sign_of(c[2])
        s == POS && return 1
        s == NEG && return -1
    end
    return 0
end

function _lvprod(cls)
    any(c -> c[1] in (:ind, :unk), cls) && return (:ind, ZERO)
    nz = count(c -> c[1] in _ZEROS, cls)
    ni = count(c -> c[1] in _INFS, cls)
    nz > 0 && ni > 0 && return (:ind, ZERO)
    if ni > 0
        s = prod(_sgn_of_class(c) for c in cls)
        s == 0 && return (:unk, ZERO)
        return (s > 0 ? :pinf : :minf, ZERO)
    end
    if nz > 0
        any(c -> c[1] === :z, cls) && return (:z, ZERO)
        s = prod(_sgn_of_class(c) for c in cls)
        s == 0 && return (:z, ZERO)
        return (s > 0 ? :zp : :zn, ZERO)
    end
    return _finclass(_mul(Term[c[2] for c in cls]))
end

function _lvpow(b::Term, e::Term, t::Sym)
    e == ONE && return _lv(b, t)
    if has(e, t)
        return _lv(_exp(_mul((e, _log(b)))), t)
    end
    cb = _lv(b, t)
    k = cb[1]
    k in (:ind, :unk) && return cb
    es = sign_of(e)
    if k === :fin
        return _finclass(_pow(cb[2], e))
    elseif k === :zp
        es == POS && return (:zp, ZERO)
        es == NEG && return (:pinf, ZERO)
    elseif k === :pinf
        es == POS && return (:pinf, ZERO)
        es == NEG && return (:zp, ZERO)
    elseif (k === :zn || k === :minf) && isint(e)
        n = numerator(e.val)
        if k === :zn
            return n > 0 ? (iseven(n) ? (:zp, ZERO) : (:zn, ZERO)) : (iseven(n) ? (:pinf, ZERO) : (:minf, ZERO))
        else
            return n > 0 ? (iseven(n) ? (:pinf, ZERO) : (:minf, ZERO)) : (iseven(n) ? (:zp, ZERO) : (:zn, ZERO))
        end
    elseif k === :z
        es == POS && return (:z, ZERO)
    end
    return (:unk, ZERO)
end

function _lvfn(g::Fn, t::Sym)
    length(g.args) == 1 || return (:unk, ZERO)
    isknownfn(g.head) || return (:unk, ZERO)
    c = _lv(g.args[1], t)
    k, v = c
    k in (:ind, :unk) && return (:ind, ZERO)
    h = g.head
    if k === :fin
        return _finclass(_fncall(h, Term[v]))
    end
    if h === :exp
        k in _ZEROS && return (:fin, ONE)
        k === :pinf && return (:pinf, ZERO)
        k === :minf && return (:zp, ZERO)
    elseif h === :log
        k === :zp && return (:minf, ZERO)
        k === :pinf && return (:pinf, ZERO)
    elseif h in (:sin, :tan, :sinh, :tanh, :asin, :atan) && k in _ZEROS
        return (k, ZERO)
    elseif h in (:cos, :cosh) && k in _ZEROS
        return (:fin, ONE)
    elseif h === :atan && k in _INFS
        return (:fin, k === :pinf ? PI / 2 : -PI / 2)
    elseif h === :tanh && k in _INFS
        return (:fin, k === :pinf ? ONE : MONE)
    elseif h in (:sinh, :cosh) && k in _INFS
        return (h === :cosh || k === :pinf) ? (:pinf, ZERO) : (:minf, ZERO)
    elseif h in (:erf, :erfi, :Si) && k in _ZEROS
        return (k, ZERO)
    elseif h === :erf && k in _INFS
        return (:fin, k === :pinf ? ONE : MONE)
    elseif h === :erfi && k in _INFS
        return (k, ZERO)
    elseif h === :Si && k in _INFS
        return (:fin, k === :pinf ? PI / 2 : -PI / 2)
    elseif h === :Ei
        k === :pinf && return (:pinf, ZERO)
        k === :minf && return (:zn, ZERO)
        k in _ZEROS && return (:minf, ZERO)
    elseif h === :Ci
        k === :pinf && return (:z, ZERO)
        k === :zp && return (:minf, ZERO)
    elseif h === :abs
        k in _ZEROS && return (:zp, ZERO)
        k in _INFS && return (:pinf, ZERO)
    end
    return (:unk, ZERO)
end

function _classval(c)
    k, v = c
    k === :fin && return simplify(v)
    k in _ZEROS && return ZERO
    k === :pinf && return INF
    k === :minf && return MINF
    return nothing
end

function _lim0(g::Term, t::Sym, depth::Int = 0)
    c = _lv(g, t)
    v = _classval(c)
    v !== nothing && return v
    depth > 8 && return nothing
    g2 = _safe(cancel, g)
    if g2 !== nothing && g2 != g
        v = _classval(_lv(g2, t))
        v !== nothing && return v
    else
        g2 = g
    end
    # quotient forms: L'Hôpital
    n, d = numerator(g2), denominator(g2)
    if d != ONE
        cn, cd = _lv(n, t), _lv(d, t)
        if (cn[1] in _ZEROS && cd[1] in _ZEROS) || (cn[1] in _INFS && cd[1] in _INFS)
            return _lim0(cancel(diff(n, t) / diff(d, t)), t, depth + 1)
        end
        if !(cn[1] in (:ind, :unk)) && !(cd[1] in (:ind, :unk))
            v = _classval(_lvprod([cn, _lvpow(d, MONE, t)]))
            v !== nothing && return v
        end
    end
    # products 0·∞ written as a quotient
    if g isa Mul
        zs, ws, cs = Term[], Term[], Term[Num(g.c)]
        for (b, e) in g.factors
            f = _powraw(b => e)
            k = _lv(f, t)[1]
            k in _ZEROS ? push!(zs, f) : k in _INFS ? push!(ws, f) : push!(cs, f)
        end
        if !isempty(zs) && !isempty(ws)
            num = _mul(vcat(cs, ws))
            den = _pow(_mul(zs), MONE)
            return _lim0(cancel(diff(num, t) / diff(den, t)), t, depth + 1)
        end
    end
    # n with indeterminate parts: try L'Hôpital on the log for exponentials
    return nothing
end

"""
    limit(f, x, a; dir = :both)

The limit of `f` as `x → a` (`a` may be `∞` or `-∞`; `dir` is `:both`, `:left`
or `:right`). Returns `∞`/`-∞` for divergence to infinity, and an unevaluated
`Limit(…)` if it cannot decide (or the one-sided limits differ).
"""
function limit(f, x::Sym, a; dir::Symbol = :both)
    f = toterm(f)
    a = toterm(a)
    if a isa Num && a.val isa Float64 && isinf(a.val)
        a = a.val > 0 ? INF : MINF
    end
    t = Sym(gensym(:t), SymInfo(true, false, Q(0), true, nothing, false))
    if a == INF
        return _limres(_lim0(subs(f, x => _pow(t, MONE)), t), f, x, a)
    elseif a == MINF
        return _limres(_lim0(subs(f, x => _mul((MONE, _pow(t, MONE)))), t), f, x, a)
    end
    direct = _safe(y -> subs(f, x => y), a)
    if direct !== nothing && !_singular(direct)
        return simplify(direct)
    end
    if dir === :right
        return _limres(_lim0(subs(f, x => a + t), t), f, x, a)
    elseif dir === :left
        return _limres(_lim0(subs(f, x => a - t), t), f, x, a)
    end
    r = _lim0(subs(f, x => a + t), t)
    l = _lim0(subs(f, x => a - t), t)
    (r === nothing || l === nothing) && return Fn(:Limit, Term[f, x, a])
    (r == l || isequiv(r, l)) && return r
    return Fn(:Limit, Term[f, x, a])
end
_limres(v, f, x, a) = v === nothing ? Fn(:Limit, Term[f, x, a]) : v

# a value that is not a usable limit: log(0), 0^negative, ∞ inside
function _singular(v::Term)
    has(v, INF) && return true
    bad = _collect_sub!(Term[], y -> (y isa Fn && y.head === :log && y.args[1] == ZERO) ||
                                     (y isa Pow && y.base == ZERO), v)
    return !isempty(bad)
end
