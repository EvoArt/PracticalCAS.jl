# Simplification, sign reasoning with factorisation, and deciding conditions.

"""
    sign_of(x) -> UInt8

The set of signs `x` can take (a NEG/ZER/POS/CPX mask), using the symbols'
assumptions, facts from [`assume!`](@ref), and the factored, cancelled and
expanded forms of `x`. See [`ispositive`](@ref) and friends for the Boolean
versions.
"""
function sign_of(x::Term)::UInt8
    s = _signset(x)
    _definite(s) && return s
    x isa Union{Num,Const,Sym} && return s
    for y in (_safe(factor, x), _safe(cancel, x), _safe(expand, x))
        y === nothing && continue
        t = s & _signset(y)
        t != 0 && (s = t)
        _definite(s) && return s
        if y isa Mul
            m = _numsign(y.c)
            for (b, e) in y.factors
                m = _smul(m, _powsign_deep(b, e))
            end
            t = s & m
            t != 0 && (s = t)
            _definite(s) && return s
        end
    end
    return s
end
sign_of(x::Number) = sign_of(toterm(x))
_definite(s) = s == POS || s == NEG || s == ZER || s == (POS | ZER) || s == (NEG | ZER)

function _safe(f, x)
    try
        return f(x)
    catch err
        err isa InterruptException && rethrow()
        return nothing
    end
end

function _powsign_deep(b::Term, e::Term)
    sb = (b isa Add) ? _sign_add_deep(b) : _signset(b)
    e == ONE && return sb
    if isint(e)
        (sb & CPX) != 0 && return ANYS
        n = numerator(e.val)
        m = iseven(n) ? (((sb & (NEG | POS)) != 0 ? POS : 0x00) | (sb & ZER)) : sb
        n < 0 && (m &= ~ZER)
        return m == 0 ? POS : m
    end
    return _powsign(b, e)
end
# a sum: also try it expanded (catches p - p^2 written as p*(1 - p) and similar)
function _sign_add_deep(b::Add)
    s = _signset(b)
    _definite(s) && return s
    y = _safe(expand, b)
    y === nothing && return s
    t = s & _signset(y)
    return t == 0 ? s : t
end

"""
    ispositive(x), isnegative(x), isnonnegative(x), isnonpositive(x), iszero_known(x)

Whether the sign is *provably* positive (etc.) under the assumptions; `false`
means "not known", not "known false".
"""
ispositive(x) = sign_of(x) == POS
isnegative(x) = sign_of(x) == NEG
isnonnegative(x) = (s = sign_of(x); (s & (NEG | CPX)) == 0)
isnonpositive(x) = (s = sign_of(x); (s & (POS | CPX)) == 0)
iszero_known(x) = sign_of(x) == ZER || iszero(cancel(toterm(x)))

"""
    decide(c) -> true, false or nothing

Whether the condition `c` holds for all values allowed by the assumptions
(`true`), for none (`false`), or depends on the parameters (`nothing`).
"""
function decide(c::Rel)
    d = _add((c.lhs, _mul((MONE, c.rhs))))
    d = cancel(d)
    d isa Num && return _rel(c.op, d, ZERO)
    s = sign_of(d)
    (s & CPX) != 0 && return nothing
    ok = _OPMASK[c.op]
    (s & ~ok) == 0 && return true
    (s & ok) == 0 && return false
    return nothing
end
decide(b::Bool) = b
function decide(c::And)
    vals = [decide(a) for a in c.args]
    any(v -> v === false, vals) && return false
    all(v -> v === true, vals) && return true
    return nothing
end
function decide(c::Or)
    vals = [decide(a) for a in c.args]
    any(v -> v === true, vals) && return true
    all(v -> v === false, vals) && return false
    return nothing
end

# ---- simplify ---------------------------------------------------------------------

"""
    simplify(x)

A simpler equivalent form of `x`: tries the cancelled, factored and expanded
forms (after simplifying inside functions and powers) and keeps the smallest.
Uses the assumptions on the symbols: `sqrt(x^2)` is `x` for `x ≥ 0`, `abs(x)`
drops for known signs, `log(exp(x))` is `x` for real `x`. On a condition,
decides it under the assumptions or reduces it: `r*(K - n) > 0` with `r > 0`
becomes `n < K`.
"""
function simplify(x::Term)::Term
    x isa Union{Num,Const,Sym} && return x
    y = _simp_inner(x)
    cands = Term[y]
    for f in (cancel, factor, expand, _trigsimp)
        z = _safe(f, y)
        z !== nothing && push!(cands, z)
    end
    z = _safe(cancel, _safe(expand, y))
    z !== nothing && push!(cands, z)
    best = cands[argmin([complexity(c) for c in cands])]
    return best
end
simplify(x::Number) = toterm(x)
simplify(x::AbstractArray) = map(simplify, x)
simplify(e::Eqn) = Eqn(simplify(e.lhs), simplify(e.rhs))

function _simp_inner(x::Term)::Term
    x isa Union{Num,Const,Sym} && return x
    if x isa Fn
        args = Term[simplify(a) for a in x.args]
        return _fnsimp(_fncall(x.head, args))
    elseif x isa Pow
        b = simplify(x.base)
        e = simplify(x.exp)
        return _powsimp(b, e)
    elseif x isa Add || x isa Mul
        return _map(_simp_inner, x)
    end
    return x
end

# function-level rules that need assumptions or factorisation
function _fnsimp(x::Term)::Term
    x isa Fn || return x
    h, a = x.head, x.args[1]
    if h === :log
        # log(b^e) = e*log(b) for b > 0 and real e; log of a product of positives
        if a isa Pow && ispositive(a.base) && _isreal_struct(a.exp)
            return _mul((a.exp, _log(a.base)))
        end
        if a isa Mul && a.c > 0 && all(p -> ispositive(p.first) && _isreal_struct(p.second), a.factors) && length(a.factors) >= 1
            parts = Term[isone(a.c) ? ZERO : _log(Num(a.c))]
            for (b, e) in a.factors
                push!(parts, _mul((e, _log(b))))
            end
            return _add(parts)
        end
    elseif h === :abs
        s = sign_of(a)
        (s & (NEG | CPX)) == 0 && return a
        (s & (POS | CPX)) == 0 && return _mul((MONE, a))
    elseif h === :sign
        s = sign_of(a)
        s == POS && return ONE
        s == NEG && return MONE
    end
    return x
end

# sqrt(f^2 g) = |f| sqrt(g), and |f| = f when f ≥ 0
function _powsimp(b::Term, e::Term)::Term
    if e isa Num && e.val isa Q && !_isint(e.val) && !(b isa Num)
        q = denominator(e.val)
        c, fs = factor_list(b)
        if !isempty(fs) && any(fk -> fk.second >= q, fs)
            out = Term[]
            inside = Term[c]
            for (f, k) in fs
                whole, r = divrem(k, Int(q))
                if whole != 0
                    af = iseven(q) ? _absknown(f) : f
                    push!(out, _pow(af, Num(whole * e.val * q)))
                end
                r != 0 && push!(inside, _pow(f, Num(r)))
            end
            push!(out, _pow(_mul(inside), e))
            return _mul(out)
        end
    end
    return _pow(b, e)
end
function _absknown(f::Term)
    s = sign_of(f)
    (s & (NEG | CPX)) == 0 && return f
    (s & (POS | CPX)) == 0 && return _mul((MONE, f))
    return _abs(f)
end

# sin² + cos² = 1: rewrite cos² as 1 - sin² and see whether it gets smaller
function _trigsimp(x::Term)::Term
    cs = _collect_sub!(Term[], y -> y isa Fn && y.head === :cos, x)
    isempty(cs) && return x
    y = x
    for c in cs
        u = c.args[1]
        y = _replace_pow(y, c, 2, _add((ONE, _mul((MONE, _pow(_sin(u), TWO))))))
    end
    return cancel(expand(y))
end
function _replace_pow(x::Term, b::Term, k::Int, r::Term)::Term
    if x isa Pow && x.base == b && isint(x.exp) && abs(x.exp.val) >= k
        n = Int(numerator(x.exp.val))
        q, m = divrem(abs(n), k)
        y = _mul((_pow(r, Num(q)), _pow(b, Num(m))))
        return n > 0 ? y : _pow(y, MONE)
    end
    x isa Union{Num,Const,Sym} && return x
    return _map(z -> _replace_pow(z, b, k, r), x)
end

"""
    isequiv(a, b) -> Bool

Whether `a - b` simplifies to zero (exact equality as functions, as far as
cancellation and the elementary rules can tell).
"""
function isequiv(a, b)
    d = toterm(a) - toterm(b)
    iszero(d) && return true
    iszero(cancel(d)) && return true
    z = _safe(x -> cancel(expand(simplify(x))), d)
    return z !== nothing && iszero(z)
end

"""
    logcombine(x)

Combine sums of logarithms into one (`log(a) - log(b)` to `log(a/b)`), as a
formal identity (exact for positive arguments).
"""
function logcombine(x::Term)::Term
    x isa Add || return x
    logs = Term[]
    rest = Term[Num(x.c)]
    for (t, k) in x.terms
        if t isa Fn && t.head === :log && k isa Q && _isint(k)
            push!(logs, _pow(t.args[1], Num(k)))
        elseif t isa Mul && k isa Q
            # k * c * log(u) with rational c
            i = findfirst(p -> p.first isa Fn && p.first.head === :log && p.second == ONE, t.factors)
            if i !== nothing && length(t.factors) == 1
                push!(logs, _pow(t.factors[1].first.args[1], Num(k * t.c)))
            else
                push!(rest, _scale(t, k))
            end
        else
            push!(rest, _scale(t, k))
        end
    end
    length(logs) <= 1 && return x
    return _add(vcat(rest, Term[_log(cancel(_mul(logs)))]))
end

# ---- conditions ------------------------------------------------------------------------

simplify(b::Bool) = b
function simplify(c::Rel)
    v = decide(c)
    v !== nothing && return v
    d = cancel(_add((c.lhs, _mul((MONE, c.rhs)))))
    op = c.op
    # drop factors of known sign (flipping the relation for negative ones)
    cf, fs = factor_list(d)
    cf.val < 0 && (op = _FLIPOP[op])
    keep = Term[]
    for (f, k) in fs
        s = sign_of(f)
        if s == POS || (s == NEG && op in (:(==), :!=)) || (iseven(k) && (s & (ZER | CPX)) == 0)
            continue
        elseif s == NEG
            isodd(k) && (op = _FLIPOP[op])
        elseif op in (:(==), :!=)
            push!(keep, f)
        else
            push!(keep, _pow(f, Num(k)))
        end
    end
    isempty(keep) && return decide(Rel(op, ONE, ZERO)) # cannot happen generically
    g = op in (:(==), :!=) ? _mul(keep) : _mul(keep)
    return _present(op, g)
end

# show `g op 0` with positive terms on the left and negative ones on the right
function _present(op::Symbol, g::Term)
    if g isa Add
        pos, neg = Term[], Term[]
        g.c > 0 && push!(pos, Num(g.c))
        g.c < 0 && push!(neg, Num(-g.c))
        for (t, k) in g.terms
            k > 0 ? push!(pos, _scale(t, k)) : push!(neg, _scale(t, -k))
        end
        if !isempty(pos) && !isempty(neg)
            l, r = _add(pos), _add(neg)
            # a single symbol alone on one side reads best on the left
            if r isa Sym && !(l isa Sym)
                return Rel(_FLIPOP[op], r, l)
            end
            return Rel(op, l, r)
        end
    end
    return Rel(op, g, ZERO)
end

function simplify(c::And)
    parts = Any[simplify(a) for a in c.args]
    return _and(parts)
end
simplify(c::Or) = _or(Any[simplify(a) for a in c.args])
