# Integration.
#
# A heuristic integrator, in the order: linearity and constant factors; a table
# of elementary antiderivatives with linear inner arguments; rational functions
# by partial fractions (logs and arctangents); substitution where the integrand
# is f(u(x)) u'(x) up to a constant; integration by parts for polynomial times
# exp/sin/cos/log/inverse trig, and exp times sin/cos; finally expanding the
# integrand and trying again. A full Risch integrator is on the roadmap.

"""
    integrate(f, x)
    integrate(f, (x, a, b))
    integrate(f, x, a, b)

The antiderivative of `f` with respect to `x` (without a constant), or the
definite integral from `a` to `b` (which may be `∞`/`-∞`), computed from the
antiderivative as a difference of one-sided limits. If no antiderivative is
found the result is the unevaluated `∫(f, x)`.

The definite integral assumes the antiderivative is continuous on the
interval: an integrand singular inside `(a, b)` is not detected.
"""
function integrate(f, x::Sym)
    f = toterm(f)
    F = _int(f, x, 0)
    F === nothing && return Fn(:Integral, Term[f, x])
    return simplify(F)
end
integrate(f, r::Tuple) = integrate(f, r...)
function integrate(f, x::Sym, a, b)
    F = integrate(f, x)
    F isa Fn && F.head === :Integral && return Fn(:Integral, Term[toterm(f), x, toterm(a), toterm(b)])
    hi = limit(F, x, b; dir = :left)
    lo = limit(F, x, a; dir = :right)
    ((hi isa Fn && hi.head === :Limit) || (lo isa Fn && lo.head === :Limit)) &&
        return Fn(:Integral, Term[toterm(f), x, toterm(a), toterm(b)])
    if (hi == INF && lo == INF) || (hi == MINF && lo == MINF)
        return Fn(:Integral, Term[toterm(f), x, toterm(a), toterm(b)])
    end
    return simplify(hi - lo)
end

# linear in x: (α, β) with u = αx + β, α ≠ 0
function _linear(u::Term, x::Sym)
    cs = polycoeffs(u, x)
    (cs === nothing || length(cs) != 2 || iszero(cs[2]) || has(cs[2], x)) && return nothing
    return (cs[2], cs[1])
end

function _int(f::Term, x::Sym, depth::Int)
    depth > 6 && return nothing
    has(f, x) || return _mul((f, x))
    f == x && return _mul((HALF, _pow(x, TWO)))
    if f isa Add
        parts = Term[]
        ok = true
        for s in _summands(f)
            F = _int(s, x, depth)
            if F === nothing
                ok = false
                break
            end
            push!(parts, F)
        end
        ok && return _add(parts)
    end
    if f isa Mul
        cs = Term[Num(f.c)]
        rest = Pair{Term,Term}[]
        for p in f.factors
            (has(p.first, x) || has(p.second, x)) ? push!(rest, p) : push!(cs, _powraw(p))
        end
        if length(cs) > 1 || !isone(f.c)
            r = _from_factors(rest)
            F = _int(r, x, depth)
            F !== nothing && return _mul(vcat(cs, Term[F]))
            return nothing
        end
    end
    F = _int_table(f, x)
    F !== nothing && return F
    F = _int_rational(f, x, depth)
    F !== nothing && return F
    F = _int_subst(f, x, depth)
    F !== nothing && return F
    F = _int_parts(f, x, depth)
    F !== nothing && return F
    g = _safe(expand, f)
    if g !== nothing && g != f && g isa Add
        F = _int(g, x, depth + 1)
        F !== nothing && return F
    end
    g = _safe(cancel, f)
    if g !== nothing && g != f
        F = _int(g, x, depth + 1)
        F !== nothing && return F
    end
    return nothing
end

function _int_table(f::Term, x::Sym)
    if f isa Pow
        b, e = f.base, f.exp
        if !has(e, x)
            l = _linear(b, x)
            l === nothing && return nothing
            α = l[1]
            e == MONE && return _mul((_log(b), _pow(α, MONE)))
            e1 = _add((e, ONE))
            return _mul((_pow(b, e1), _pow(_mul((e1, α)), MONE)))
        elseif !has(b, x)
            l = _linear(e, x)
            l === nothing && return nothing
            return _mul((f, _pow(_mul((l[1], _log(b))), MONE)))
        end
        return nothing
    end
    f isa Fn && length(f.args) == 1 || return nothing
    u = f.args[1]
    l = _linear(u, x)
    l === nothing && return nothing
    ia = _pow(l[1], MONE)
    h = f.head
    r = if h === :exp
        f
    elseif h === :sin
        -_cos(u)
    elseif h === :cos
        _sin(u)
    elseif h === :tan
        -_log(_cos(u))
    elseif h === :log
        u * _log(u) - u
    elseif h === :sinh
        _fncall(:cosh, Term[u])
    elseif h === :cosh
        _fncall(:sinh, Term[u])
    elseif h === :tanh
        _log(_fncall(:cosh, Term[u]))
    elseif h === :atan
        u * f - _log(1 + u^2) / 2
    elseif h === :asin
        u * f + sqrt(1 - u^2)
    elseif h === :acos
        u * f - sqrt(1 - u^2)
    else
        nothing
    end
    r === nothing && return nothing
    return _mul((r, ia))
end

function _isrational_in(f::Term, x::Sym)
    gens = _collect_gens!(Gens(), _inner(cancel, f)).list
    return all(g -> g == x || !has(g, x), gens)
end

function _int_rational(f::Term, x::Sym, depth::Int)
    _isrational_in(f, x) || return nothing
    f = cancel(f)
    den = denominator(f)
    if !has(den, x)
        cs = polycoeffs(f, x)
        cs === nothing && return nothing
        return _add(Term[_mul((c, _pow(x, Num(k)), Num(Q(1) // k))) for (k, c) in enumerate(cs)])
    end
    p = _safe(y -> apart(y, x), f)
    p === nothing && return nothing
    if p isa Add && length(_summands(p)) > 1
        parts = Term[]
        for s in _summands(p)
            F = _int_simplefrac(s, x)
            F === nothing && (F = _int(s, x, depth + 1))
            F === nothing && return nothing
            push!(parts, F)
        end
        return _add(parts)
    end
    return _int_simplefrac(p, x)
end

# one partial fraction: polynomial, A/(αx+β)^k or (Bx + C)/(ax² + bx + c)
function _int_simplefrac(s::Term, x::Sym)
    n, d = numerator(s), denominator(s)
    has(d, x) || return _int_rational_poly(s, x)
    c, fs = factor_list(d)
    xf = [(g, k) for (g, k) in fs if has(g, x)]
    length(xf) == 1 || return nothing
    g, k = xf[1]
    scal = _mul(Term[c; [_pow(h, Num(j)) for (h, j) in fs if !has(h, x)]])
    nc = polycoeffs(n, x)
    gc = polycoeffs(g, x)
    (nc === nothing || gc === nothing) && return nothing
    if length(gc) == 2
        # A/(αx+β)^k with A possibly linear-free: integrate the polynomial numerator over a power
        length(nc) == 1 || return nothing
        return _mul((nc[1], _pow(scal, MONE), _int_table(_pow(g, Num(-k)), x)))
    elseif length(gc) == 3 && k == 1 && length(nc) <= 2
        C = nc[1]
        B = length(nc) == 2 ? nc[2] : ZERO
        cc, b, a = gc
        disc = simplify(4 * a * cc - b^2)
        sq = simplify(sqrt(disc))
        part1 = iszero(B) ? ZERO : B / (2a) * _log(g)
        k2 = simplify(C - B * b / (2a))
        part2 = iszero(k2) ? ZERO : k2 * 2 / sq * _fncall(:atan, Term[(2a * x + b) / sq])
        return _mul((_pow(scal, MONE), part1 + part2))
    end
    return nothing
end
function _int_rational_poly(s::Term, x::Sym)
    cs = polycoeffs(s, x)
    cs === nothing && return nothing
    return _add(Term[_mul((c, _pow(x, Num(k)), Num(Q(1) // k))) for (k, c) in enumerate(cs)])
end

# ∫ f(u) u' dx = ∫ f(U) dU
function _int_subst(f::Term, x::Sym, depth::Int)
    cands = _collect_sub!(Term[], y -> has(y, x) && y != x, f)
    inner = Term[]
    for y in cands
        if y isa Fn
            append!(inner, y.args)
        elseif y isa Pow
            push!(inner, y.base)
            has(y.exp, x) && push!(inner, y.exp)
        end
        y isa Union{Fn,Pow} && push!(inner, y)
    end
    unique!(inner)
    filter!(u -> has(u, x) && u != x, inner)
    sort!(inner; by = complexity, rev = true)
    for u in inner
        du = diff(u, x)
        iszero(du) && continue
        q = _safe(z -> cancel(f / z), du)
        q === nothing && continue
        U = Sym(gensym(:U), SymInfo(_isreal_struct(u), false, nothing, false, nothing, false))
        q2 = subs(q, u => U)
        if has(q2, x)
            # try inverting u = U for x
            xs = _safe(z -> (_SOLVE_WARN[] = false; r = _solve1(u - z, x); _SOLVE_WARN[] = true; r), U)
            _SOLVE_WARN[] = true
            (xs === nothing || length(xs) != 1) && continue
            q2 = cancel(subs(q, x => xs[1]))
            has(q2, x) && continue
        end
        complexity(q2) > 3 * complexity(f) + 10 && continue
        G = _int(q2, U, depth + 1)
        G === nothing && continue
        return subs(G, U => u)
    end
    return nothing
end

_ispolyin(p::Term, x::Sym) = polycoeffs(p, x) !== nothing

function _int_parts(f::Term, x::Sym, depth::Int)
    facs = f isa Mul ? Term[_powraw(p) for p in f.factors] : Term[f]
    f isa Mul && !isone(f.c) && return nothing
    # exp(lin) * sin/cos(lin)
    if length(facs) == 2
        e = findfirst(y -> y isa Fn && y.head === :exp && _linear(y.args[1], x) !== nothing, facs)
        t = findfirst(y -> y isa Fn && y.head in (:sin, :cos) && _linear(y.args[1], x) !== nothing, facs)
        if e !== nothing && t !== nothing
            E, T = facs[e], facs[t]
            a = _linear(E.args[1], x)[1]
            b = _linear(T.args[1], x)[1]
            u = T.args[1]
            den = a^2 + b^2
            r = T.head === :sin ? (a * _sin(u) - b * _cos(u)) : (a * _cos(u) + b * _sin(u))
            return E * r / den
        end
    end
    polys = Term[y for y in facs if _ispolyin(y, x)]
    others = Term[y for y in facs if !_ispolyin(y, x)]
    length(others) == 1 || return nothing
    g = others[1]
    P = _mul(polys)
    if g isa Fn && g.head in (:exp, :sin, :cos, :sinh, :cosh) && _linear(g.args[1], x) !== nothing
        n = degree(P, x)
        (n === nothing || n > 12) && return nothing
        out = Term[]
        G = g
        Pk = P
        sgn = 1
        for k in 0:n
            G = _int_table(G, x)
            G === nothing && return nothing
            push!(out, sgn * Pk * G)
            Pk = diff(Pk, x)
            sgn = -sgn
        end
        return _add(out)
    elseif g isa Fn && g.head in (:log, :atan, :asin, :acos) && !isempty(polys)
        Pi = _int(P, x, depth + 1)
        Pi === nothing && return nothing
        rest = _int(cancel(Pi * diff(g, x)), x, depth + 1)
        rest === nothing && return nothing
        return Pi * g - rest
    elseif g isa Pow && g.base isa Fn && g.base.head === :log && isint(g.exp) && g.exp.val > 0
        # ∫ P log(u)^n: by parts, reducing the power
        Pi = _int(P, x, depth + 1)
        Pi === nothing && return nothing
        rest = _int(cancel(Pi * diff(g, x)), x, depth + 1)
        rest === nothing && return nothing
        return Pi * g - rest
    end
    return nothing
end
