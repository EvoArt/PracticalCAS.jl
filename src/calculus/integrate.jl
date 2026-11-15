# Integration: the driver.
#
# `integrate` tries a sequence of methods on the integrand, from cheap special
# cases to complete algorithms:
#
#   polynomials, constant factors, a table of elementary functions of linear
#   arguments; rational functions (Hermite reduction and Lazard–Rioboo–Trager,
#   complete, ratint.jl); linearity; integration by parts; erf and Ei forms;
#   substitution (derivative divides, with inversion); rationalising
#   substitutions for radicals of linear polynomials; square roots of
#   quadratics (reduction to ∫dx/√Q) and Euler's substitutions; trigonometric
#   integrands by Bioche's rules and by linearisation through complex
#   exponentials; the Risch–Norman parallel integrator (risch_norman.jl); and
#   finally the expanded and cancelled forms of the integrand.
#
# Every candidate antiderivative is checked by differentiating it and comparing
# with the integrand at several numeric points that satisfy the assumptions, so
# a heuristic can fail to find an antiderivative but never return a wrong one.

const _INTDEBUG = Ref(false)

mutable struct _IntCtx
    cache::Dict{Tuple{Term,Sym},Union{Term,Nothing}}
    active::Vector{Tuple{Term,Sym}}
    budget::Int
end
_IntCtx() = _IntCtx(Dict{Tuple{Term,Sym},Union{Term,Nothing}}(), Tuple{Term,Sym}[], 600)

const _METHODS = (
    (:poly, _im_poly), (:const, _im_const), (:table, _im_table), (:ratint, _im_ratint),
    (:sum, _im_sum), (:parts, _im_parts), (:expquad, _im_expquad), (:expei, _im_expei),
    (:risch_norman_notrig, _im_risch_notrig), (:bioche_odd, _im_bioche_odd), (:fourier, _im_fourier),
    (:subst, _im_subst), (:radlin, _im_radlin), (:sqrtquad, _im_sqrtquad), (:bioche, _im_bioche),
    (:risch_norman, (c, f, x) -> _risch_norman(f, x)), (:euler, _im_euler), (:rewrite, _im_rewrite))

"""
    integrate(f, x)
    integrate(f, (x, a, b))
    integrate(f, x, a, b)

The antiderivative of `f` with respect to `x` (without a constant), or the
definite integral from `a` to `b` (which may be `∞`/`-∞`), computed from the
antiderivative as a difference of one-sided limits. If no antiderivative is
found the result is the unevaluated `∫(f, x)`.

Rational functions are integrated completely (logarithms and arctangents, or
sums over the roots of an irreducible polynomial as `RootOf`); elementary
integrands by rules and the Risch–Norman heuristic; some non-elementary ones in
terms of `erf`, `erfi`, `Ei`, `Si` and `Ci`. Every antiderivative returned has
been checked by differentiation.

For a definite integral, poles of a rational integrand inside the interval
make the result unevaluated, and the jumps of `tan` in an antiderivative are
accounted for when the bounds are numbers.
"""
function integrate(f, x::Sym)
    f = toterm(f)
    F = _integrate(f, x)
    F === nothing && return Fn(:Integral, Term[f, x])
    return F
end
integrate(f, r::Tuple) = integrate(f, r...)

function _integrate(f::Term, x::Sym)
    fl = _hasfloat(f)
    g = fl ? _rationalize(f) : f
    g === nothing && return nothing
    ctx = _IntCtx()
    F = _irec(ctx, g, x)
    F === nothing && return nothing
    F = _dropconst(_postint(F), x)
    S = _safe(simplify, F)
    if S !== nothing && S != F && complexity(S) <= complexity(F) && _verify(S, g, x)
        F = S
    end
    return fl ? _floatify(F) : F
end

function _irec(ctx::_IntCtx, f::Term, x::Sym)
    has(f, x) || return _mul((f, x))
    key = (f, x)
    haskey(ctx.cache, key) && return ctx.cache[key]
    key in ctx.active && return nothing
    (length(ctx.active) > 12 || ctx.budget <= 0) && return nothing
    ctx.budget -= 1
    push!(ctx.active, key)
    F = try
        _imethods(ctx, f, x)
    finally
        pop!(ctx.active)
    end
    ctx.cache[key] = F
    return F
end

function _imethods(ctx::_IntCtx, f::Term, x::Sym)
    for (name, m) in _METHODS
        F = try
            m(ctx, f, x)
        catch err
            err isa InterruptException && rethrow()
            _INTDEBUG[] && @warn "integrate: $name failed on $f" exception = err
            nothing
        end
        F === nothing && continue
        # a real integrand gets an answer without i
        if has(F, IM) && !has(f, IM)
            _INTDEBUG[] && @warn "integrate: $name gave a complex form" f F
            continue
        end
        if _verify(F, f, x)
            _INTDEBUG[] && @info "integrate: $name: ∫ $f = $F"
            return F
        end
        _INTDEBUG[] && @warn "integrate: $name gave a wrong antiderivative" f F
    end
    return nothing
end

# ---- verification ----------------------------------------------------------------

const _VPTS = (0.6180339887, 1.3247179572, 0.4142135624, 1.7320508076, 0.8660254038,
    2.2360679775, 0.3183098862, 1.1892071150, 0.5772156649, 1.4655712319, 0.7548776662,
    1.0986122887, 0.2679491924, 1.9318516526)

function _sample(s::Sym, j::Int, k::Int)
    i = s.info
    v = _VPTS[mod(3j + 5k, length(_VPTS))+1] * (1 + 0.137 * mod(j, 5))
    if i.integer
        lo = i.lo === nothing ? 1 : ceil(Int, Float64(i.lo))
        return Num(lo + 1 + mod(j + k, 3))
    end
    i.real || return toterm(complex(v, 0.37 * v))
    lo, hi = i.lo, i.hi
    if lo !== nothing && hi !== nothing
        return Num(Float64(lo) + v / (v + 1) * Float64(hi - lo))
    elseif lo !== nothing
        return Num(Float64(lo) + v)
    elseif hi !== nothing
        return Num(Float64(hi) - v)
    end
    # unbounded real symbols take both signs
    return Num(isodd(k) ? -v : v)
end

function _facts_ok(d)
    for (g, mask) in FACTS
        all(s -> haskey(d, s), free_symbols(g)) || continue
        v = _numval(g, d)
        v === nothing && continue
        v = real(v)
        bit = v < 0 ? NEG : (v == 0 ? ZER : POS)
        (bit & mask) == 0 && return false
    end
    return true
end

function _numval(t::Term, d)
    try
        v = _ev(subs(t, d))
        return v isa Number ? v : nothing
    catch err
        err isa InterruptException && rethrow()
        return nothing
    end
end

_hasintegral(F::Term) = !isempty(_collect_sub!(Term[], y -> y isa Fn && y.head in (:Integral, :Limit, :re, :im), F))

"""
    _verify(F, f, x) -> Bool

Whether d/dx F equals f at several numeric points (respecting the symbols'
assumptions and the facts).
"""
function _verify(F::Term, f::Term, x::Sym)
    _hasintegral(F) && return false
    dF = _safe(y -> diff(y, x), F)
    dF === nothing && return false
    syms = union(free_symbols(F), free_symbols(f))
    x in syms || push!(syms, x)
    # the variable of a RootOf is bound
    for r in _collect_sub!(Term[], y -> y isa Fn && y.head === :RootOf, F)
        filter!(s -> s != r.args[2], syms)
    end
    good = 0
    for k in 1:14
        d = Dict{Term,Term}(s => _sample(s, j, k) for (j, s) in enumerate(syms))
        _facts_ok(d) || continue
        a = _numval(dF, d)
        b = _numval(f, d)
        (a === nothing || b === nothing) && continue
        (isfinite(a) && isfinite(b)) || continue
        abs(a - b) <= 1e-7 * max(abs(a), abs(b)) + 1e-10 || return false
        good += 1
        good >= 3 && return true
    end
    return good >= 2
end

# ---- floats, tidying -------------------------------------------------------------

_ratv(v::Q) = v
_ratv(v::Float64) = isfinite(v) ? Q(rationalize(BigInt, v)) : throw(ArgumentError("integrate: non-finite number"))
function _rationalize(x::Term)::Term
    x isa Num && return Num(_ratv(x.val))
    x isa Add && return _add(Term[Num(_ratv(x.c)); [_mul((Num(_ratv(k)), _rationalize(t))) for (t, k) in x.terms]])
    x isa Mul && return _mul(Term[Num(_ratv(x.c)); [_pow(_rationalize(b), _rationalize(e)) for (b, e) in x.factors]])
    x isa Pow && return _pow(_rationalize(x.base), _rationalize(x.exp))
    x isa Fn && return _fncall(x.head, Term[_rationalize(a) for a in x.args])
    return x
end
_fv(v) = v isa Q && !_isint(v) ? Float64(v) : v
function _floatify(x::Term)::Term
    x isa Num && return Num(_fv(x.val))
    x isa Add && return _add(Term[Num(_fv(x.c)); [_mul((Num(_fv(k)), _floatify(t))) for (t, k) in x.terms]])
    x isa Mul && return _mul(Term[Num(_fv(x.c)); [_pow(_floatify(b), e) for (b, e) in x.factors]])
    x isa Pow && return _pow(_floatify(x.base), x.exp)
    x isa Fn && return _fncall(x.head, Term[_floatify(a) for a in x.args])
    return x
end

# without its x-free summands (constants of integration)
function _dropconst(F::Term, x::Sym)
    G = F isa Add ? F : (complexity(F) < 150 ? _safe(expand, F) : nothing)
    (G isa Add && any(s -> !has(s, x), _summands(G))) || return F
    H = _add(Term[s for s in _summands(G) if has(s, x)])
    return F isa Add ? H : (complexity(H) <= complexity(F) + 4 ? H : F)
end

# atan(tan(u)) = u and log(-u) for log(u) with u ≤ 0, each up to a constant
function _postint(F::Term)::Term
    F isa Union{Num,Const,Sym} && return F
    y = _map(_postint, F)
    if y isa Fn && y.head === :atan && y.args[1] isa Fn && y.args[1].head === :tan
        return y.args[1].args[1]
    end
    if y isa Fn && y.head === :log
        a = y.args[1]
        s = sign_of(a)
        if (s & (POS | CPX)) == 0 && s != ZER
            return _log(cancel(-a))
        end
        # log(k u) = log(u) + constant, for the rational content k of a sum
        if a isa Add && a.c isa Q && all(p -> p.second isa Q, a.terms)
            ks = Q[k for (_, k) in a.terms]
            iszero(a.c) || push!(ks, a.c)
            k = Q(gcd(numerator.(ks)), lcm(denominator.(ks)))
            k > 0 && !isone(k) && return _log(_mul((Num(inv(k)), a)))
        end
    end
    return y
end

# ---- definite integrals ------------------------------------------------------------

function integrate(f, x::Sym, a, b)
    f, a, b = toterm(f), toterm(a), toterm(b)
    unev = Fn(:Integral, Term[f, x, a, b])
    F = integrate(f, x)
    F isa Fn && F.head === :Integral && return unev
    _pole_inside(f, x, a, b) && return unev
    pts = _tan_jumps(F, x, a, b)
    pts === nothing && return unev
    nodes = Term[a; pts; b]
    total = Term[]
    for k in 1:length(nodes)-1
        hi = k + 1 < length(nodes) ? _jumpval(F, x, nodes[k+1], :left) : limit(F, x, nodes[k+1]; dir = :left)
        lo = k > 1 ? _jumpval(F, x, nodes[k], :right) : limit(F, x, nodes[k]; dir = :right)
        ((hi isa Fn && hi.head === :Limit) || (lo isa Fn && lo.head === :Limit)) && return unev
        ((hi == INF && lo == INF) || (hi == MINF && lo == MINF)) && return unev
        push!(total, hi - lo)
    end
    r = _add(total)
    (has(r, INF) && length(total) > 1) && return unev
    return simplify(r)
end

_numbound(a::Term) = (a == INF ? Inf : a == MINF ? -Inf : (v = _numval(a, Dict{Term,Term}()); v isa Real ? Float64(v) : nothing))

# a real pole of a rational integrand strictly inside (a, b)
function _pole_inside(f::Term, x::Sym, a::Term, b::Term)
    lo, hi = _numbound(a), _numbound(b)
    (lo === nothing || hi === nothing) && return false
    lo > hi && ((lo, hi) = (hi, lo))
    _isratfun(f, x) || return false
    den = denominator(cancel(f))
    cs = polycoeffs(den, x)
    cs === nothing && return false
    vs = Any[_numval(c, Dict{Term,Term}()) for c in cs]
    any(v -> !(v isa Number), vs) && return false
    for r in _numroots(ComplexF64.(vs))
        abs(imag(r)) < 1e-9 * max(1, abs(r)) || continue
        lo + 1e-12 < real(r) < hi - 1e-12 && return true
    end
    return false
end

# the one-sided limit of F at a point p where some tan(αx + β) in F is infinite
function _jumpval(F::Term, x::Sym, p::Term, dir::Symbol)
    τ = _isym(:τ, _IPOS)
    d = Dict{Term,Term}()
    for t in _collect_sub!(Term[], y -> y isa Fn && y.head === :tan && has(y, x), F)
        l = _linear(t.args[1], x)
        l === nothing && return Fn(:Limit, Term[F, x, p])
        cv = _numval(_cos(subs(t.args[1], x => p)), Dict{Term,Term}())
        (cv isa Number && abs(cv) < 1e-12) || continue
        αv = _numval(l[1], Dict{Term,Term}())
        s = (dir === :left) == (real(αv) > 0) ? 1 : -1
        d[t] = s / τ
    end
    G = subs(subs(F, d), x => p)
    return limit(G, τ, 0; dir = :right)
end

# the points in (a, b) where a tan(αx + β) in F jumps (nothing if infinitely many)
function _tan_jumps(F::Term, x::Sym, a::Term, b::Term)
    atoms = _collect_sub!(Term[], y -> y isa Fn && y.head === :tan && has(y, x), F)
    isempty(atoms) && return Term[]
    lo, hi = _numbound(a), _numbound(b)
    (lo === nothing || hi === nothing) && return Term[]
    (isinf(lo) || isinf(hi)) && return nothing
    pts = Term[]
    for t in atoms
        l = _linear(t.args[1], x)
        l === nothing && return nothing
        α, β = l
        av, bv = _numval(α, Dict{Term,Term}()), _numval(β, Dict{Term,Term}())
        (av isa Real && bv isa Real) || return nothing
        # αx + β = π/2 + kπ
        ks = sort([(av * lo + bv - π / 2) / π, (av * hi + bv - π / 2) / π])
        for k in ceil(Int, ks[1]):floor(Int, ks[2])
            p = cancel((PI / 2 + k * PI - β) / α)
            pv = _numval(p, Dict{Term,Term}())
            (min(lo, hi) < pv < max(lo, hi)) && push!(pts, p)
        end
    end
    unique!(pts)
    sort!(pts; by = p -> _numval(p, Dict{Term,Term}()), rev = _numbound(a) > _numbound(b))
    return pts
end
