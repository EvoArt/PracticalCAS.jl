# Solving equations and systems.
#
# One equation: take the numerator of the cancelled form, factor it, and solve
# each factor: polynomial factors by formula (degree ≤ 2, or a polynomial in
# x^k), factors that are polynomial in a single generator g(x) (exp, log, a
# power) by solving for g and inverting. Systems: factor an equation, branch on
# its factors, solve each for a variable it contains, substitute and recurse.

const _SOLVE_WARN = Ref(true)

function _warn_unsolved(g, x)
    _SOLVE_WARN[] && @warn "solve: could not solve $g = 0 for $x; solutions may be missing"
end

"""
    solve(eq, x) -> Vector{Term}
    solve(eqs, xs) -> Vector{Dict{Sym,Term}}

Solve an equation (`lhs ~ rhs`, or an expression meaning `expr = 0`) for the
symbol `x`, or a system of equations for the symbols `xs`. Other symbols are
parameters. Each solution of a system is a dictionary from the unknowns to
values; unknowns that are left free do not appear. Solutions that make a
denominator vanish are dropped. Warns when a factor could not be solved, in
which case solutions may be missing.

    solve(r*n*(1 - n/K), n)                  # [0, K]
    solve([x + y ~ 1, x - y ~ 0], [x, y])    # [Dict(x => 1/2, y => 1/2)]
"""
solve(eq::Eqn, x::Sym) = solve(eq.lhs - eq.rhs, x)
solve(f::Number, x::Sym) = solve(toterm(f), x)
function solve(f::Term, x::Sym)
    sols = _solve1(f, x)
    return _dedupe([simplify(s) for s in sols])
end

function _dedupe(xs)
    out = Term[]
    for x in xs
        any(y -> isequiv(x, y), out) || push!(out, x)
    end
    return out
end

_eqterm(e::Eqn) = e.lhs - e.rhs
_eqterm(e) = toterm(e)

function _solve1(f::Term, x::Sym)::Vector{Term}
    f = logcombine(f)
    n, d = numerator(f), denominator(f)
    has(n, x) || return Term[]
    _, fs = factor_list(n)
    sols = Term[]
    for (g, k) in fs
        k > 0 && has(g, x) || continue
        append!(sols, _solve_factor(g, x))
    end
    # drop values that make the denominator vanish
    if has(d, x)
        sols = filter(s -> !_iszero_at(d, x, s), sols)
    end
    return sols
end

function _iszero_at(d::Term, x::Sym, s::Term)
    v = _safe(y -> cancel(subs(d, x => y)), s)
    v === nothing && return true
    return iszero(v)
end

# generators of g that depend on x
function _xgens(g::Term, x::Sym)
    gens = _collect_gens!(Gens(), _inner(cancel, g)).list
    return [h for h in gens if has(h, x)]
end

function _solve_factor(g::Term, x::Sym)::Vector{Term}
    xg = _xgens(g, x)
    if xg == Term[x]
        return _solve_poly(g, x)
    elseif length(xg) == 1
        h = xg[1]
        H = Sym(gensym(:H), SymInfo(false, false, nothing, false, nothing, false))
        gh = subs(g, h => H)
        has(gh, x) && (_warn_unsolved(g, x); return Term[])
        vals = _solve_poly(gh, H)
        out = Term[]
        for v in vals
            append!(out, _invert(h, v, x))
        end
        return out
    elseif length(xg) == 2 && x in xg
        # x and x^(1/q): substitute x = y^q
        other = xg[1] == x ? xg[2] : xg[1]
        if other isa Pow && other.base == x && other.exp isa Num && other.exp.val isa Q && numerator(other.exp.val) == 1
            q = Int(denominator(other.exp.val))
            y = Sym(gensym(:y), SymInfo(true, false, Q(0), false, nothing, false))
            gy = cancel(subs(g, Dict{Term,Term}(other => y, x => _pow(y, Num(q)))))
            ys = _solve1(gy, y)
            return Term[_pow(v, Num(q)) for v in ys if !isnegative(v)]
        end
    end
    _warn_unsolved(g, x)
    return Term[]
end

function _solve_poly(g::Term, x::Sym)::Vector{Term}
    cs = polycoeffs(g, x)
    cs === nothing && (_warn_unsolved(g, x); return Term[])
    while length(cs) > 1 && iszero(cs[end])
        pop!(cs)
    end
    d = length(cs) - 1
    d == 0 && return Term[]
    if d == 1
        return Term[cancel(-cs[1] / cs[2])]
    elseif d == 2
        c, b, a = cs
        disc = simplify(b^2 - 4 * a * c)
        sq = simplify(sqrt(disc))
        return Term[cancel((-b - sq) / (2a)), cancel((-b + sq) / (2a))]
    end
    # a polynomial in x^k
    nz = [i - 1 for i in eachindex(cs) if !iszero(cs[i])]
    k = reduce(gcd, nz)
    if k > 1
        Y = Sym(gensym(:Y), SymInfo(false, false, nothing, false, nothing, false))
        gy = _add(Term[_mul((cs[i+1], _pow(Y, Num(div(i, k))))) for i in nz])
        out = Term[]
        for v in _solve_poly(gy, Y)
            r = _pow(v, Num(Q(1) // k))
            push!(out, r)
            iseven(k) && push!(out, -r)
        end
        return out
    end
    # numeric coefficients: give the roots as RootOf (exact) objects
    if all(c -> c isa Num, cs)
        p = _add(Term[_mul((cs[i], _pow(x, Num(i - 1)))) for i in eachindex(cs)])
        return Term[RootOf(p, x, i) for i in 1:d]
    end
    _warn_unsolved(g, x)
    return Term[]
end

# solve h(x) = v for x, where h is a single generator
function _invert(h::Term, v::Term, x::Sym)::Vector{Term}
    if h isa Fn && length(h.args) == 1
        u = h.args[1]
        r = if h.head === :exp
            isnegative(v) || iszero(v) ? nothing : _log(v)
        elseif h.head === :log
            _exp(v)
        elseif h.head === :sin
            _fncall(:asin, Term[v])
        elseif h.head === :cos
            _fncall(:acos, Term[v])
        elseif h.head === :tan
            _fncall(:atan, Term[v])
        else
            nothing
        end
        r === nothing && return Term[]
        return _solve1(u - r, x)
    elseif h isa Pow
        b, e = h.base, h.exp
        if has(b, x) && !has(e, x)
            return _solve1(b - _pow(v, _pow(e, MONE)), x)
        elseif has(e, x) && !has(b, x)
            (isnegative(v) || iszero(v)) && return Term[]
            return _solve1(e - _log(v) / _log(b), x)
        end
    end
    _warn_unsolved(h - v, x)
    return Term[]
end

# ---- systems ------------------------------------------------------------------------

function solve(eqs::AbstractVector, xs::AbstractVector)
    fs = Term[_eqterm(e) for e in eqs]
    vars = Sym[x for x in xs]
    dens = Term[denominator(f) for f in fs]
    nums = Term[numerator(f) for f in fs]
    out = Dict{Sym,Term}[]
    _solve_rec!(out, nums, vars, Dict{Sym,Term}())
    # finish: substitute until values are free of solved unknowns, simplify
    res = Dict{Sym,Term}[]
    for s in out
        t = _close(s)
        t === nothing && continue
        bad = any(d -> has_any(d, vars) && _iszero_at_all(d, t), dens)
        bad && continue
        any(r -> _samesol(r, t), res) || push!(res, t)
    end
    return res
end

has_any(x::Term, vars) = any(v -> has(x, v), vars)

function _iszero_at_all(d::Term, s)
    v = _safe(y -> cancel(subs(y, s)), d)
    return v === nothing || iszero(v)
end

function _close(s)
    t = copy(s)
    for _ in 1:length(t)+1
        changed = false
        for (k, v) in t
            w = subs(v, t)
            if w != v
                t[k] = w
                changed = true
            end
        end
        changed || break
    end
    return Dict{Sym,Term}(k => simplify(v) for (k, v) in t)
end

function _samesol(a, b)
    keys(a) == keys(b) || return false
    return all(k -> isequiv(a[k], b[k]), keys(a))
end

function _solve_rec!(out, eqs, xs, sol)
    live = Term[]
    for e in eqs
        e = numerator(cancel(e))
        iszero(e) && continue
        if !has_any(e, xs)
            # a condition on the parameters alone: generically not satisfied
            # (unless the solved values make it vanish identically)
            return
        end
        push!(live, e)
    end
    if isempty(live) || isempty(xs)
        isempty(live) && push!(out, sol)
        return
    end
    # pick the simplest equation in the fewest unknowns
    score(e) = (count(v -> has(e, v), xs), complexity(e))
    e = live[argmin([score(e) for e in live])]
    _, fs = factor_list(e)
    for (g, k) in fs
        k > 0 || continue
        vs = [v for v in xs if has(g, v)]
        isempty(vs) && continue
        v = _pick_var(g, vs)
        vals = _solve1(g, v)
        for val in vals
            newsol = Dict{Sym,Term}(k2 => subs(s2, v => val) for (k2, s2) in sol)
            newsol[v] = val
            rest = Term[subs(q, v => val) for q in live if q !== e]
            newxs = [w for w in xs if w != v]
            _solve_rec!(out, rest, newxs, newsol)
        end
    end
end

# prefer a variable the factor is linear in, then the lowest degree
function _pick_var(g::Term, vs)
    best, bestscore = vs[1], (typemax(Int), typemax(Int))
    for v in vs
        d = degree(g, v)
        d === nothing && (d = 100)
        sc = (d, complexity(g))
        if sc < bestscore
            best, bestscore = v, sc
        end
    end
    return best
end
