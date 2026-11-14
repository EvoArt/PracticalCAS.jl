# Recurrence equations (discrete-time models).

_initial(n::Sym) = Sym(Symbol(n.name, "₀"), n.info)

"""
    rsolve(f, n, t; ic = n₀)

Solve the first-order recurrence `n(t+1) = f(n)` for `n(t)`. The initial
value defaults to the symbol `n₀` (named after `n`). Handles:

- linear maps `a n + b` (`n(t) = n̂ + (n₀ - n̂) aᵗ`, or `n₀ + b t` when `a = 1`);
- linear-fractional (Möbius) maps `(a n + b)/(c n + d)`, through `x = 1/n`
  after moving a fixed point to zero; this covers the Beverton–Holt model
  and haploid selection.

    rsolve([f₁, f₂], [x, y], t; ic = [x₀, y₀])

A linear system `n(t+1) = A n + b`, by diagonalisation ([`matpow`](@ref)).
"""
function rsolve(f, n::Sym, t::Sym; ic = nothing)
    f = toterm(f)
    n0 = ic === nothing ? _initial(n) : toterm(ic)
    r = _rsolve1(f, n, t, n0)
    r === nothing && throw(ArgumentError("rsolve: cannot solve n(t+1) = $f"))
    return simplify(r)
end

function _rsolve1(f::Term, n::Sym, t::Sym, n0::Term)
    has(f, t) && return nothing
    cs = polycoeffs(f, n)
    if cs !== nothing && length(cs) <= 2
        length(cs) == 1 && return cs[1]   # constant map
        b, a = cs
        iszero(simplify(a - 1)) && return n0 + b * t
        ns = simplify(b / (1 - a))
        return ns + (n0 - ns) * _pow(a, t)
    end
    g = cancel(f)
    num, den = numerator(g), denominator(g)
    nc, dc = polycoeffs(num, n), polycoeffs(den, n)
    (nc === nothing || dc === nothing || length(nc) > 2 || length(dc) != 2) && return nothing
    b = nc[1]
    a = length(nc) == 2 ? nc[2] : ZERO
    d, c = dc
    if iszero(b)
        # x = 1/n: x(t+1) = c/a + (d/a) x
        x = Sym(gensym(:x), _REAL)
        xs = _rsolve1(c / a + (d / a) * x, x, t, _pow(n0, MONE))
        xs === nothing && return nothing
        return cancel(_pow(xs, MONE))
    end
    # move a fixed point to zero: n = m + n̂
    fps = solve(n * (c * n + d) - (a * n + b), n)
    isempty(fps) && return nothing
    ns = fps[1]
    m = Sym(gensym(:m), _REAL)
    fm = cancel(subs(f, n => m + ns) - ns)
    ms = _rsolve1(fm, m, t, n0 - ns)
    ms === nothing && return nothing
    return ms + ns
end

function rsolve(F::AbstractVector, ns::AbstractVector, t::Sym; ic = nothing)
    F = Term[toterm(f) for f in F]
    A = jacobian(F, ns)
    any(a -> has_any(a, ns) || has(a, t), A) && throw(ArgumentError("rsolve: only linear systems with constant coefficients are supported"))
    zero_ = Dict{Term,Term}(v => ZERO for v in ns)
    b = Term[simplify(subs(f, zero_)) for f in F]
    n0 = ic === nothing ? Term[_initial(v) for v in ns] : Term[toterm(v) for v in ic]
    k = length(ns)
    IA = Term[(i == j ? ONE : ZERO) - A[i, j] for i in 1:k, j in 1:k]
    nstar = all(iszero, b) ? _tzeros(k) : IA \ b
    P = matpow(A, t)
    return Term[simplify(x) for x in nstar + P * (n0 - nstar)]
end
