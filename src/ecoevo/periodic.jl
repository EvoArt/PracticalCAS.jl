# Periodic behaviour (Otto & Day ch. 11): cycles of discrete-time models, Hopf
# bifurcations, and constants of motion of continuous-time models.

"""
    Cycle

A `k`-cycle of a discrete-time model: the points visited in order, the
multiplier matrix (the product of the Jacobians around the cycle, the Jacobian
of the `k`-fold map), its eigenvalues, the condition for stability (all
eigenvalues inside the unit circle) and the verdict.
"""
struct Cycle
    points::Vector{Dict{Sym,Term}}
    multiplier::Matrix{Term}
    eigenvalues::Vector{Term}
    condition::CondLike
    verdict::Symbol
end

function Base.show(io::IO, c::Cycle)
    pts = [join(("$(k) = $(v)" for (k, v) in sort(collect(p); by = q -> String(q.first.name))), ", ") for p in c.points]
    println(io, length(c.points), "-cycle: ", join(("(" * s * ")" for s in pts), " → "))
    println(io, "  multiplier: ", size(c.multiplier) == (1, 1) ? string(c.multiplier[1, 1]) : string(c.multiplier))
    println(io, "  stable if:  ", c.condition)
    print(io, "  verdict:    ", c.verdict)
end

_compose(m::MapModel, k::Int) = begin
    F = copy(m.rhs)
    for _ in 2:k
        d = Dict{Term,Term}(v => f for (v, f) in zip(m.vars, F))
        F = Term[subs(f, d) for f in m.rhs]
    end
    F
end

_divisors(k::Int) = [d for d in 1:k-1 if k % d == 0]

"""
    cycles(m::MapModel, k = 2) -> Vector{Cycle}

The cycles of exact period `k` of a discrete-time model: solutions of
`Fᵏ(n) = n` that are not points of lower period, grouped into orbits, each
with its stability (the product of the Jacobians around the cycle, so the
multiplier `f'(n₁) f'(n₂)` for a 2-cycle of a one-variable map).

    @syms n r::positive
    c = only(cycles(recurrence(n => r * n * (1 - n)), 2))
    c.condition        # 3 < r < 1 + √6
"""
function cycles(m::MapModel, k::Integer = 2)
    k >= 2 || throw(ArgumentError("cycles: the period must be at least 2"))
    Fk = _compose(m, k)
    pts = Dict{Sym,Term}[]
    if length(m.vars) == 1
        n = m.vars[1]
        g = numerator(cancel(Fk[1] - n))
        for d in _divisors(k)
            Pd = numerator(cancel(_compose(m, d)[1] - n))
            g = numerator(cancel(g / Pd))
        end
        for x in solve(g, n)
            push!(pts, Dict{Sym,Term}(n => x))
        end
    else
        sols = solve(Term[f - v for (f, v) in zip(Fk, m.vars)], m.vars)
        lower = [_compose(m, d) for d in _divisors(k)]
        for s in sols
            length(s) == length(m.vars) || continue
            d = _pointdict(s)
            any(G -> all(isequiv(subs(G[i], d), s[m.vars[i]]) for i in eachindex(m.vars)), lower) && continue
            push!(pts, Dict{Sym,Term}(v => s[v] for v in m.vars))
        end
    end
    # group the points into orbits
    used = falses(length(pts))
    out = Cycle[]
    J = jacobian(m)
    for i in eachindex(pts)
        used[i] && continue
        orbit = [pts[i]]
        used[i] = true
        cur = pts[i]
        for _ in 2:k
            d = _pointdict(cur)
            nxt = Dict{Sym,Term}(v => simplify(subs(f, d)) for (v, f) in zip(m.vars, m.rhs))
            j = findfirst(jj -> !used[jj] && all(isequiv(pts[jj][v], nxt[v]) for v in m.vars), eachindex(pts))
            j === nothing && break
            used[j] = true
            push!(orbit, pts[j])
            cur = pts[j]
        end
        length(orbit) == k || continue
        push!(out, _cycle_stability(J, orbit))
    end
    return out
end

function _cycle_stability(J, orbit)
    n = size(J, 1)
    M = Term[i == j ? ONE : ZERO for i in 1:n, j in 1:n]
    for p in orbit
        M = Term[x for x in subs(J, _pointdict(p))] * M
    end
    M = Term[simplify(expand(x)) for x in M]
    vals = n == 1 ? Term[M[1, 1]] : something(_safe(_eigvals, M), Term[])
    cond = if n == 1
        _and(Any[simplify(Rel(:<, M[1, 1], ONE)), simplify(Rel(:>, M[1, 1], MONE))])
    else
        jury(M)
    end
    return Cycle(orbit, M, vals, cond, decide_verdict(cond))
end

"""
    hopf(m, point) -> (condition, frequency)

The condition for a Hopf bifurcation at an equilibrium of a continuous-time
model: a pair of eigenvalues on the imaginary axis with the others in the left
half-plane (for two variables, `tr J = 0` with `det J > 0`; in general the
Hurwitz determinant `Δₙ₋₁ = 0` with the lower ones and `aₙ` positive), and the
angular frequency `ω` of the oscillations born there (`√det J` for two
variables; `nothing` above three). For a discrete-time model with two
variables, the Neimark–Sacker condition `det J = 1` with `|tr J| < 2`.

    hopf(m, point, μ) -> Vector

The values of the parameter `μ` that satisfy the equality part of the
condition.
"""
function hopf(m::DynModel, point::AbstractDict)
    J = jacobian(m, point)
    n = size(J, 1)
    n >= 2 || throw(ArgumentError("hopf: needs at least two variables"))
    if !_iscont(m)
        n == 2 || throw(ArgumentError("hopf: the Neimark–Sacker condition is implemented for two variables"))
        T, D = simplify(tr(J)), simplify(det(J))
        c = _and(Any[eq(D, 1), simplify(Rel(:<, T, TWO)), simplify(Rel(:>, T, -TWO))])
        return (condition = c, frequency = _fncall(:acos, Term[simplify(T / 2)]), equality = D - 1)
    end
    b = charcoeffs(J)
    Δ = simplify(_hurwitz_det(b, n - 1))
    conds = Any[eq(Δ, 0), simplify(Rel(:>, b[end], ZERO))]
    for i in 1:n-2
        push!(conds, simplify(Rel(:>, simplify(_hurwitz_det(b, i)), ZERO)))
    end
    ω = n <= 3 ? simplify(_pow(b[3], HALF)) : nothing
    return (condition = _and(conds), frequency = ω, equality = Δ)
end
hopf(m::DynModel, point::AbstractDict, μ::Sym) = solve(hopf(m, point).equality, μ)

"""
    conserved_quantity(m::ODEModel) -> Term

A constant of motion `H(x, y)` of a two-variable model whose trajectories
satisfy a separable equation `dy/dx = a(x) b(y)`:
`H = ∫ dy/b(y) - ∫ a(x) dx`, checked by `dH/dt = 0`. For Lotka–Volterra
predator–prey dynamics this shows the orbits are closed. Throws if no such
quantity is found.
"""
function conserved_quantity(m::ODEModel)
    length(m.vars) == 2 || throw(ArgumentError("conserved_quantity: needs two variables"))
    x, y = m.vars
    f, g = m.rhs
    ratio = cancel(g / f)
    c, fs = factor_list(ratio)
    ax, by = Term[toterm(c)], Term[]
    for (h, k) in fs
        hx, hy = has(h, x), has(h, y)
        hx && hy && throw(ArgumentError("conserved_quantity: dy/dx = $ratio is not separable"))
        push!(hy ? by : ax, _pow(h, Num(k)))
    end
    H = integrate(simplify(_pow(_mul(by), MONE)), y) - integrate(simplify(_mul(ax)), x)
    _hasintegral(H) && throw(ArgumentError("conserved_quantity: could not integrate"))
    H = simplify(H)
    isconserved(H, m) || throw(ArgumentError("conserved_quantity: the candidate $H is not conserved"))
    return H
end

"""
    isconserved(H, m) -> Bool

Whether `H` is a constant of motion of the continuous-time model `m`:
`dH/dt = Σ ∂H/∂xᵢ ⋅ dxᵢ/dt = 0`.
"""
isconserved(H, m::ODEModel) = iszero(simplify(_add(Term[diff(toterm(H), v) * f for (v, f) in zip(m.vars, m.rhs)])))
