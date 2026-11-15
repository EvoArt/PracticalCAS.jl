# Dynamical models: equilibria, Jacobians, local stability.

abstract type DynModel end

"""
    ode(n => rhs, ...)

A continuous-time model `dn/dt = rhs` in one or more variables.

    @syms n::nonneg r::positive K::positive
    m = ode(n => r*n*(1 - n/K))
    equilibria(m)            # [Dict(n => 0), Dict(n => K)]
    stability(m)             # each equilibrium with eigenvalues and verdict
"""
struct ODEModel <: DynModel
    vars::Vector{Sym}
    rhs::Vector{Term}
end
ode(ps::Pair...) = ODEModel(Sym[p.first for p in ps], Term[toterm(p.second) for p in ps])

"""
    recurrence(n => next, ...)

A discrete-time model `n(t+1) = next` in one or more variables.

    m = recurrence(n => R*n/(1 + (R - 1)*n/K))
"""
struct MapModel <: DynModel
    vars::Vector{Sym}
    rhs::Vector{Term}
end
recurrence(ps::Pair...) = MapModel(Sym[p.first for p in ps], Term[toterm(p.second) for p in ps])

function Base.show(io::IO, m::ODEModel)
    println(io, "Continuous-time model:")
    for (v, f) in zip(m.vars, m.rhs)
        println(io, "  d", v, "/dt = ", f)
    end
end
function Base.show(io::IO, m::MapModel)
    println(io, "Discrete-time model:")
    for (v, f) in zip(m.vars, m.rhs)
        println(io, "  ", v, "(t+1) = ", f)
    end
end

_iscont(::ODEModel) = true
_iscont(::MapModel) = false

"""
    equilibria(m) -> Vector{Dict}

The equilibria of a model: where the rates are zero (continuous time) or where
`n(t+1) = n(t)` (discrete time).
"""
function equilibria(m::DynModel)
    eqs = _iscont(m) ? m.rhs : Term[f - v for (f, v) in zip(m.rhs, m.vars)]
    sols = solve(eqs, m.vars)
    # unknowns left free are free parameters of a line of equilibria; keep them
    return [Dict{Sym,Term}(v => get(s, v, v) for v in m.vars) for s in sols]
end

jacobian(m::DynModel) = jacobian(m.rhs, m.vars)
jacobian(m::DynModel, point::AbstractDict) = Term[simplify(x) for x in subs(jacobian(m), _pointdict(point))]
_pointdict(p::AbstractDict) = Dict{Term,Term}(toterm(k) => toterm(v) for (k, v) in p)

"""
    Stability

The local stability of an equilibrium: the point, the Jacobian there, its
eigenvalues (when they could be found), the condition for stability
(Routh–Hurwitz in continuous time, Jury in discrete time, simplified under the
assumptions) and the verdict `:stable`, `:unstable`, `:depends`, or
`:neutral` when the eigenvalues sit on the stability boundary (purely imaginary
in continuous time, modulus 1 in discrete time) so that the linearisation does
not decide.
"""
struct Stability
    point::Dict{Sym,Term}
    jacobian::Matrix{Term}
    eigenvalues::Vector{Term}
    condition::CondLike
    verdict::Symbol
    continuous::Bool
end

function Base.show(io::IO, s::Stability)
    pt = join(("$(k) = $(v)" for (k, v) in sort(collect(s.point); by = p -> String(p.first.name))), ", ")
    println(io, "Equilibrium ", pt)
    println(io, "  eigenvalues: ", isempty(s.eigenvalues) ? "(not found)" : join(string.(s.eigenvalues), ", "))
    println(io, "  stable if:   ", s.condition)
    print(io, "  verdict:     ", s.verdict)
end

"""
    stability(m, point) -> Stability
    stability(m) -> Vector{Stability}

Local stability of an equilibrium of a continuous- or discrete-time model (or
of all of them). In continuous time an equilibrium is stable when all
eigenvalues of the Jacobian have negative real part, in discrete time when
they all lie inside the unit circle; the condition is computed from the
characteristic polynomial, so it is exact even when the eigenvalues have no
closed form.
"""
function stability(m::DynModel, point::AbstractDict)
    J = jacobian(m, point)
    vals = _safe(_eigvals, J)
    vals === nothing && (vals = Term[])
    # with all eigenvalues known and real, "each one < 0" (or inside (-1, 1)) is
    # exact and reads better than the Routh–Hurwitz / Jury conditions
    if length(vals) == size(J, 1) && all(v -> (sign_of(v) & CPX) == 0, vals)
        cs = Any[]
        for λ in _dedupe(vals)
            if _iscont(m)
                push!(cs, simplify(Rel(:<, λ, ZERO)))
            else
                push!(cs, simplify(Rel(:<, λ, ONE)))
                push!(cs, simplify(Rel(:>, λ, MONE)))
            end
        end
        cond = _and(cs)
    else
        cond = _iscont(m) ? routh_hurwitz(J) : jury(J)
    end
    v = decide_verdict(cond)
    v === :unstable && _borderline(vals, _iscont(m)) && (v = :neutral)
    pd = Dict{Sym,Term}(k => toterm(x) for (k, x) in point)
    return Stability(pd, J, vals, cond, v, _iscont(m))
end
stability(m::DynModel) = [stability(m, e) for e in equilibria(m)]

# no eigenvalue is known to be unstable but some sit on the boundary (real part
# 0 in continuous time, modulus 1 in discrete time): linearisation is inconclusive
function _borderline(vals, cont::Bool)
    isempty(vals) && return false
    onb = false
    for λ in vals
        if cont
            re = _safe(z -> simplify(_reim(z)[1]), λ)
            re === nothing && return false
            sre = sign_of(re)
            (sre & (POS | CPX)) != 0 && return false
            sre == ZER && (onb = true)
        else
            re, im_ = _reim(λ)
            m2 = simplify(re^2 + im_^2 - 1)
            sm = sign_of(m2)
            (sm & (POS | CPX)) != 0 && return false
            sm == ZER && (onb = true)
        end
    end
    return onb
end

decide_verdict(c) = (d = decide(c); d === true ? :stable : d === false ? :unstable : :depends)

"""
    nullclines(m, i, x)

The solutions for `x` of `rhs[i] = 0` (continuous time) or `next[i] = vars[i]`
(discrete time): the `i`-th nullcline as curves `x = …`.
"""
function nullclines(m::DynModel, i::Integer, x::Sym)
    f = _iscont(m) ? m.rhs[i] : m.rhs[i] - m.vars[i]
    return solve(f, x)
end

"""
    linearize(m, point)

The linearised dynamics about an equilibrium: the Jacobian there (for
continuous time `d(δn)/dt = J δn`, for discrete time `δn(t+1) = J δn(t)`).
"""
linearize(m::DynModel, point::AbstractDict) = jacobian(m, point)

"""
    dsolve(m::ODEModel; ic) / rsolve(m::MapModel; ic)

Solve a one-variable model (or a linear multi-variable one) in the symbol `t`.
"""
function dsolve(m::ODEModel, t::Sym; ic = nothing)
    length(m.vars) == 1 && return dsolve(m.rhs[1], m.vars[1], t; ic = ic)
    return dsolve(m.rhs, m.vars, t; ic = ic)
end
function rsolve(m::MapModel, t::Sym; ic = nothing)
    length(m.vars) == 1 && return rsolve(m.rhs[1], m.vars[1], t; ic = ic)
    return rsolve(m.rhs, m.vars, t; ic = ic)
end

"""
    invasion_fitness(rhs, x, point)

The per-capita growth of a rare type `x` whose dynamics are `rhs` (a rate,
or a next-generation value): `∂rhs/∂x` at `x = 0` and the residents at
`point`. Its sign relative to 0 (continuous time) or 1 (discrete time)
decides invasion.
"""
function invasion_fitness(rhs, x::Sym, point::AbstractDict = Dict{Sym,Term}())
    d = _pointdict(point)
    d[x] = ZERO
    return simplify(subs(diff(toterm(rhs), x), d))
end

"""
    quasi_steady_state(m::ODEModel, fast) -> Vector{ODEModel}

Separation of time scales: set the rates of the fast variables `fast` (a symbol
or a vector) to zero, solve for them, and substitute into the equations of the
slow variables. Returns one reduced model for each branch of the solution
(often just one), whose variables are the slow ones.

    @syms S::nonneg C::nonneg k₁::positive k₋::positive k₂::positive E₀::positive
    # enzyme kinetics: the complex C is fast; dS/dt = -k₂E₀S/(K + S) with K = (k₋ + k₂)/k₁
    quasi_steady_state(ode(S => -k₁*S*(E₀ - C) + k₋*C, C => k₁*S*(E₀ - C) - (k₋ + k₂)*C), C)

"""
function quasi_steady_state(m::ODEModel, fast)
    fast = fast isa Sym ? Sym[fast] : Sym[v for v in fast]
    idx = [findfirst(==(v), m.vars) for v in fast]
    any(isnothing, idx) && throw(ArgumentError("quasi_steady_state: the fast variables must be variables of the model"))
    slow = [i for i in eachindex(m.vars) if !(i in idx)]
    isempty(slow) && throw(ArgumentError("quasi_steady_state: no slow variables left"))
    sols = solve(Term[m.rhs[i] for i in idx], fast)
    out = ODEModel[]
    for s in sols
        all(v -> haskey(s, v), fast) || continue
        d = _pointdict(s)
        push!(out, ODEModel(Sym[m.vars[i] for i in slow], Term[simplify(subs(m.rhs[i], d)) for i in slow]))
    end
    return out
end
