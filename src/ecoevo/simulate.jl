# Numerical solutions (Otto & Day ch. 4): iterating recurrences, integrating
# ODEs, cobweb and bifurcation data. Everything returns plain arrays, for
# tables or for any plotting package.

# the right-hand sides as a compiled function of the state, at numeric parameters
function _numeric_rhs(m::DynModel, parameters)
    d = Dict{Term,Term}(toterm(k) => toterm(v) for (k, v) in parameters)
    F = Term[subs(f, d) for f in m.rhs]
    extra = setdiff(free_symbols(F), m.vars)
    isempty(extra) || throw(ArgumentError("simulate: give values for the parameters $(join(string.(extra), ", "))"))
    f = lambdify(F, m.vars)
    return x -> Float64.(real.(f(x...)))
end

_initial_vector(m::DynModel, ic) = ic isa AbstractDict ? Float64[Float64(ic[v]) for v in m.vars] :
    ic isa Number ? Float64[Float64(ic)] : Float64[Float64(x) for x in ic]

"""
    simulate(m::MapModel, ic, steps; parameters = Dict()) -> (t, u)
    simulate(m::ODEModel, ic, tspan; parameters = Dict(), saveat, reltol, abstol) -> (t, u)

Numerical solution of a model at numeric parameter values (a dictionary from
the parameter symbols to numbers). `ic` is the initial state (a number, a
vector in the order of the variables, or a dictionary). Returns times `t` and a
matrix `u` with one row per time and one column per variable.

A recurrence is iterated `steps` times. An ODE is integrated over `tspan`
(a number `T` for `(0, T)`, or a pair) by the adaptive Dormand–Prince 5(4)
method; `saveat` (default: 201 equally spaced times) gives the output times,
which the integrator steps to exactly.

    @syms n r K
    simulate(recurrence(n => n + r * n * (1 - n / K)), 0.1, 50; parameters = Dict(r => 2.5, K => 1))
    simulate(ode(n => r * n * (1 - n / K)), 0.1, 10; parameters = Dict(r => 1, K => 1))
"""
function simulate(m::MapModel, ic, steps::Integer; parameters = Dict())
    f = _numeric_rhs(m, parameters)
    x = _initial_vector(m, ic)
    u = Matrix{Float64}(undef, steps + 1, length(x))
    u[1, :] = x
    for i in 1:steps
        x = f(x)
        u[i+1, :] = x
    end
    return (t = collect(0:steps), u = u)
end

# Dormand–Prince 5(4) tableau
const _DP_C = (0.0, 1 / 5, 3 / 10, 4 / 5, 8 / 9, 1.0, 1.0)
const _DP_A = ((), (1 / 5,), (3 / 40, 9 / 40), (44 / 45, -56 / 15, 32 / 9),
    (19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729),
    (9017 / 3168, -355 / 33, 46732 / 5247, 49 / 176, -5103 / 18656),
    (35 / 384, 0.0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84))
const _DP_B = (35 / 384, 0.0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84, 0.0)
const _DP_E = (71 / 57600, 0.0, -71 / 16695, 71 / 1920, -17253 / 339200, 22 / 525, -1 / 40)

function simulate(m::ODEModel, ic, tspan; parameters = Dict(), saveat = nothing,
                  reltol::Real = 1e-8, abstol::Real = 1e-10, maxsteps::Integer = 1_000_000)
    f = _numeric_rhs(m, parameters)
    t0, t1 = tspan isa Number ? (0.0, Float64(tspan)) : (Float64(tspan[1]), Float64(tspan[2]))
    ts = saveat === nothing ? collect(range(t0, t1; length = 201)) : Float64.(collect(saveat))
    x = _initial_vector(m, ic)
    u = Matrix{Float64}(undef, length(ts), length(x))
    t = t0
    h = (t1 - t0) / 1000
    k = Vector{Vector{Float64}}(undef, 7)
    nsteps = 0
    for (i, ts_i) in enumerate(ts)
        while t < ts_i - 1e-14 * max(1.0, abs(ts_i))
            h = min(h, ts_i - t)
            k[1] = f(x)
            for s in 2:7
                xs = copy(x)
                for (j, a) in enumerate(_DP_A[s])
                    a == 0 || (xs .+= h * a .* k[j])
                end
                k[s] = f(xs)
            end
            xn = x .+ h .* sum(_DP_B[s] .* k[s] for s in 1:7)
            err = h .* sum(_DP_E[s] .* k[s] for s in 1:7)
            sc = abstol .+ reltol .* max.(abs.(x), abs.(xn))
            e = sqrt(sum(abs2, err ./ sc) / length(x))
            if e <= 1 || h < 1e-14
                t += h
                x = xn
            end
            all(isfinite, x) || throw(ErrorException("simulate: the solution became infinite near t = $t"))
            h *= min(5.0, max(0.2, 0.9 * (e == 0 ? 5.0 : e^(-1 / 5))))
            (nsteps += 1) > maxsteps && throw(ErrorException("simulate: too many steps (stiff problem?)"))
        end
        u[i, :] = x
    end
    return (t = ts, u = u)
end

"""
    cobweb(m::MapModel, ic, steps; parameters = Dict()) -> Matrix

The vertices of the cobweb diagram of a one-variable recurrence: starting at
`(n₀, 0)`, up to the curve `(n₀, n₁)`, across to the diagonal `(n₁, n₁)`, up to
`(n₁, n₂)`, and so on. One row per vertex, columns `n(t)` and `n(t+1)`.
"""
function cobweb(m::MapModel, ic, steps::Integer; parameters = Dict())
    length(m.vars) == 1 || throw(ArgumentError("cobweb: needs a one-variable recurrence"))
    u = simulate(m, ic, steps; parameters = parameters).u[:, 1]
    pts = [u[1] 0.0]
    for i in 1:steps
        pts = vcat(pts, [u[i] u[i+1]], [u[i+1] u[i+1]])
    end
    return pts
end

"""
    bifurcation_data(m::MapModel, μ, values; ic, transient = 500, keep = 100, parameters = Dict())

The long-term states of a recurrence over a range of values of the parameter
`μ` (an orbit or bifurcation diagram, as for the logistic map): for each value,
iterate `transient` steps from `ic`, then record the next `keep` values of the
first variable. Returns `(parameter, state)` vectors of equal length, for a
scatter plot.
"""
function bifurcation_data(m::MapModel, μ::Sym, values; ic, transient::Integer = 500,
                          keep::Integer = 100, parameters = Dict())
    ps, xs = Float64[], Float64[]
    for v in values
        pars = Dict{Any,Any}(parameters)
        pars[μ] = v
        u = simulate(m, ic, transient + keep; parameters = pars).u
        for i in transient+2:transient+keep+1
            push!(ps, Float64(v))
            push!(xs, u[i, 1])
        end
    end
    return (parameter = ps, state = xs)
end
