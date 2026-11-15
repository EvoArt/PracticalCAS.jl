# Symbolic graph extraction and numerical phase portraits, independent of drawing.

"An influence `from → to`, its symbolic derivative, and sign (:positive, :negative, :zero, :unknown)."
struct DynamicsEdge
    from::Sym
    to::Sym
    derivative::Term
    sign::Symbol
end

"Nodes, signed influence edges, and positions returned by `dynamics_graph`."
struct DynamicsGraph
    nodes::Vector{Sym}
    edges::Vector{DynamicsEdge}
    positions::Vector{NTuple{2,Float64}}
end

function _checkmodel(m)
    n = length(m.vars)
    n > 0 && n == length(m.rhs) || throw(ArgumentError("model needs one equation per variable"))
    length(unique(m.vars)) == n || throw(ArgumentError("model variables must be distinct"))
end

_plotdict(p::AbstractDict) = _pointdict(p)
_plotdict(p) = Dict{Term,Term}(toterm(k) => toterm(v) for (k, v) in p)

"""
    dynamics_graph(model; parameters=Dict(), point=Dict(), selfloops=true, positions=nothing)

Build an influence graph from an `ode` or `recurrence`: `x → y` means that
`∂rhs_y/∂x` is not identically zero. Signs use symbolic assumptions, optionally
after substituting parameters and a state `point`. An undecidable sign is
`:unknown`; a structural edge that vanishes at `point` has sign `:zero`.
This is not a compartment-flow or causal graph. For maps the
derivative is of the next state, not the increment. Cycles and self-loops are
supported. `positions` may be a dictionary from variables to `(x, y)`.
"""
function dynamics_graph(m::DynModel; parameters=Dict(), point=Dict(), selfloops=true, positions=nothing)
    _checkmodel(m)
    p, q = _plotdict(parameters), _plotdict(point)
    any(v -> haskey(p, v), m.vars) && throw(ArgumentError("put state values in point, not parameters"))
    edges = DynamicsEdge[]
    for (i, rhs) in enumerate(m.rhs), (j, v) in enumerate(m.vars)
        !selfloops && i == j && continue
        d = simplify(subs(diff(rhs, v), p))
        iszero(d) && continue
        at = simplify(subs(d, q))
        # Retain a structural edge even if its derivative vanishes at this point.
        s = iszero(at) ? :zero : ispositive(at) ? :positive : isnegative(at) ? :negative : :unknown
        push!(edges, DynamicsEdge(v, m.vars[i], d, s))
    end
    n = length(m.vars)
    pos = positions === nothing ? _ringlayout(n, first(_node_size(m.vars))) :
        [(Float64(positions[v][1]), Float64(positions[v][2])) for v in m.vars]
    all(p -> all(isfinite, p), pos) || throw(ArgumentError("positions must be finite"))
    length(unique(pos)) == n || throw(ArgumentError("node positions must be distinct"))
    return DynamicsGraph(copy(m.vars), edges, pos)
end

# Node geometry shared by the layout and the drawing, in layout units: nodes
# are circles of radius 0.3 (as in PracticalProbability's diagrams), widened
# to ellipses when a label would not fit, all nodes of a graph the same size.
const _NODE_R = 0.3
const _NODE_FONT = 0.24

# half-width and half-height of the nodes for `labels`
function _node_size(labels)
    w = 0.5 * 0.55 * _NODE_FONT * maximum(x -> length(string(x)), labels; init=1) + 0.08
    return w <= 1.2_NODE_R ? (max(w, _NODE_R), max(w, _NODE_R)) : (w, _NODE_R)
end

# n nodes on a circle, the first at the top (two side by side, four in a
# square), clockwise, far enough apart for nodes of half-width rx.
function _ringlayout(n, rx)
    n == 1 && return [(0.0, 0.0)]
    # a triangle needs room inside for the labels of three inner curves
    radius = max(n == 3 ? 1.45 : 1.0, n/6, (2rx + 1.0)/(2sinpi(1/n)))
    offset = 0.5 + (iseven(n) ? 1/n : 0.0)
    return [(radius*cospi(offset - 2(i - 1)/n), radius*sinpi(offset - 2(i - 1)/n)) for i in 1:n]
end

"""
Numerical data for a phase portrait. `states` are model coordinates (`ternary_data`
stores all three frequencies); `points` and `vectors` are Cartesian drawing
coordinates. `trajectories` contains projected paths from a fixed-step RK4
integration. `bounds`, `labels`, and `ternary` describe the drawing domain.
`equilibria` holds the marked equilibria as `(state, point, stability)` with
`stability` one of `:stable`, `:unstable` or `:neutral` (from the eigenvalues
of a numerical Jacobian; on the simplex, of the two independent frequencies).
"""
struct PhaseData
    states::Vector{Vector{Float64}}
    points::Vector{NTuple{2,Float64}}
    vectors::Vector{NTuple{2,Float64}}
    trajectories::Vector{Vector{NTuple{2,Float64}}}
    bounds::NTuple{4,Float64}
    labels::Vector{String}
    ternary::Bool
    equilibria::Vector{@NamedTuple{state::Vector{Float64}, point::NTuple{2,Float64}, stability::Symbol}}
end

# Equilibria to mark on a portrait. `g` is the field in the two independent
# coordinates (`vars`, rates `rhs` after substituting parameters); `full` maps
# them to a model state. `spec` is `nothing`, `:auto` (solve rhs = 0) or a
# vector of states.
function _marks(spec, g, vars, rhs, full, inside, project)
    T = @NamedTuple{state::Vector{Float64}, point::NTuple{2,Float64}, stability::Symbol}
    marks = T[]
    spec === nothing && return marks
    states = Vector{Float64}[]
    if spec === :auto
        for s in equilibria(ode((v => r for (v, r) in zip(vars, rhs))...))
            vals = [evalf(s[v]) for v in vars]
            all(x -> x isa Real && isfinite(x), vals) || continue   # complex, or a line of equilibria
            u = full(Float64.(vals))
            inside(u) && !any(w -> maximum(abs, w - u) < 1e-9, states) && push!(states, u)
        end
    elseif spec isa Symbol
        throw(ArgumentError("equilibria must be nothing, :auto or a vector of states"))
    else
        for p in spec
            u = Float64.(collect(p))
            inside(u) || throw(ArgumentError("equilibrium $p is outside the plotting domain"))
            push!(states, u)
        end
    end
    for u in states
        w = u[1:2]
        h = 1e-6 * max(1.0, maximum(abs, w))
        J = hcat([(g(w + h*e) - g(w - h*e)) / 2h for e in ([1.0, 0.0], [0.0, 1.0])]...)
        λ = maximum(real, eigvals(J))
        tol = 1e-6 * max(1.0, maximum(abs, J))
        push!(marks, (state=u, point=project(u), stability=λ < -tol ? :stable : λ > tol ? :unstable : :neutral))
    end
    return marks
end

function _field(m, parameters)
    _checkmodel(m)
    p = _plotdict(parameters)
    any(v -> haskey(p, v), m.vars) && throw(ArgumentError("parameters cannot replace state variables"))
    rhs = simplify.(subs(m.rhs, p))
    missing = setdiff(free_symbols(rhs), m.vars)
    isempty(missing) || throw(ArgumentError("supply numeric parameters for: $(join(string.(missing), ", "))"))
    f = lambdify(rhs, m.vars)
    function field(u)
        v = f(u...)
        all(x -> x isa Real && isfinite(x), v) ||
            throw(ArgumentError("vector field must be finite and real at $u"))
        return Float64.(v)
    end
    return field, rhs
end

function _resolution(n)
    n isa Integer && n >= 2 || throw(ArgumentError("resolution must be an integer ≥ 2"))
    return n
end

function _interval(x)
    length(x) == 2 || throw(ArgumentError("limits must be (lower, upper)"))
    a, b = Float64.(x)
    isfinite(a) && isfinite(b) && a < b || throw(ArgumentError("limits must be finite and increasing"))
    return a, b
end

function _paths(f, initials, inside, project; dt, steps)
    dt isa Real && isfinite(dt) && dt > 0 || throw(ArgumentError("dt must be finite and positive"))
    steps isa Integer && steps >= 0 || throw(ArgumentError("steps must be a nonnegative integer"))
    paths = Vector{NTuple{2,Float64}}[]
    for initial in initials
        u = Float64.(collect(initial))
        inside(u) || throw(ArgumentError("initial state $initial is outside the plotting domain"))
        path = NTuple{2,Float64}[project(u)]
        for _ in 1:steps
            k1 = f(u)
            u2 = u + (dt/2)*k1
            inside(u2) || break
            k2 = f(u2)
            u3 = u + (dt/2)*k2
            inside(u3) || break
            k3 = f(u3)
            u4 = u + dt*k3
            inside(u4) || break
            k4 = f(u4)
            next = u + (dt/6)*(k1 + 2k2 + 2k3 + k4)
            inside(next) || break
            push!(path, project(next))
            u = next
        end
        push!(paths, path)
    end
    return paths
end

"""
    phase_data(model; xlim=(0, 1), ylim=(0, 1), parameters=Dict(),
               resolution=20, initials=[], dt=0.02, steps=500, equilibria=nothing)

Sample a two-variable autonomous ODE's vector field and optional trajectories.
All remaining parameters must be numeric. Trajectories use fixed-step RK4 and
stop on reaching the plotting boundary; reduce `dt` to check numerical accuracy.
`equilibria = :auto` solves for the equilibria in the window and classifies
each from its Jacobian; a vector of states marks given points instead.
"""
function phase_data(m::ODEModel; xlim=(0, 1), ylim=(0, 1), parameters=Dict(),
                    resolution=20, initials=[], dt=0.02, steps=500, equilibria=nothing)
    length(m.vars) == 2 || throw(ArgumentError("phase_data needs two state variables"))
    n = _resolution(resolution)
    xmin, xmax = _interval(xlim)
    ymin, ymax = _interval(ylim)
    f, rhs = _field(m, parameters)
    states = [[x, y] for x in range(xmin, xmax; length=n) for y in range(ymin, ymax; length=n)]
    project(u) = (u[1], u[2])
    inside(u) = length(u) == 2 && all(isfinite, u) && xmin <= u[1] <= xmax && ymin <= u[2] <= ymax
    paths = _paths(f, initials, inside, project; dt, steps)
    marks = _marks(equilibria, f, m.vars, rhs, identity, inside, project)
    return PhaseData(states, project.(states), [project(f(u)) for u in states], paths,
                     (xmin, xmax, ymin, ymax), string.(m.vars), false, marks)
end

const _TRIHEIGHT = sqrt(3.0)/2
_tripoint(u) = (u[2] + u[3]/2, _TRIHEIGHT*u[3])

"""
    ternary_data(game::MatrixGame; kwargs...)
    ternary_data(model::ODEModel; parameters=Dict(), resolution=18, labels=nothing,
                 initials=[], dt=0.02, steps=500, equilibria=nothing)

Sample dynamics on the three-frequency simplex. A game must have three
strategies. A model may contain two independent frequencies (`x₃ = 1-x₁-x₂`)
or three rates whose sum vanishes on the simplex. Vertices 1, 2, 3 are left,
right, top. `initials` always contains triples summing to one. Samples are
checked for outward flow at the boundary; this is a numerical check, not a
proof of simplex invariance. Trajectories stop if an RK4 step leaves the simplex
(no clipping or renormalisation). These are phase portraits at fixed parameters,
not parameter-space bifurcation diagrams. `equilibria` is as for
[`phase_data`](@ref), with states given as triples.
"""
function ternary_data(m::ODEModel; parameters=Dict(), resolution=18, labels=nothing,
                      initials=[], dt=0.02, steps=500, equilibria=nothing)
    n = _resolution(resolution)
    dim = length(m.vars)
    dim in (2, 3) || throw(ArgumentError("ternary_data needs two independent or three conserved frequencies"))
    field, rhs = _field(m, parameters)
    if dim == 3
        total = simplify(subs(sum(rhs), m.vars[3] => 1-m.vars[1]-m.vars[2]))
        iszero(total) || throw(ArgumentError("the three frequency rates must sum to zero on the simplex"))
    end
    function f(u)
        v = field(u[1:dim])
        # Use the independent rates to keep the numerical field tangent.
        return [v[1], v[2], -v[1]-v[2]]
    end
    labs = labels === nothing ? (dim == 3 ? string.(m.vars) : [string.(m.vars); "1 - $(m.vars[1]) - $(m.vars[2])"]) : string.(collect(labels))
    length(labs) == 3 || throw(ArgumentError("ternary labels must have length three"))
    states = [[i/n, j/n, (n-i-j)/n] for i in 0:n for j in 0:n-i]
    velocities = [f(u) for u in states]
    for (u, v) in zip(states, velocities), k in 1:3
        u[k] == 0 && v[k] < -1e-10*maximum(abs, v) &&
            throw(ArgumentError("frequency $k has outward flow at $u; the simplex is not invariant"))
    end
    inside(u) = length(u) == 3 && all(isfinite, u) && minimum(u) >= -1e-12 &&
                maximum(u) <= 1+1e-12 && abs(sum(u)-1) <= 1e-10
    paths = _paths(f, initials, inside, _tripoint; dt, steps)
    # the two independent frequencies, with x₃ = 1 - x₁ - x₂
    v1, v2 = m.vars[1], m.vars[2]
    rhs2 = dim == 3 ? [simplify(subs(r, m.vars[3] => 1-v1-v2)) for r in rhs[1:2]] : rhs
    g(w) = f([w[1], w[2], 1-w[1]-w[2]])[1:2]
    marks = _marks(equilibria, g, [v1, v2], rhs2, w -> [w[1], w[2], 1-w[1]-w[2]], inside, _tripoint)
    return PhaseData(states, _tripoint.(states), _tripoint.(velocities), paths,
                     (0.0, 1.0, 0.0, _TRIHEIGHT), labs, true, marks)
end

function ternary_data(g::MatrixGame; labels=g.strategies, kwargs...)
    size(g.A) == (3, 3) || throw(ArgumentError("ternary_data needs a three-strategy game"))
    return ternary_data(replicator(g); labels, kwargs...)
end
