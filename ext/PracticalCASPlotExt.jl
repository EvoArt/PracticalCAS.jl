module PracticalCASPlotExt

using PracticalCAS
import PracticalCAS: dynamicsplot, dynamicsplot!, phaseplot, phaseplot!, ternaryplot, ternaryplot!
import PracticalBayesPlot as PBP

# The look of PracticalProbability's diagrams: Wong's colour-blind-safe
# palette, black outlines 1.6 wide, and diagram sizes in data units so the
# TikZ and CeTZ outputs keep their proportions.
const _BLUE = "#0072B2"
const _VERMILION = "#D55E00"
const _GREY = "#7F7F7F"
const _FIELD = "#A0A0A0"        # direction-field arrows
const _LIGHT = "#E4E4E4"        # ternary grid
const _CYCLE = ("#0072B2", "#E69F00", "#009E73", "#CC79A7", "#56B4E9", "#D55E00")
const _STROKE = 1.6
const _HEAD = (0.16, 0.065)     # arrowhead length and half-width, layout units
const _NODE_FONT = PracticalCAS._NODE_FONT

# ---------------------------------------------------------------------------
# geometry
# ---------------------------------------------------------------------------

_unit(v) = (l = hypot(v[1], v[2]); (v[1]/l, v[2]/l))
# distance from the centre of an ellipse with half-axes (rx, ry) to its edge along u
_reach((rx, ry), u) = 1/sqrt((u[1]/rx)^2 + (u[2]/ry)^2)
_isinside(p, c, (rx, ry)) = ((p[1]-c[1])/rx)^2 + ((p[2]-c[2])/ry)^2 < 1
_ellipse(c, (rx, ry); n=72) = [(c[1] + rx*cospi(2t/n), c[2] + ry*sinpi(2t/n)) for t in 0:n-1]
# half the extent of a w × h box along the unit vector n
_extent(n, (w, h)) = abs(n[1])*w/2 + abs(n[2])*h/2
# approximate size of a label of height fs
_labelsize(s, fs) = (0.55fs*length(s) + 0.04, fs)

function _bisect(pin, pout, c, size)
    for _ in 1:30
        m = (pin .+ pout) ./ 2
        _isinside(m, c, size) ? (pin = m) : (pout = m)
    end
    return pout
end

_qbezier(p0, c, p1; n=32) = [(1-t)^2 .* p0 .+ 2t*(1-t) .* c .+ t^2 .* p1 for t in range(0, 1; length=n)]

# Split a path ending at an arrow tip into the line (stopping at the head's
# base, so it does not poke through the tip) and the head polygon.
function _withhead(path, (len, hw))
    tip = path[end]
    k = length(path) - 1
    while k > 1 && hypot((path[k] .- tip)...) < len
        k -= 1
    end
    u = _unit(tip .- path[k])
    base = tip .- len .* u
    head = [tip, (base[1] - hw*u[2], base[2] + hw*u[1]), (base[1] + hw*u[2], base[2] - hw*u[1])]
    return [path[1:k]; [base]], head
end

# A self-loop on the node at a (half-axes `size`), on the side u, as the arc
# of a small circle outside the node; it ends on the outline.
function _loop(a, size, u; ρ=0.22)
    c = a .+ (_reach(size, u) + 0.1) .* u
    φ0 = atan(-u[2], -u[1])                  # this end of the circle is inside the node
    pts = [(c[1] + ρ*cos(φ0 + 2π*t/180), c[2] + ρ*sin(φ0 + 2π*t/180)) for t in 0:180]
    out = findall(p -> !_isinside(p, a, size), pts)
    i, j = first(out), last(out)
    return [[_bisect(pts[i-1], pts[i], a, size)]; pts[i:j]; [_bisect(pts[j+1], pts[j], a, size)]]
end

# ---------------------------------------------------------------------------
# influence graphs
# ---------------------------------------------------------------------------

function _graphgeometry(g::DynamicsGraph, edgelabels)
    edgelabels in (:sign, :derivative, :none) ||
        throw(ArgumentError("edgelabels must be :sign, :derivative, or :none"))
    size = PracticalCAS._node_size(g.nodes)
    pos = Dict(zip(g.nodes, g.positions))
    n = length(g.nodes)
    centre = n == 0 ? (0.0, 0.0) : (sum(first, g.positions)/n, sum(last, g.positions)/n)
    edges = []
    extents = NTuple{2,Float64}[]
    for e in g.edges
        a, b = pos[e.from], pos[e.to]
        color = e.sign === :positive ? _BLUE : e.sign === :negative ? _VERMILION : _GREY
        text, tex, fs = if edgelabels === :none
            "", "", 0.0
        elseif edgelabels === :derivative
            string(e.derivative), latex(e.derivative), 0.17
        else
            s = e.sign === :positive ? "+" : e.sign === :negative ? "−" : e.sign === :zero ? "0" : "?"
            s, s == "−" ? "-" : s, 0.24
        end
        box = _labelsize(text, fs)
        if e.from == e.to
            r = hypot((a .- centre)...)
            u = r < 1e-9 ? (0.0, 1.0) : (a .- centre) ./ r
            path = _loop(a, size, u)
            labelpos = a .+ (_reach(size, u) + 0.1 + 0.22 + 0.05 + _extent(u, box)) .* u
        else
            d = b .- a
            u = _unit(d)
            hypot(d...) > 2_reach(size, u) + 0.1 ||
                throw(ArgumentError("node positions are too close to draw distinct nodes"))
            perp = (-u[2], u[1])
            reciprocal = any(q -> q.from == e.to && q.to == e.from, g.edges)
            c = (a .+ b) ./ 2 .+ (reciprocal ? 0.35 : 0.0) .* perp
            ua, ub = _unit(c .- a), _unit(b .- c)
            start, stop = a .+ _reach(size, ua) .* ua, b .- _reach(size, ub) .* ub
            path = _qbezier(start, c, stop)
            mid = 0.25 .* start .+ 0.5 .* c .+ 0.25 .* stop
            labelpos = mid .+ (0.06 + _extent(perp, box)) .* perp
        end
        push!(edges, (; path, color, text, tex, fs, labelpos))
        append!(extents, path)
        isempty(text) || append!(extents, [labelpos .- box ./ 2, labelpos .+ box ./ 2])
    end
    for p in g.positions
        append!(extents, [p .- size, p .+ size])
    end
    xs, ys = first.(extents), last.(extents)
    bbox = isempty(extents) ? (-1.0, 1.0, -1.0, 1.0) : (minimum(xs), maximum(xs), minimum(ys), maximum(ys))
    return (; size, edges, bbox)
end

function _graph!(ax, g; edgelabels=:sign)
    geo = _graphgeometry(g, edgelabels)
    _drawgraph!(ax, g, geo)
    return g
end

function _drawgraph!(ax, g, geo)
    for e in geo.edges
        line, head = _withhead(e.path, _HEAD)
        PBP.lines!(ax, first.(line), last.(line); color=e.color, linewidth=_STROKE)
        PBP.poly!(ax, head; color=e.color)
        isempty(e.text) || PBP.text!(ax, e.labelpos...; text=e.text, latex=e.tex, fontsize=e.fs,
                                     markerspace=:data, align=(:center, :center), color=e.color)
    end
    for (v, p) in zip(g.nodes, g.positions)
        PBP.poly!(ax, _ellipse(p, geo.size); color=:white, strokecolor=:black, strokewidth=_STROKE)
        PBP.text!(ax, p...; text=string(v), latex=latex(v), fontsize=_NODE_FONT, markerspace=:data,
                  align=(:center, :center))
    end
end

# A figure fitted to a diagram's bounding box: `scale` pixels per layout
# unit, one equal-aspect axis without decorations.
function _diagramfigure(bbox, figure, axis; scale=110, m=0.12)
    xmin, xmax, ymin, ymax = bbox
    W, H = xmax - xmin + 2m, ymax - ymin + 2m
    title = isempty(string(get(axis, :title, ""))) ? 0 : 28
    fig = PBP.Figure(; merge((; size=(round(Int, scale*W) + 20, round(Int, scale*H) + 20 + title)), figure)...)
    ax = PBP.Axis(fig[1, 1]; merge((; aspect=PBP.DataAspect(), limits=(xmin - m, xmax + m, ymin - m, ymax + m)),
                                   axis)...)
    PBP.hidedecorations!(ax)
    PBP.hidespines!(ax)
    return fig, ax
end

function dynamicsplot(g::DynamicsGraph; edgelabels=:sign, scale=110, figure=(;), axis=(;))
    geo = _graphgeometry(g, edgelabels)
    fig, ax = _diagramfigure(geo.bbox, figure, axis; scale)
    _drawgraph!(ax, g, geo)
    return fig
end

function dynamicsplot(m::PracticalCAS.DynModel; parameters=Dict(), point=Dict(), selfloops=true,
                      positions=nothing, kwargs...)
    return dynamicsplot(dynamics_graph(m; parameters, point, selfloops, positions); kwargs...)
end

dynamicsplot!(ax::PBP.Axis, g::DynamicsGraph; kwargs...) = _graph!(ax, g; kwargs...)
function dynamicsplot!(ax::PBP.Axis, m::PracticalCAS.DynModel; parameters=Dict(), point=Dict(),
                       selfloops=true, positions=nothing, kwargs...)
    return _graph!(ax, dynamics_graph(m; parameters, point, selfloops, positions); kwargs...)
end

# ---------------------------------------------------------------------------
# phase portraits
# ---------------------------------------------------------------------------

# the largest t ≥ 0 with p + t v still in the domain
function _room(d, p, v)
    t = Inf
    if d.ternary
        s3 = sqrt(3)
        u = (1 - p[1] - p[2]/s3, p[1] - p[2]/s3, 2p[2]/s3)
        du = (-v[1] - v[2]/s3, v[1] - v[2]/s3, 2v[2]/s3)
        for k in 1:3
            du[k] < 0 && (t = min(t, max(0.0, u[k])/(-du[k])))
        end
    else
        xmin, xmax, ymin, ymax = d.bounds
        for (k, lo, hi) in ((1, xmin, xmax), (2, ymin, ymax))
            v[k] > 0 && (t = min(t, max(0.0, hi - p[k])/v[k]))
            v[k] < 0 && (t = min(t, max(0.0, p[k] - lo)/(-v[k])))
        end
    end
    return t
end

# an arrow along `pts`, its head shaped in axis-fraction units (nrm ↔ dat)
function _arrow!(ax, pts, nrm, dat; color, head, linewidth)
    line, h = _withhead(nrm.(pts), head)
    PBP.lines!(ax, first.(dat.(line)), last.(dat.(line)); color, linewidth)
    PBP.poly!(ax, dat.(h); color)
end

function _portrait!(ax, d; normalize=true, arrowscale=0.7, color=_FIELD, trajectorycolor=nothing,
                    linewidth=2.0)
    isfinite(arrowscale) && arrowscale > 0 || throw(ArgumentError("arrowscale must be finite and positive"))
    xmin, xmax, ymin, ymax = d.bounds
    # Arrow lengths and heads are measured in fractions of the axis, so
    # unequal units on x and y do not distort them.
    sx, sy = d.ternary ? (1.0, 1.0) : (xmax - xmin, ymax - ymin)
    nrm(p) = (p[1]/sx, p[2]/sy)
    dat(q) = (q[1]*sx, q[2]*sy)
    h = sqrt(3)/2
    if d.ternary
        for q in (0.2, 0.4, 0.6, 0.8), (a, b) in (((q, 0.0), (q/2, h*q)), ((1-q, 0.0), (1-q/2, h*q)),
                                                    ((q/2, h*q), (1-q/2, h*q)))
            PBP.lines!(ax, [a[1], b[1]], [a[2], b[2]]; color=_LIGHT, linewidth=0.6)
        end
    end
    speeds = [hypot(v[1]/sx, v[2]/sy) for v in d.vectors]
    peak = maximum(speeds; init=0.0)
    spacing = d.ternary ? 1/(sqrt(2length(d.points))-1) : 1/(sqrt(length(d.points))-1)
    for (p, v, speed) in zip(d.points, d.vectors, speeds)
        (peak > 0 && speed > 1e-9peak) || continue
        len = arrowscale*spacing*(normalize ? 1.0 : speed/peak)
        # centred on the sample point, kept inside the domain
        half = 0.5len/speed
        fwd, back = min(half, _room(d, p, v)), min(half, _room(d, p, (-v[1], -v[2])))
        L = (fwd + back)*speed
        L > 0.15len || continue
        hl = min(0.4L, 0.32arrowscale*spacing)
        _arrow!(ax, [p .- back .* v, p .+ fwd .* v], nrm, dat; color, head=(hl, 0.42hl), linewidth=0.8)
    end
    d.ternary && PBP.lines!(ax, [0, 1, 0.5, 0], [0, 0, h, 0]; color=:black, linewidth=_STROKE)
    for (i, path) in enumerate(d.trajectories)
        length(path) >= 2 || continue
        col = trajectorycolor === nothing ? _CYCLE[mod1(i, length(_CYCLE))] : trajectorycolor
        PBP.lines!(ax, first.(path), last.(path); color=col, linewidth)
        # direction: arrowheads part-way along
        q = nrm.(path)
        cum = cumsum([0.0; [hypot((q[k] .- q[k-1])...) for k in 2:length(q)]])
        if length(q) >= 3 && cum[end] > 0.06
            for f in (0.3, 0.7)
                k = clamp(searchsortedfirst(cum, f*cum[end]), 3, length(q))
                u = _unit(q[k] .- q[k-2])
                tip, base = q[k] .+ 0.016 .* u, q[k] .- 0.016 .* u
                PBP.poly!(ax, dat.([tip, (base[1] - 0.013u[2], base[2] + 0.013u[1]),
                                    (base[1] + 0.013u[2], base[2] - 0.013u[1])]); color=col)
            end
        end
        PBP.scatter!(ax, [path[1][1]], [path[1][2]]; color=col, markersize=7, strokecolor=:white, strokewidth=1)
    end
    for e in d.equilibria
        fill = e.stability === :stable ? :black : e.stability === :unstable ? :white : "#BDBDBD"
        PBP.scatter!(ax, [e.point[1]], [e.point[2]]; color=fill, markersize=9, strokecolor=:black, strokewidth=1.4)
    end
    if d.ternary
        for (label, x, y, va) in zip(d.labels, (0.0, 1.0, 0.5), (-0.035, -0.035, h + 0.035), (:top, :top, :bottom))
            PBP.text!(ax, x, y; text=label, fontsize=0.045, markerspace=:data, align=(:center, va))
        end
    end
    return d
end

function _phasefigure(d; figure=(;), axis=(;), kwargs...)
    title = isempty(string(get(axis, :title, ""))) ? 0 : 28
    if d.ternary
        h = sqrt(3)/2
        fig, ax = _diagramfigure((-0.04, 1.04, -0.08, h + 0.08), figure, axis; scale=380, m=0.02)
    else
        xmin, xmax, ymin, ymax = d.bounds
        dx, dy = xmax - xmin, ymax - ymin
        n = sqrt(length(d.points))
        pad = max(0.03, 0.5/(n - 1))
        fig = PBP.Figure(; merge((; size=(500, 470 + title)), figure)...)
        ax = PBP.Axis(fig[1, 1]; merge((; aspect=1, xlabel=d.labels[1], ylabel=d.labels[2],
                                          xgridvisible=false, ygridvisible=false,
                                          limits=(xmin - pad*dx, xmax + pad*dx, ymin - pad*dy, ymax + pad*dy)),
                                       axis)...)
    end
    _portrait!(ax, d; kwargs...)
    return fig
end

function phaseplot(m::ODEModel; xlim=(0, 1), ylim=(0, 1), parameters=Dict(), resolution=20,
                   initials=[], dt=0.02, steps=500, equilibria=nothing, kwargs...)
    return _phasefigure(phase_data(m; xlim, ylim, parameters, resolution, initials, dt, steps, equilibria);
                        kwargs...)
end
function phaseplot!(ax::PBP.Axis, m::ODEModel; xlim=(0, 1), ylim=(0, 1), parameters=Dict(),
                    resolution=20, initials=[], dt=0.02, steps=500, equilibria=nothing, kwargs...)
    return _portrait!(ax, phase_data(m; xlim, ylim, parameters, resolution, initials, dt, steps, equilibria);
                      kwargs...)
end
function ternaryplot(m::Union{ODEModel,MatrixGame}; parameters=Dict(), resolution=18,
                     initials=[], dt=0.02, steps=500, labels=nothing, equilibria=nothing, kwargs...)
    labs = labels === nothing && m isa MatrixGame ? m.strategies : labels
    return _phasefigure(ternary_data(m; parameters, resolution, initials, dt, steps, labels=labs, equilibria);
                        kwargs...)
end
function ternaryplot!(ax::PBP.Axis, m::Union{ODEModel,MatrixGame}; parameters=Dict(), resolution=18,
                      initials=[], dt=0.02, steps=500, labels=nothing, equilibria=nothing, kwargs...)
    labs = labels === nothing && m isa MatrixGame ? m.strategies : labels
    return _portrait!(ax, ternary_data(m; parameters, resolution, initials, dt, steps, labels=labs, equilibria);
                      kwargs...)
end

end
