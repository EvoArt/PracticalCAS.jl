"""
    dynamicsplot(model; parameters=Dict(), point=Dict(), selfloops=true,
                 positions=nothing, edgelabels=:sign, scale=110, figure=(;), axis=(;))
    dynamicsplot(graph::DynamicsGraph; kwargs...)

Draw a symbolic influence graph. Load `PracticalBayesPlot` to enable drawing.
Positive edges are blue, negative vermilion, and unknown grey; edge labels can be
`:sign`, `:derivative`, or `:none`. Nodes widen to ellipses for long names; the
figure is sized to the drawing at `scale` pixels per layout unit. Returns a PracticalBayesPlot figure, which
displays inline as SVG and can be saved as SVG, TikZ, or CeTZ.
Structural edges whose derivative vanishes at a supplied `point` are labelled `0`.
See `dynamics_graph` for the meaning of arrows.
"""
function dynamicsplot end

"Draw a dynamics graph into an existing PracticalBayesPlot axis; return its graph data."
function dynamicsplot! end

"""
    phaseplot(model; xlim=(0, 1), ylim=(0, 1), parameters=Dict(),
              resolution=20, initials=[], dt=0.02, steps=500, equilibria=nothing,
              normalize=true, arrowscale=0.7, trajectorycolor=nothing,
              figure=(;), axis=(;))

Draw a two-variable ODE's phase portrait with direction arrows and optional
trajectories. Load `PracticalBayesPlot` first. See `phase_data` for numerical
options. Arrows are normalised by default; with `normalize=false`, lengths
are relative to the largest sampled speed. `arrowscale` scales arrow length
relative to grid spacing. Trajectories take Wong's palette in turn (or all
`trajectorycolor`), with a dot at the start and arrowheads along the way.
`equilibria=:auto` marks the equilibria in the window: filled if stable, open
if unstable (saddles included), grey if neutral.
"""
function phaseplot end

"Draw a phase portrait into an existing PracticalBayesPlot axis; return its `PhaseData`."
function phaseplot! end

"""
    ternaryplot(game_or_model; kwargs...)

Draw a ternary phase portrait of a three-strategy `MatrixGame` or frequency
equations (`ODEModel`). Load `PracticalBayesPlot` first. See `ternary_data` for
model conventions and numerical options, and `phaseplot` for drawing options.
"""
function ternaryplot end

"Draw a ternary portrait into an existing PracticalBayesPlot axis; return its `PhaseData`."
function ternaryplot! end

for name in (:dynamicsplot, :dynamicsplot!, :phaseplot, :phaseplot!, :ternaryplot, :ternaryplot!)
    @eval $name(args...; kwargs...) = throw(ArgumentError(
        "load PracticalBayesPlot (`using PracticalBayesPlot`) and pass a supported model or axis to " * $(string(name))))
end
