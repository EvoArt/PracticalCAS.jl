using PracticalCAS
import PracticalBayesPlot as PBP

# Run with an environment containing PracticalCAS and PracticalBayesPlot.
# An optional argument selects the directory for SVG figures.
out = isempty(ARGS) ? joinpath(@__DIR__, "plotting-output") : only(ARGS)
mkpath(out)

@syms prey::positive predator::positive r::positive a::positive b::positive d::positive
lv = ode(prey => r*prey-a*prey*predator,
         predator => b*prey*predator-d*predator)
PBP.save(joinpath(out, "dynamics.svg"), dynamicsplot(lv; selfloops=false,
    axis=(; title="Predator–prey influences")))
PBP.save(joinpath(out, "phase.svg"), phaseplot(lv;
    parameters=Dict(r=>1, a=>1, b=>1, d=>1), xlim=(0, 3), ylim=(0, 3),
    initials=[[0.25, 1.0], [0.5, 1.0], [0.75, 1.0]], dt=0.02, steps=420, equilibria=:auto,
    axis=(; title="Lotka–Volterra phase portrait")))

# Competition: coexistence is a stable node; the single-species states are saddles.
@syms n1::positive n2::positive
competition = ode(n1 => n1*(1 - n1 - n2/2), n2 => n2*(1 - n2 - n1/2))
PBP.save(joinpath(out, "competition.svg"), phaseplot(competition; xlim=(0, 1.2), ylim=(0, 1.2),
    initials=[[0.05, 0.1], [1.15, 0.05], [0.1, 1.15], [1.1, 1.1]], steps=800, equilibria=:auto,
    axis=(; title="Lotka–Volterra competition")))

rps = MatrixGame([0 -1 1; 1 0 -1; -1 1 0]; strategies=["Rock", "Paper", "Scissors"])
fig = ternaryplot(rps; initials=[[0.2, 0.3, 0.5], [0.1, 0.2, 0.7]], steps=2000, equilibria=:auto,
    axis=(; title="Rock–paper–scissors replicator dynamics"))
PBP.save(joinpath(out, "ternary.svg"), fig)
PBP.save(joinpath(out, "ternary.tex"), fig)
PBP.save(joinpath(out, "ternary.typ"), fig)

# Equivalently, give all three frequency equations (or the first two with
# z replaced by 1-x-y). Rates must preserve total frequency and the simplex.
@syms x y z
frequencies = ode(x=>x*(z-y), y=>y*(x-z), z=>z*(y-x))
PBP.save(joinpath(out, "equations.svg"), ternaryplot(frequencies;
    labels=["Rock", "Paper", "Scissors"], initials=[[0.2, 0.3, 0.5]]))
