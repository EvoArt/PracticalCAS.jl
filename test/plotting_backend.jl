# Optional integration tests: run in an environment with PracticalBayesPlot.
using PracticalCAS, PracticalBayesPlot, Test
import PracticalBayesPlot as PBP

@testset "PracticalBayesPlot extension" begin
    @syms x::positive y::positive
    m = ode(x=>x*(1-y), y=>y*(x-1))
    game = MatrixGame([0 -1 1; 1 0 -1; -1 1 0]; strategies=["Rock", "Paper", "Scissors"])
    figs = [dynamicsplot(m), dynamicsplot(m; edgelabels=:derivative),
            phaseplot(m; xlim=(0, 3), ylim=(0, 3), initials=[[0.5, 0.7]]),
            ternaryplot(game; initials=[[0.2, 0.3, 0.5]]),
            phaseplot(m; xlim=(0, 3), ylim=(0, 3), equilibria=:auto, normalize=false,
                      axis=(; title="with equilibria")),
            ternaryplot(game; equilibria=:auto, trajectorycolor=:black, initials=[[0.2, 0.3, 0.5]])]
    mktempdir() do dir
        for (i, fig) in enumerate(figs)
            @test fig isa PBP.Figure
            for ext in ("svg", "tex", "typ")
                path = joinpath(dir, "plot-$i.$ext")
                PBP.save(path, fig)
                @test filesize(path) > 100
                @test !occursin("NaN", read(path, String))
            end
        end
    end
    fig = PBP.Figure()
    ax = PBP.Axis(fig[1, 1]; aspect=PBP.DataAspect())
    @test dynamicsplot!(ax, m) isa DynamicsGraph
    @test phaseplot!(ax, m) isa PhaseData
    @test ternaryplot!(ax, game) isa PhaseData
    @test length(phaseplot!(ax, m; xlim=(0, 3), ylim=(0, 3), equilibria=:auto).equilibria) == 2
    # long names widen the nodes to ellipses instead of shrinking the text
    @syms predator::positive prey::positive
    @test occursin("predator", PBP.svg(dynamicsplot(ode(prey => prey*(1 - predator), predator => predator*(prey - 1)))))
    @test_throws ArgumentError dynamicsplot(m; edgelabels=:invalid)
    @test_throws ArgumentError phaseplot(m; arrowscale=-1)
    @test occursin(">0<", PBP.svg(dynamicsplot(m; point=Dict(x=>1, y=>1))))
end
