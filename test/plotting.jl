@testset "plot data" begin
    @syms prey::positive predator::positive r::positive a::positive b::positive d::positive
    m = ode(prey => r*prey-a*prey*predator, predator => b*prey*predator-d*predator)
    g = dynamics_graph(m)
    @test g.nodes == [prey, predator]
    @test length(g.edges) == 4
    edge(x, y) = only(filter(e -> e.from == x && e.to == y, g.edges))
    @test edge(predator, prey).sign == :negative
    @test edge(prey, predator).sign == :positive
    @test isequiv(edge(predator, prey).derivative, -a*prey)
    @test edge(prey, prey).sign == :unknown
    @test length(dynamics_graph(m; selfloops=false).edges) == 2
    @test g.positions[1][1] < g.positions[2][1] && g.positions[1][2] ≈ g.positions[2][2]   # side by side
    @test length(dynamics_graph(m; parameters=Dict(a=>0)).edges) == 3
    @test length(dynamics_graph(ode(prey=>prey-prey)).edges) == 0
    @test only(dynamics_graph(recurrence(prey=>2prey)).edges).derivative == toterm(2)
    @test_throws ArgumentError dynamics_graph(m; parameters=Dict(prey=>1))
    localgraph = dynamics_graph(m; parameters=Dict(r=>1, a=>1), point=Dict(predator=>2))
    @test only(filter(e -> e.from==prey && e.to==prey, localgraph.edges)).sign == :negative
    zerograph = dynamics_graph(m; parameters=Dict(r=>1, a=>1), point=Dict(predator=>1))
    @test only(filter(e -> e.from==prey && e.to==prey, zerograph.edges)).sign == :zero

    @syms x y z k
    linear = ode(x => -x, y => -2y)
    p = phase_data(linear; xlim=(-1, 1), ylim=(-1, 1), resolution=3,
                   initials=[[0.8, 0.5]], dt=0.01, steps=100)
    @test length(p.points) == 9
    @test p.vectors[1] == (1.0, 2.0)
    @test p.trajectories[1][end][1] ≈ 0.8exp(-1) atol=1e-8
    @test p.trajectories[1][end][2] ≈ 0.5exp(-2) atol=1e-8
    @test_throws ArgumentError phase_data(ode(x=>k*x, y=>y))
    @test length(phase_data(ode(x=>k*x, y=>y); parameters=Dict(k=>1)).points) == 400
    @test_throws ArgumentError phase_data(linear; resolution=1)
    @test_throws ArgumentError phase_data(linear; xlim=(1, 0))
    @test_throws ArgumentError phase_data(linear; dt=0)
    @test_throws ArgumentError phase_data(linear; initials=[[2, 0]])
    @test_throws ArgumentError phase_data(ode(x=>1/x, y=>y))

    # equilibria in the window, classified from a numerical Jacobian
    comp = ode(x => x*(1 - x - y/2), y => y*(1 - y - x/2))
    eqs = phase_data(comp; xlim=(0, 1.2), ylim=(0, 1.2), equilibria=:auto).equilibria
    @test length(eqs) == 4
    stab(p) = only(q.stability for q in eqs if isapprox(q.state, p; atol=1e-9))
    @test stab([2/3, 2/3]) == :stable
    @test stab([0, 0]) == :unstable
    @test stab([1, 0]) == :unstable && stab([0, 1]) == :unstable   # saddles
    @test only(phase_data(comp; equilibria=[[0.0, 0.0]]).equilibria).point == (0.0, 0.0)
    @test isempty(phase_data(comp).equilibria)
    @test_throws ArgumentError phase_data(comp; equilibria=[[2.0, 0.0]])
    @test_throws ArgumentError phase_data(comp; equilibria=:all)

    game = MatrixGame([0 -1 1; 1 0 -1; -1 1 0]; strategies=["Rock", "Paper", "Scissors"])
    t = ternary_data(game; resolution=6, initials=[[0.2, 0.3, 0.5]], dt=0.02, steps=100)
    @test t.ternary && t.labels == game.strategies
    @test length(t.points) == 28
    @test all(u -> minimum(u) >= 0 && sum(u) ≈ 1, t.states)
    @test t.points[findfirst(==([1.0, 0.0, 0.0]), t.states)] == (0.0, 0.0)
    @test t.points[findfirst(==([0.0, 1.0, 0.0]), t.states)] == (1.0, 0.0)
    center = findfirst(u -> all(v -> v ≈ 1/3, u), t.states)
    @test all(v -> abs(v)<1e-12, t.vectors[center])
    # At (1/2,1/2,0), rock loses to paper: velocity points right.
    boundary = findfirst(==([0.5, 0.5, 0.0]), t.states)
    @test collect(t.vectors[boundary]) ≈ [0.25, 0.0]
    @test length(only(t.trajectories)) == 101
    # Zero-sum RPS conserves the product of frequencies.
    px, py = t.trajectories[1][end]
    u3 = 2py/sqrt(3)
    u2 = px-u3/2
    @test (1-u2-u3)*u2*u3 ≈ 0.2*0.3*0.5 atol=1e-9
    # the vertices are saddles on the simplex; the centre is neutrally stable
    teq = ternary_data(game; resolution=6, equilibria=:auto).equilibria
    @test length(teq) == 4
    @test only(q for q in teq if q.stability === :neutral).state ≈ fill(1/3, 3)
    @test count(q -> q.stability === :unstable && maximum(q.state) ≈ 1, teq) == 3

    full = ode(x=>x*(z-y), y=>y*(x-z), z=>z*(y-x))
    tfull = ternary_data(full; resolution=6)
    @test all(isapprox.(first.(t.vectors), first.(tfull.vectors); atol=1e-12))
    @test all(isapprox.(last.(t.vectors), last.(tfull.vectors); atol=1e-12))
    reduced = ode(x=>x*(1-x-2y), y=>y*(2x+y-1))
    @test ternary_data(reduced; resolution=6).points == t.points
    @test_throws ArgumentError ternary_data(ode(x=>x, y=>y, z=>z))
    @test_throws ArgumentError ternary_data(ode(x=>-1, y=>0))
    @test_throws ArgumentError ternary_data(game; initials=[[0.2, 0.3]])
    @test_throws ArgumentError ternary_data(game; initials=[[0.2, 0.3, 0.4]])
    @test_throws ArgumentError ternary_data(game; labels=["a", "b"])
    @test_throws ArgumentError ternary_data(hawk_dove(1, 2))
end
