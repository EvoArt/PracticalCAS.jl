@testset "ecology and evolution" begin
    @syms n::nonneg r::positive K::positive R::positive

    @testset "one-variable models (Otto & Day ch. 5)" begin
        m = ode(n => r * n * (1 - n / K))
        eqs = equilibria(m)
        @test Set(e[n] for e in eqs) == Set([toterm(0), K])
        st = Dict(e[n] => stability(m, e) for e in eqs)
        @test st[toterm(0)].verdict === :unstable
        @test st[K].verdict === :stable
        @test st[K].eigenvalues == [-r]
        # discrete logistic n' = n + r n (1 - n/K): K stable iff 0 < r < 2
        d = recurrence(n => n + r * n * (1 - n / K))
        sK = stability(d, Dict(n => K))
        @test sK.verdict === :depends
        @test decide(subs(sK.condition, r => 1)) === true
        @test decide(subs(sK.condition, r => 3)) === false
        # Beverton–Holt: K stable for R > 1
        bh = recurrence(n => R * n / (1 + (R - 1) * n / K))
        s = stability(bh, Dict(n => K))
        @test s.eigenvalues == [1 / R] || isequiv(s.eigenvalues[1], 1 / R)
    end

    @testset "multi-variable models (ch. 7-8)" begin
        @syms N::nonneg P::nonneg b::positive d::positive e::positive
        # Lotka–Volterra predator–prey: the interior equilibrium is neutral
        # (purely imaginary eigenvalues), the origin a saddle
        lv = ode(N => r * N - b * N * P, P => e * b * N * P - d * P)
        eqs = equilibria(lv)
        @test length(eqs) == 2
        o = only(filter(q -> iszero(q[N]), eqs))
        @test stability(lv, o).verdict === :unstable
        # with logistic prey the interior equilibrium is stable when it exists
        rm = ode(N => r * N * (1 - N / K) - b * N * P, P => e * b * N * P - d * P)
        inter = only(filter(q -> !iszero(q[N]) && !iszero(q[P]), equilibria(rm)))
        @test inter[N] ≅ d / (e * b)
        s = stability(rm, inter)
        @test s.verdict === :depends                          # needs the equilibrium to be positive
        @test decide(subs(s.condition, r => 1, K => 10, b => 1, d => 1, e => 1)) === true
        # SIR with births: R0 and stability of the disease-free equilibrium
        @syms S::nonneg I::nonneg β::positive γ::positive μ::positive Λ::positive
        sir = ode(S => Λ - β * S * I - μ * S, I => β * S * I - (γ + μ) * I)
        dfe = Dict(S => Λ / μ, I => toterm(0))
        R0 = reproduction_number([β * S * I], [(γ + μ) * I], [I], dfe)
        @test R0 ≅ β * Λ / (μ * (γ + μ))
        sd = stability(sir, dfe)
        @test decide(subs(sd.condition, β => 1, Λ => 1, μ => 1, γ => 1)) === true   # R0 = 1/2
        @test decide(subs(sd.condition, β => 4, Λ => 1, μ => 1, γ => 1)) === false  # R0 = 2
    end

    @testset "games and ESS" begin
        @syms V::positive C::positive
        G = hawk_dove(V, C)
        es = ess(G)
        mixed = only(filter(e -> length(e.support) == 2, es))
        @test mixed.x[1] ≅ V / C
        @test mixed.condition == Rel(:>, C, V)
        pure = filter(e -> length(e.support) == 1, es)
        @test length(pure) == 1 && pure[1].support == [1]   # Dove is never an ESS
        assuming(V < C) do
            es2 = ess(G)
            @test any(e -> length(e.support) == 2 && e.holds === true, es2)
        end
        # prisoner's dilemma: defect is the only ESS
        pd = MatrixGame([3 0; 5 1]; strategies = ["C", "D"])
        e = ess(pd)
        @test length(e) == 1 && e[1].support == [2] && e[1].holds === true
        # rock–paper–scissors (zero sum): no ESS, interior Nash equilibrium
        rps = MatrixGame([0 -1 1; 1 0 -1; -1 1 0])
        @test isempty(filter(q -> q.holds === true, ess(rps)))
        ne = nash(rps)
        @test any(q -> length(q.support) == 3 && all(isequiv.(q.x, [1 // 3, 1 // 3, 1 // 3])), ne)
        # replicator dynamics for Hawk–Dove: the mixed ESS is a stable rest point
        rep = replicator(G)
        p = rep.vars[1]
        @test any(q -> isequiv(q[p], V / C), equilibria(rep))
        s = stability(rep, Dict(p => V / C))
        assuming(V < C) do
            @test decide(s.condition) === true
        end
    end

    @testset "adaptive dynamics (ch. 12)" begin
        @syms m::positive x::positive a::positive
        # a mutant m in resident x with fitness W = m*exp(-(m^2)/2)/(x*exp(-(x^2)/2)) - 1 type
        # simple stabilising example: W(m, x) = -(m - a)^2 + (x - a)^2
        W = -(m - a)^2 + (x - a)^2
        @test selection_gradient(W, m, x) ≅ -2(x - a)
        ss = classify_singular(W, m, x)
        @test length(ss) == 1 && ss[1].value == a && ss[1].kind === :CSS
        # disruptive selection at the singular point: a branching point
        W2 = (m - x)^2 - (m - x) * (x - a)
        ss2 = classify_singular(W2, m, x)
        @test only(ss2).kind === :branching
    end

    @testset "structured populations (ch. 10)" begin
        @syms f1::positive f2::positive s1::(0, 1) λ
        L = leslie([f1, f2], [s1])
        @test L == [f1 f2; s1 0]
        @test charpoly(L, λ) ≅ λ^2 - f1 * λ - f2 * s1
        # numeric example: dominant eigenvalue 2 of [1 2; 1 0]
        A = symbolic([1 2; 1 0])
        @test Set(eigvals(A)) == Set([toterm(2), toterm(-1)])
        w = stable_distribution(A, 2)
        @test w == [toterm(2 // 3), toterm(1 // 3)]
        v = reproductive_values(A, 2)
        @test v == [toterm(1), toterm(1)]
        S = sensitivity(A, 2)
        @test all(isequiv.(S, [2//3 1//3; 2//3 1//3]))
        E = elasticity(A, 2)
        @test isequiv(sum(E), 1)
    end

    @testset "Markov chains" begin
        @syms q::(0, 1)
        # gambler's ruin on {0,1,2,3}: absorbing 0 and 3
        P = [1 0 0 0; 1-q 0 q 0; 0 1-q 0 q; 0 0 0 1]
        res = absorption(P, [2, 3], [1, 4])
        @test numeq(res.probabilities[1, 2], 0.25 / (1 - 0.5 + 0.25), q => 0.5) ||
              numeq(res.probabilities[1, 2], 1 / 3, q => 0.5)
        @test numeq(res.times[1], 2.0, q => 0.5)
    end
end
