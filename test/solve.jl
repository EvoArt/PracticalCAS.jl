@testset "solve" begin
    @syms x y a b c
    @syms r::positive K::positive n::nonneg R::positive

    @testset "one equation" begin
        @test Set(solve(x^2 - 1, x)) == Set([toterm(-1), toterm(1)])
        @test solve(2x + 3 ~ 0, x) == [toterm(-3 // 2)]
        s = solve(a * x^2 + b * x + c, x)
        @test length(s) == 2
        @test all(v -> iszero(simplify(subs(a * x^2 + b * x + c, x => v))), s)
        # logistic equilibria
        @test Set(solve(r * n * (1 - n / K), n)) == Set([toterm(0), K])
        # Beverton–Holt (discrete): n = R n/(1 + (R-1) n/K)
        s = solve(R * n / (1 + (R - 1) * n / K) ~ n, n)
        @test Set(s) == Set([toterm(0), K])
        # Ricker: n = n exp(r (1 - n/K))
        s = solve(n * exp(r * (1 - n / K)) ~ n, n)
        @test Set(s) == Set([toterm(0), K])
        # exponentials and logs
        @test solve(exp(x) ~ 2, x) == [log(toterm(2))]
        @test solve(log(x) ~ 1, x) == [exp(toterm(1))]
        @test solve(x^4 - 5x^2 + 4, x) |> length == 4
        @test isempty(solve(x^2 + 1, x) |> s -> filter(isreal, s))
        # denominators: x/(x - 1) = 0 has x = 0 only; (x^2-1)/(x-1) = 0 has x = -1 only
        @test solve((x^2 - 1) / (x - 1), x) == [toterm(-1)]
    end

    @testset "systems" begin
        s = solve([x + y ~ 1, x - y ~ 0], [x, y])
        @test length(s) == 1 && s[1][x] == 1 // 2 && s[1][y] == 1 // 2
        # Lotka–Volterra competition equilibria
        @syms n1::nonneg n2::nonneg r1::positive r2::positive K1::positive K2::positive α::positive β::positive
        F = [r1 * n1 * (1 - (n1 + α * n2) / K1), r2 * n2 * (1 - (n2 + β * n1) / K2)]
        eqs = solve(F, [n1, n2])
        @test length(eqs) == 4
        interior = only(filter(e -> !iszero(e[n1]) && !iszero(e[n2]), eqs))
        @test interior[n1] ≅ (K1 - α * K2) / (1 - α * β)
        @test interior[n2] ≅ (K2 - β * K1) / (1 - α * β)
        # predator–prey with logistic prey
        @syms N::nonneg P::nonneg b::positive d::positive e::positive
        G = [r * N * (1 - N / K) - b * N * P, e * b * N * P - d * P]
        eqs = solve(G, [N, P])
        @test length(eqs) == 3
    end
end
