@testset "calculus" begin
    @syms x y a
    @syms r::positive K::positive n::nonneg t::nonneg s::positive N::positive

    @testset "limits" begin
        @test limit(sin(x) / x, x, 0) == 1
        @test limit((x^2 - 1) / (x - 1), x, 1) == 2
        @test limit(1 / x, x, ∞) == 0
        @test limit(x, x, ∞) == ∞
        @test limit(exp(-r * t), t, ∞) == 0
        @test limit((1 - exp(-x)) / x, x, 0) == 1
        @test limit(x * log(x), x, 0; dir = :right) == 0
        @test limit((3x^2 + 1) / (x^2 - 2), x, ∞) == 3
        # the logistic solution approaches K
        sol = K / (1 + (K - 1) * exp(-r * t))
        @test limit(sol, t, ∞) == K
    end

    @testset "taylor" begin
        @test taylor(exp(x), x, 0, 3) ≅ 1 + x + x^2 / 2 + x^3 / 6
        @test taylor(log(1 + x), x, 0, 2) ≅ x - x^2 / 2
        @test taylor(1 / (1 - x), x, 0, 3) ≅ 1 + x + x^2 + x^3
        @test taylor(sin(x), x, 0, 5) ≅ x - x^3 / 6 + x^5 / 120
        @test taylor(x * y, [x, y], [1, 1], 1) ≅ x + y - 1
    end

    @testset "partial fractions" begin
        @test apart(1 / (x * (x + 1)), x) ≅ 1 / x - 1 / (x + 1)
        @test apart(1 / (n * (K - n)), n) ≅ 1 / (K * n) + 1 / (K * (K - n))
        @test apart((x + 3) / ((x + 1) * (x + 2)), x) ≅ 2 / (x + 1) - 1 / (x + 2)
        @test apart(1 / (x^2 * (x + 1)), x) ≅ 1 / x^2 - 1 / x + 1 / (x + 1)
    end

    @testset "integrate" begin
        D(F, f, v) = isequiv(diff(F, v), f)
        for f in (x^3, 1 / x, exp(2x), sin(3x), cos(x), x * exp(x), x^2 * sin(x),
                  log(x), x * log(x), 1 / (1 + x^2), 1 / (x * (x + 1)), x / (x^2 + 1),
                  exp(x) * sin(x), x * exp(x^2), sin(x) * cos(x), 1 / (x * log(x)),
                  (2x + 1) / (x^2 + x + 1), 1 / (2x + 3)^2, sqrt(x), atan(x))
            F = integrate(f, x)
            @test !(F isa Fn && F.head === :Integral)
            @test D(F, f, x)
        end
        # the logistic integral: ∫ dn / (r n (1 - n/K))
        F = integrate(1 / (r * n * (1 - n / K)), n)
        @test D(F, 1 / (r * n * (1 - n / K)), n)
        @test integrate(x^2, x, 0, 1) == 1 // 3
        @test integrate(exp(-x), (x, 0, ∞)) == 1
        @test integrate(exp(-r * t), t, 0, ∞) == 1 / r
        # unevaluated when no antiderivative is known
        @test integrate(exp(x^2), x) isa Fn
    end
end
