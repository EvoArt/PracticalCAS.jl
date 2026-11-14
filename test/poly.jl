@testset "polynomials" begin
    @syms x y a b c
    @syms r::positive K::positive n::nonneg

    @testset "expand" begin
        @test expand((x + 1)^2) == x^2 + 2x + 1
        @test expand((x + y) * (x - y)) == x^2 - y^2
        @test expand(x * (y + 1)) == x * y + x
        @test expand((a + b)^3) == a^3 + 3a^2 * b + 3a * b^2 + b^3
    end

    @testset "cancel" begin
        @test cancel((x^2 - 1) / (x - 1)) == x + 1
        @test cancel(1 / x + 1 / y) ≅ (x + y) / (x * y)
        @test cancel((x^2 - y^2) / (x + y)) == x - y
        @test cancel((a * x + a * y) / (x + y)) == a
        @test iszero(cancel(r * n * (1 - n / K) - (r * n - r * n^2 / K)))
        @test cancel(x / x^2) == 1 / x
    end

    @testset "factor" begin
        @test factor(x^2 - 1) ≅ (x - 1) * (x + 1)
        _, fs = factor_list(x^2 - 1)
        @test length(fs) == 2
        _, fs = factor_list(r * n - r * n^2 / K)          # r n (K - n)/K
        @test length(filter(f -> f.second > 0, fs)) == 3
        _, fs = factor_list(x^2 + 2x * y + y^2)
        @test fs == [x + y => 2]
        _, fs = factor_list(x^3 - 6x^2 + 11x - 6)          # (x-1)(x-2)(x-3)
        @test length(fs) == 3
        _, fs = factor_list(x^4 - 5x^2 + 6)                 # (x²-2)(x²-3)
        @test length(fs) == 2
        _, fs = factor_list(a * x^2 + (a * b + 1) * x + b)  # (a x + 1)(x + b)
        @test length(fs) == 2
        @test factor(2x + 2) ≅ 2 * (x + 1)
        @test string(factor(2x + 2)) == "2*(1 + x)"
        _, fs = factor_list(x^2 + 1)
        @test length(fs) == 1
    end

    @testset "coefficients" begin
        @test polycoeffs(a * x^2 + b * x + c, x) == [c, b, a]
        @test degree(x^3 + x, x) == 3
        @test coeff(a * x^2 + b * x, x, 2) == a
        @test polycoeffs(exp(x), x) === nothing
        @test collect(a * x + b * x + c, x) ≅ c + (a + b) * x
        @test numerator((x + 1) / y) == x + 1
        @test denominator((x + 1) / y) == y
    end
end
