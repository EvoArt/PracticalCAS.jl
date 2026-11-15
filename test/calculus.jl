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
        D(F, f, v) = all(p -> isapprox(evalf(diff(F, v), v => p, r => 0.7, K => 2.0), evalf(f, v => p, r => 0.7, K => 2.0); rtol = 1e-8), (0.3, 0.6, 1.1))
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
        # non-elementary: erfi; unevaluated when no antiderivative is known
        @test isequiv(integrate(exp(x^2), x), sqrt(PracticalCAS.PI) / 2 * erfi(x))
        @test integrate(exp(x^3), x) isa Fn
    end
end

include("integrate.jl")

@testset "sums, products, Euler integrals, perturbation" begin
    @syms k::natural n::natural p::(0, 1) s x λ::positive a::positive b::positive r::positive ε
    @test summation(k^2, k, 1, n) ≅ n * (n + 1) * (2n + 1) / 6
    @test summation(k^3, k, 1, n) ≅ (n * (n + 1) / 2)^2
    @test summation(x^k, k, 0, n - 1) ≅ (x^n - 1) / (x - 1)
    @test summation(k * x^k, k, 0, ∞) ≅ x / (1 - x)^2
    @test summation(k, k, 1, 10) == 55
    @test summation(exp(-λ) * λ^k / factorial(k), k, 0, ∞) ≅ 1
    @test summation(k^2 * exp(-λ) * λ^k / factorial(k), k, 0, ∞) ≅ λ + λ^2
    @test summation(exp(-λ) * λ^k / factorial(k), k, 2, ∞) ≅ 1 - exp(-λ) * (1 + λ)
    @test summation(k * binomial(n, k) * p^k * (1 - p)^(n - k), k, 0, n) ≅ n * p
    @test summation(binomial(n, k) * x^k, k, 0, n) ≅ (1 + x)^n
    @test summation(k * (1 - p)^(k - 1) * p, k, 1, ∞) ≅ 1 / p
    @test summation(1 / k^2, k, 1, ∞) isa Fn
    @test isapprox(evalf(summation(1 / k^2, k, 1, ∞)), π^2 / 6; rtol = 1e-5)
    @test product(k, k, 1, n) == factorial(n)
    @test product(r, k, 1, n) ≅ r^n
    @test product((k + 1) / k, k, 1, n) ≅ n + 1
    @test integrate(x^(a - 1) * exp(-b * x), x, 0, ∞) ≅ gamma(a) / b^a
    @test integrate(x^(a - 1) * (1 - x)^(b - 1), x, 0, 1) ≅ gamma(a) * gamma(b) / gamma(a + b)
    @test simplify(gamma(a + 2) / gamma(a)) ≅ a * (a + 1)
    @test simplify(factorial(n + 1) / factorial(n - 1)) ≅ n * (n + 1)
    rts = perturb(x^2 - (2 + ε) * x + ε, x, ε; order = 2)
    @test any(r -> r ≅ ε / 2 - ε^2 / 8, rts) && any(r -> r ≅ 2 + ε / 2 + ε^2 / 8, rts)
end

@testset "Gaussian integrals" begin
    @syms z μ σ::positive
    φ = exp(-(z - μ)^2 / (2σ^2)) / sqrt(2 * PracticalCAS.PI * σ^2)
    @test integrate(φ, z, -∞, ∞) ≅ 1
    @test integrate(z * φ, z, -∞, ∞) ≅ μ
    @test integrate((z - μ)^2 * φ, z, -∞, ∞) ≅ σ^2
    @test integrate((z - μ)^4 * φ, z, -∞, ∞) ≅ 3σ^4
    @test integrate(z^2 * φ, z, -∞, ∞) ≅ μ^2 + σ^2
end
