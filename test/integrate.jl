# Integration corpus: every antiderivative is checked by differentiating it
# and comparing with the integrand at a few points (independently of the
# integrator's own check).

using PracticalCAS: PI

const INT_PTS = (0.37, 0.71, 1.29)

function intcheck(f, x, vals...; pts = INT_PTS)
    t0 = time()
    F = integrate(f, x)
    isdefined(Main, :INT_VERBOSE) && println(rpad(string(f), 40), " => ", F, "   [", round(time() - t0; digits = 2), "s]"); isdefined(Main, :INT_VERBOSE) && flush(stdout)
    F isa Fn && F.head === :Integral && return false
    dF = diff(F, x)
    for p in pts
        a = evalf(dF, x => p, vals...)
        b = evalf(toterm(f), x => p, vals...)
        isapprox(a, b; rtol = 1e-8, atol = 1e-10) || return false
    end
    return true
end

@testset "integration corpus" begin
    @syms x a::positive b::positive
    @syms r::positive K::positive n::nonneg t::nonneg μ σ::positive λ::positive

    rational = [
        1 / (x^2 + 1), 1 / (x^2 - 1), x / (x^2 + 1), 1 / (x^3 + 1), 1 / (x^4 + 1),
        (x^2 + 1) / (x^3 - x), 1 / (x^2 + x + 1)^2, (3x + 2) / (x^2 + 2x + 5)^2,
        1 / (x^3 + 2), 1 / ((x - 1)^3 * (x + 2)), x^5 / (x^2 + 1), 1 / (x^6 - 1),
        1 / (x^4 - 2), (x^4 + 1) / (x^2 * (x^2 + 1)^2), (2x^3 - 4x + 1) / (x^2 - 2x + 3),
        1 / (x^2 + 2)^3, (x^3 + x) / (x^4 + 2x^2 + 1), 1 / (x * (x^2 + 4)),
        (x - 1) / (x^2 + 4x + 13), 1 / (4x^2 + 4x + 5), 1 / (x^5 + x),
    ]
    for f in rational
        @test intcheck(f, x)
    end
    # parameters
    @test intcheck(1 / (a^2 + x^2), x, a => 1.7)
    @test intcheck(1 / (x^2 - a^2), x, a => 0.3)
    @test intcheck(1 / (a * x^2 + b), x, a => 1.3, b => 0.6)
    @test intcheck(1 / (r * n * (1 - n / K)), n, r => 0.5, K => 3.0)
    @test intcheck(x / ((x + a) * (x + b)), x, a => 1.3, b => 0.6)

    exponential = [
        x * exp(x), x^2 * exp(-x), exp(x) / (1 + exp(x)), exp(x) / (1 + exp(2x)),
        1 / (1 + exp(x)), exp(2x) / (1 + exp(x)), x * exp(x^2), exp(-x^2), x^2 * exp(-x^2),
        exp(-x^2 + 2x), exp(x) / x, exp(x) / x^2, (x + 1) * exp(x) / x, exp(exp(x)) * exp(x),
        exp(x) / (1 + x)^2 * x, (1 + 2x^2) * exp(x^2), exp(x) * log(x) + exp(x) / x,
        2^x, x * 2^x, x^x * (1 + log(x)), exp(3x) * exp(-x) * x, exp(x) / (exp(2x) - 1),
        1 / (exp(x) + exp(-x)), exp(x) * (x^2 + 1) / (x + 1)^2,
    ]
    for f in exponential
        @test intcheck(f, x)
    end

    logarithmic = [
        log(x), log(x)^2, x * log(x), x^2 * log(x)^2, log(x) / x, 1 / (x * log(x)),
        log(1 + x), log(x^2 + 1), log(x) / x^2, log(log(x)) / x, 1 / (x * (1 + log(x)^2)),
        log(x)^3 / x, x^3 * log(2x), 1 / log(x), log(x) / (1 + x)^2,
    ]
    for f in logarithmic
        @test intcheck(f, x)
    end

    trigonometric = [
        sin(x)^2, sin(x)^3, sin(x)^2 * cos(x)^3, sin(x)^4, cos(x)^2 * sin(x)^2, x * sin(x),
        x^2 * cos(3x), exp(2x) * sin(3x), x * exp(x) * sin(x), sin(2x) * cos(3x), tan(x),
        tan(x)^2, tan(x)^3, 1 / cos(x), 1 / sin(x), 1 / (2 + cos(x)), 1 / (1 + sin(x)),
        sin(x) / (1 + cos(x)^2), 1 / cos(x)^2, 1 / (sin(x) * cos(x)), sin(x) / x,
        cos(2x) / x, x^2 * sin(x) * exp(-x), sinh(x)^2, cosh(x) * sinh(x), x * cosh(x),
        tanh(x), 1 / cosh(x), sin(x)^5 * cos(x)^2, cos(x)^6, sin(3x + 1) * sin(x),
        x * sin(x)^2, 1 / (3 + 5 * sin(x)), sin(x) * cos(x) / (1 + sin(x)^2),
    ]
    for f in trigonometric
        @test intcheck(f, x)
    end

    inverse = [atan(x), x * atan(x), asin(x), acos(x), x^2 * atan(x), atan(x) / x^2, log(x) * atan(x) / x^0]
    for f in inverse[1:6]
        @test intcheck(f, x; pts = (0.21, 0.43, 0.67))
    end

    algebraic = [
        sqrt(x), x * sqrt(1 + x), 1 / sqrt(1 - x^2), sqrt(1 - x^2), x / sqrt(1 - x^2),
        sqrt(x^2 + 1), 1 / sqrt(x^2 + 1), x^2 / sqrt(x^2 + 4), 1 / (x * sqrt(x^2 + 1)),
        sqrt(x) / (1 + x), 1 / (sqrt(x) + 1), 1 / sqrt(2x - x^2), (x + 1) / sqrt(x^2 + 2x + 5),
        (1 + x^2)^(3 // 2), 1 / (1 + x^2)^(3 // 2), x^3 * sqrt(1 + x^2), x / sqrt(x + 1),
        1 / (x^(1 // 3) + x^(1 // 2)), sqrt(1 + x) / x, x * (2x + 3)^(2 // 3),
    ]
    for f in algebraic
        @test intcheck(f, x; pts = (0.21, 0.43, 0.67))
    end

    # ecology and probability
    @test intcheck(t * exp(-r * t), t, r => 0.8)
    @test intcheck(t^2 * exp(-a * t), t, a => 1.4)
    @test intcheck(λ * t * exp(-λ * t), t, λ => 0.9)
    @test intcheck(1 / (a + b * exp(-r * t)), t, a => 1.2, b => 0.7, r => 0.5)
    @test intcheck(exp(-(x - μ)^2 / (2σ^2)) / (σ * sqrt(2PI)), x, μ => 0.3, σ => 1.1)
    @test intcheck(r * n * (1 - n / K), n, r => 0.5, K => 3.0)
    @test intcheck(exp(-a * x) * sin(b * x), x, a => 0.4, b => 2.0)
    @test intcheck(x^(a - 1) * exp(-x) * (a - x), x, a => 2.5)

    @testset "forms" begin
        @test isequiv(integrate(1 / (1 + x^2), x), atan(x))
        @test isequiv(integrate(exp(-x^2), x), sqrt(PI) / 2 * erf(x))
        @test isequiv(integrate(exp(x) / x, x), Ei(x))
        @test isequiv(integrate(sin(x) / x, x), Si(x))
        @test isequiv(integrate(1 / sqrt(1 - x^2), x), asin(x))
        @test !has(integrate(1 / (1 + x^4), x), PracticalCAS._TSYM)
        @test isequiv(integrate(x / (x^2 + 1), x), log(x^2 + 1) / 2)
        @test !has(integrate(sin(x)^2 * cos(x), x), PracticalCAS.IM)
        @test !has(integrate(exp(x) * sin(x), x), PracticalCAS.IM)
    end

    @testset "definite" begin
        @test integrate(x^2, x, 0, 1) == 1 // 3
        @test integrate(exp(-x), (x, 0, ∞)) == 1
        @test integrate(exp(-r * t), t, 0, ∞) == 1 / r
        @test isequiv(integrate(exp(-x^2), x, -∞, ∞), sqrt(PI))
        @test integrate(x^3 * exp(-x), x, 0, ∞) == 6
        @test isequiv(integrate(1 / (1 + x^2), x, 0, 1), PI / 4)
        @test isequiv(integrate(1 / (1 + x^2), x, 0, ∞), PI / 2)
        @test integrate(sin(x), x, 0, PI) == 2
        @test isapprox(evalf(integrate(1 / (2 + cos(x)), x, 0, 2PI)), 2π / sqrt(3); rtol = 1e-10)
        @test integrate(1 / x, x, -1, 1) isa Fn
        @test isequiv(integrate(exp(-(x - μ)^2 / (2σ^2)) / (σ * sqrt(2PI)), x, -∞, ∞), 1)
        @test isequiv(integrate(exp(-(x - μ)^2 / (2σ^2)) / σ, x, -∞, ∞), sqrt(2PI))
    end

    @testset "special function values" begin
        @test erf(0.5) ≈ 0.5204998778130465 rtol = 1e-13
        @test erf(3.0) ≈ 0.9999779095030014 rtol = 1e-13
        @test erfi(1.0) ≈ 1.6504257587975428 rtol = 1e-13
        @test Ei(1.0) ≈ 1.8951178163559368 rtol = 1e-13
        @test Ei(-2.0) ≈ -0.04890051070806112 rtol = 1e-12
        @test Ei(50.0) ≈ 1.0585636897131690963e20 rtol = 1e-12
        @test Si(1.0) ≈ 0.9460830703671830 rtol = 1e-13
        @test Si(10.0) ≈ 1.658347594218874 rtol = 1e-13
        @test Ci(1.0) ≈ 0.3374039229009681 rtol = 1e-13
        @test Ci(10.0) ≈ -0.04545643300445537 rtol = 1e-12
        @test evalf(erf(toterm(1 // 2))) ≈ 0.5204998778130465
    end

    # non-elementary and not handled: left unevaluated
    @test integrate(exp(x^3), x) isa Fn
    @test integrate(sin(x^2), x) isa Fn
end
