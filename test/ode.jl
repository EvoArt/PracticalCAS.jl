D2(f, v) = diff(f(v), v, 2)

@testset "ODEs and recurrences" begin
    @syms t x y a b
    @syms r::positive K::positive n::positive n₀::positive R::positive

    @testset "first order" begin
        # exponential growth
        @test dsolve(r * n, n, t; ic = n₀) == n₀ * exp(r * t)
        # constant input and decay
        s = dsolve(a - b * x, x, t; ic = 0)
        @test isequiv(diff(s, t), a - b * s) && iszero(simplify(subs(s, t => 0)))
        # logistic growth
        s = dsolve(r * n * (1 - n / K), n, t; ic = n₀)
        @test isequiv(diff(s, t), r * s * (1 - s / K))
        @test isequiv(subs(s, t => 0), n₀)
        @test limit(s, t, ∞) == K
        # separable, non-autonomous
        s = dsolve(t * x, x, t; ic = 1)
        @test isequiv(s, exp(t^2 / 2))
        # general solution has a constant
        s = dsolve(-r * x, x, t)
        @test has(s, PracticalCAS._const(1))
    end

    @testset "higher order and boundary values" begin
        @funs u w
        @syms p::(0, 1) Ns::positive
        # backward equation for fixation: u'' + 2 Ns u' = 0, u(0) = 0, u(1) = 1
        s = dsolve(D2(u, p) + 2Ns * diff(u(p), p) ~ 0, u(p); bc = [u(0) => 0, u(1) => 1])
        @test isequiv(s, (1 - exp(-2Ns * p)) / (1 - exp(-2Ns)))
        # harmonic oscillator: y'' + y = 0
        s = dsolve(D2(w, t) + w(t) ~ 0, w(t); ic = (0, [1, 0]))
        @test isequiv(s, cos(t))
        # with constant forcing
        s = dsolve(D2(w, t) - w(t) ~ 2, w(t))
        @test isequiv(diff(s, t, 2) - s, 2)
    end

    @testset "linear systems" begin
        sol = dsolve([-x, -2y], [x, y], t; ic = [1, 1])
        @test sol[1] == exp(-t) && sol[2] == exp(-2t)
    end

    @testset "recurrences" begin
        @test rsolve(R * n, n, t) == n₀ * R^t
        s = rsolve(a * n + b, n, t; ic = n₀)
        @test numeq(s, a^2 * n₀ + a * b + b, t => 2, a => 3, b => 5, n₀ => 7)
        # Beverton–Holt
        s = rsolve(R * n / (1 + (R - 1) * n / K), n, t)
        f(m) = R * m / (1 + (R - 1) * m / K)
        @test numeq(s, f(f(f(n₀))), t => 3, R => 2, K => 100, n₀ => 5)
        # haploid selection
        @syms q::(0, 1) WA::positive Wa::positive q₀::(0, 1)
        s = rsolve(q * WA / (q * WA + (1 - q) * Wa), q, t; ic = q₀)
        g(m) = m * WA / (m * WA + (1 - m) * Wa)
        @test numeq(s, g(g(q₀)), t => 2, WA => 1.2, Wa => 1.0, q₀ => 0.1)
        # linear system
        sol = rsolve([x / 2, y / 3], [x, y], t; ic = [1, 1])
        @test sol[1] ≅ (1 // 2)^t
    end
end

