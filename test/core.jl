@testset "core" begin
    @syms x y z a b
    @syms p::(0, 1) r::positive K::positive n::nonneg k::integer w::complex

    @testset "canonical arithmetic" begin
        @test x + x == 2x
        @test x - x == 0
        @test x * x == x^2
        @test x^2 * x^3 == x^5
        @test (x + y) - (y + x) == 0
        @test 2 * (x + y) == 2x + 2y          # numbers distribute over sums
        @test -(x - y) == y - x
        @test x / x == 1
        @test x^0 == 1
        @test 0 * x == 0
        @test (x * y)^2 == x^2 * y^2
        @test (x^2)^3 == x^6
        @test sqrt(x)^2 == x
        @test sqrt(Num(8)) == 2 * sqrt(Num(2))
        @test sqrt(Num(4)) == 2
        @test sqrt(Num(-4)) == 2im
        @test toterm(im)^2 == -1
        @test exp(x) * exp(y) == exp(x + y)
        @test exp(log(x)) == x
        @test log(exp(x)) == x                 # x is real by default
        @test log(exp(w)) != w                 # not for complex w
        @test exp(Num(0)) == 1
        @test sin(Num(0)) == 0 && cos(toterm(π)) == -1
        @test sin(-x) == -sin(x) && cos(-x) == cos(x)
        @test Num(1 // 2) + Num(1 // 3) == Num(5 // 6)
        @test hash(x + y) == hash(y + x)
        @test length(Set([x + y, y + x, 2x])) == 2
    end

    @testset "assumptions" begin
        @test sqrt(r^2) == r                   # r > 0
        @test abs(r) == r
        @test abs(-r) == r
        @test abs(x) != x
        @test ispositive(1 - p)                # p ∈ (0, 1)
        @test ispositive(p * (1 - p))
        @test ispositive(r * K + 1)
        @test isnegative(-r / K)
        @test isnonnegative(n^2 + x^2)
        @test ispositive(exp(x))
        @test ispositive(1 - exp(-r))          # exp(-r) ∈ (0, 1)
        @test !ispositive(x)
        @test decide(r > 0) === true
        @test decide(-r > 0) === false
        @test decide(x > 0) === nothing
        @test decide(p < 1) === true
        @syms V::positive C::positive
        @test decide(C - V > 0) === nothing
        assuming(V < C) do
            @test decide(C - V > 0) === true
            @test decide(2V - 2C < 0) === true
            @test ispositive((C - V) / C)
        end
        @test decide(C - V > 0) === nothing    # the fact is gone again
    end

    @testset "subs, symbols, evalf" begin
        @test subs(x^2 + y, x => 2) == 4 + y
        @test subs(r * n * (1 - n / K), n => K) == 0
        @test free_symbols(x * y + z) == [x, y, z]
        @test has(exp(x * y), y) && !has(exp(x), y)
        @test evalf(x^2 + 1, x => 3) == 10.0
        @test evalf(sqrt(x), x => -4) ≈ 2im
        f = lambdify(r * n * (1 - n / K), [n, r, K])
        @test f(10.0, 1.0, 100.0) ≈ 9.0
        @test evalf(toterm(π)) ≈ π
    end

    @testset "differentiation" begin
        @test diff(x^3, x) == 3x^2
        @test diff(sin(x), x) == cos(x)
        @test diff(exp(2x), x) == 2exp(2x)
        @test diff(log(x), x) == 1 / x
        @test diff(x * y, x, y) == 1
        @test diff(x^4, x, 2) == 12x^2
        @test diff(a^x, x) == a^x * log(a)
        @test diff(r * n * (1 - n / K), n) ≅ r - 2r * n / K
        @funs u
        @syms t
        d = diff(u(t), t)
        @test d isa PracticalCAS.Deriv
        @test diff(u(t)^2, t) == 2u(t) * d
        J = jacobian([x * y, x + y], [x, y])
        @test J == [y x; 1 1]
        @test hessian(x^2 * y, [x, y]) == [2y 2x; 2x 0]
    end

    @testset "printing" begin
        @test string(x + 1) == "1 + x"
        @test string(K - n) == "K - n"
        @test string(x / y) == "x/y"
        @test string(x^2) == "x^2"
        @test string(sqrt(x)) == "sqrt(x)"
        @test string(-x) == "-x"
        @test string(x / 2) == "x/2"
        @test string(exp(x)) == "exp(x)"
        @test string(x ~ 1) == "x ~ 1"
        @test string(x < 1) == "x < 1"
        @test latex(x / y) == "\\frac{x}{y}"
        @test latex(sqrt(x)) == "\\sqrt{x}"
        @syms α K₁ r_max
        @test latex(α) == "\\alpha"
        @test latex(K₁) == "K_{1}"
        @test latex(r_max) == "r_{\\mathrm{max}}"
        @syms ηᵢ tᵢ δᵢ x₁ᵢ rₘₐₓ K12 βⱼ
        @test latex(ηᵢ) == "\\eta_{i}"
        @test latex(tᵢ) == "t_{i}"
        @test latex(δᵢ) == "\\delta_{i}"
        @test latex(x₁ᵢ) == "x_{1i}"
        @test latex(rₘₐₓ) == "r_{\\mathrm{max}}"
        @test latex(K12) == "K_{12}"
        @test latex(βⱼ) == "\\beta_{j}"
        @test occursin("\\eta_{i}", latex(exp(ηᵢ)))
        @test occursin("e^{", latex(exp(x)))
    end
end

@testset "factorials, gamma, binomials" begin
    @syms n::natural k::natural x
    @test factorial(toterm(5)) == 120
    @test factorial(n) isa Fn
    @test binomial(n, 2) ≅ n * (n - 1) / 2
    @test binomial(toterm(6), toterm(2)) == 15
    @test binomial(n, -1) == 0
    @test gamma(toterm(5)) == 24
    @test gamma(toterm(1 // 2)) ≅ sqrt(PracticalCAS.PI)
    @test isapprox(evalf(gamma(toterm(0.5))), sqrt(π); rtol = 1e-12)
    @test isapprox(evalf(gamma(x), x => 3.7), 4.170651783796603; rtol = 1e-12)
    @test isapprox(evalf(binomial(n, k), n => 10, k => 3), 120.0)
    @test isapprox(evalf(factorial(x), x => 2.5), 3.323350970447843; rtol = 1e-12)
    @test latex(factorial(n)) == "n!"
    @test latex(binomial(n, k)) == raw"\binom{n}{k}"
    @test ispositive(factorial(n))
    @test_throws ArgumentError diff(binomial(n, x), x)
    r, i = reim(toterm(3) + 2im)
    @test r == 3 && i == 2
end
