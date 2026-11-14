@testset "simplify" begin
    @syms x y
    @syms r::positive K::positive n::nonneg p::(0, 1) a::positive b::positive

    @test simplify((x^2 - 1) / (x - 1)) == x + 1
    @test simplify(sin(x)^2 + cos(x)^2) == 1
    @test simplify(sqrt(4x^2)) ≅ 2abs(x)
    @test simplify(sqrt(4a^2)) == 2a
    @test simplify(log(a^3)) == 3log(a)
    @test simplify(abs(-a * b)) == a * b
    @test simplify(r * n * (1 - n / K) - r * n + r * n^2 / K) == 0
    @test isequiv(p * (1 - p), p - p^2)
    @test logcombine(log(x) - log(y)) == log(x / y)

    @testset "conditions" begin
        @test simplify(r > 0) === true
        @test simplify(-r * K > 0) === false
        c = simplify(r * (K - n) > 0)          # r > 0 drops out
        @test c isa Rel
        @test decide(subs(c, n => K / 2)) === true
        @test decide(subs(c, n => 2K)) === false
        @syms V::positive C::positive
        c2 = simplify((C - V) / C > 0)
        @test c2 == Rel(:>, C, V)
        @test simplify((x > 0) & (r > 0)) == (x > 0)
    end
end
