@testset "linear algebra" begin
    @syms a b c d λ
    @syms r::positive K::positive

    A = [a b; c d]
    @test det(A) == a * d - b * c
    @test tr(A) == a + d
    @test all(isequiv.(inv(A) * A, [1 0; 0 1]))
    @test charpoly(A, λ) ≅ λ^2 - (a + d) * λ + a * d - b * c
    @test all(isequiv.(charcoeffs(A), [1, -(a + d), a * d - b * c]))

    M = symbolic([2 1; 1 2])
    @test Set(eigvals(M)) == Set([toterm(1), toterm(3)])
    e = eigen(M)
    for (λv, v) in zip(e.values, eachcol(e.vectors))
        @test all(iszero, simplify.(M * v - λv * v))
    end
    @test eigvals(symbolic([1 2; 0 3])) == [toterm(1), toterm(3)]
    # complex eigenvalues
    ev = eigvals(symbolic([0 -1; 1 0]))
    @test Set(ev) == Set([toterm(im), toterm(-im)])

    @test rank(symbolic([1 2; 2 4])) == 1
    ns = nullspace(symbolic([1 2; 2 4]))
    @test length(ns) == 1
    @test linsolve(symbolic([1 1; 1 -1]), [toterm(3), toterm(1)]) == [toterm(2), toterm(1)]
    B4 = [1 2 3 4; 0 1 2 3; 1 0 1 0; 2 1 0 1]
    @test det(symbolic(B4)) == toterm(round(Int, det(B4)))

    @testset "matrix functions" begin
        @syms t
        P = matpow(symbolic([2 1; 0 3]), t)
        @test numeq(P[1, 2], 9 - 4, t => 2)        # [2 1; 0 3]^2 = [4 5; 0 9]
        E = matexp(symbolic([-1 0; 0 -2]), t)
        @test E[1, 1] == exp(-t) && E[2, 2] == exp(-2t)
    end

    @testset "stability criteria" begin
        @syms T D
        rh = routh_hurwitz([1, -T, D])
        @test rh isa Condition
        @test decide(subs(rh, T => -1, D => 2)) === true
        @test decide(subs(rh, T => 1, D => 2)) === false
        J = [-r 0; 0 -K]
        @test routh_hurwitz(J) === true
        @test routh_hurwitz([r 0; 0 -K]) === false
        # discrete: eigenvalues 1/2 and -1/3 are inside the unit circle
        @test jury(symbolic([1//2 0; 0 -1//3])) === true
        @test jury(symbolic([2 0; 0 0])) === false
        j1 = jury([1, -a])                          # one variable: -1 < a < 1
        @test decide(subs(j1, a => 1 // 2)) === true
        @test decide(subs(j1, a => -3 // 2)) === false
    end
end
