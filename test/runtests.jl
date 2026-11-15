using PracticalCAS
using PracticalCAS: Add, Mul, Pow, Q
using LinearAlgebra
using Test

# equal as functions (a - b simplifies to zero)
≅(a, b) = isequiv(a, b)
# numerically equal at a point
numeq(a, b, ps...) = isapprox(evalf(toterm(a), ps...), evalf(toterm(b), ps...); rtol = 1e-9, atol = 1e-12)

@testset "PracticalCAS" begin
    include("core.jl")
    include("poly.jl")
    include("simplify.jl")
    include("solve.jl")
    include("linalg.jl")
    include("calculus.jl")
    include("ode.jl")
    include("ecoevo.jl")
    include("examples.jl")
end
