"""
    PracticalCAS

A computer algebra system in pure Julia, aimed first at mathematical modelling
in ecology and evolution (everything Otto & Day's *A Biologist's Guide to
Mathematical Modeling* needs): exact arithmetic with assumptions, polynomial
algebra and factorisation, simplification, equation and system solving, symbolic
linear algebra, calculus (limits, series, integration), ODE and recurrence
solving, and tools for equilibria and stability, invasion analysis and adaptive
dynamics, matrix games and ESSs, structured populations and R₀.

The code is layered (see CLAUDE.md): core → poly → simplify → solve → linalg →
calculus → ode → ecoevo, each layer using only the ones before it.
"""
module PracticalCAS

using LinearAlgebra
import LinearAlgebra: det, tr, rank, nullspace, eigvals, eigvecs, eigen

# core: terms, arithmetic, assumptions, printing
include("core/types.jl")
include("core/arith.jl")
include("core/functions.jl")
include("core/syms.jl")
include("core/assume.jl")
include("core/traverse.jl")
include("core/relations.jl")
include("core/diff.jl")
include("core/numeric.jl")
include("core/printing.jl")

# polynomials and rational functions
include("poly/mpoly.jl")
include("poly/convert.jl")
include("poly/factor.jl")
include("poly/api.jl")

include("simplify/simplify.jl")
include("solve/solve.jl")
include("linalg/linalg.jl")

include("calculus/limits.jl")
include("calculus/series.jl")
include("calculus/apart.jl")
include("calculus/integrate.jl")

include("ode/dsolve.jl")
include("ode/rsolve.jl")

include("ecoevo/models.jl")
include("ecoevo/games.jl")
include("ecoevo/adaptive.jl")
include("ecoevo/structured.jl")

"""
    ∞

Infinity, for limits and integration bounds (`-∞` for minus infinity).
"""
const ∞ = INF

# core
export Term, Num, Sym, Fn, Eqn, Condition, Rel, And, Or, UFun, RootOf
export @syms, @funs, sym, toterm, ∞
export subs, free_symbols, has, complexity, evalf, lambdify, latex
export gradient, jacobian, hessian, reim
export assume!, forget!, assuming, eq, neq
# polynomials
export expand, cancel, together, factor, factor_list, polycoeffs, degree, coeff
# simplification and reasoning
export simplify, sign_of, ispositive, isnegative, isnonnegative, isnonpositive,
    decide, isequiv, logcombine
# solving
export solve
# linear algebra (det, tr, inv, rank, nullspace, eigvals, eigvecs, eigen extend LinearAlgebra)
export det, tr, rank, nullspace, eigvals, eigvecs, eigen
export symbolic, rref, linsolve, charpoly, charcoeffs, left_eigvec, right_eigvec,
    matpow, matexp, routh_hurwitz, jury
# calculus
export limit, taylor, series, linearize, apart, integrate
# differential and difference equations
export dsolve, rsolve
# ecology and evolution
export ode, recurrence, ODEModel, MapModel, equilibria, stability, Stability,
    nullclines, invasion_fitness
export MatrixGame, hawk_dove, payoff, nash, ess, replicator, GameEquilibrium
export selection_gradient, singular_strategies, classify_singular, SingularStrategy, invades
export leslie, stable_distribution, reproductive_values, sensitivity, elasticity,
    next_generation, reproduction_number, absorption

end
