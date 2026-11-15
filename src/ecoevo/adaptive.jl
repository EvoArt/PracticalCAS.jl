# Evolutionary invasion analysis and adaptive dynamics (Otto & Day ch. 12).

"""
    selection_gradient(W, m, r)

`∂W/∂m` at `m = r`, for an invasion fitness `W(m, r)` of a mutant with trait
`m` in a resident population with trait `r`.
"""
selection_gradient(W, m::Sym, r::Sym) = simplify(subs(diff(toterm(W), m), m => r))

"""
    singular_strategies(W, m, r) -> Vector{Term}

The resident traits where the selection gradient vanishes.
"""
singular_strategies(W, m::Sym, r::Sym) = solve(selection_gradient(W, m, r), r)

"""
    SingularStrategy

A singular strategy `value` with the conditions for evolutionary stability
(`∂²W/∂m² < 0`: no nearby mutant invades) and convergence stability
(`∂²W/∂m² + ∂²W/∂m∂r < 0`: nearby residents evolve towards it), and the
resulting type: `:CSS` (both: an evolutionary end point), `:branching` (CS but
not ES), `:garden_of_eden` (ES but not CS), `:repeller` (neither), or
`:depends`.
"""
struct SingularStrategy
    value::Term
    ess::CondLike
    convergence::CondLike
    kind::Symbol
end

function Base.show(io::IO, s::SingularStrategy)
    println(io, "Singular strategy ", s.value, " (", s.kind, ")")
    println(io, "  evolutionarily stable if: ", s.ess)
    print(io, "  convergence stable if:    ", s.convergence)
end

"""
    classify_singular(W, m, r) -> Vector{SingularStrategy}

Find and classify the singular strategies of the invasion fitness `W(m, r)`.
The classification uses second derivatives, so it does not depend on whether
`W` is a growth rate (neutral value 0) or a growth factor (neutral value 1).
"""
function classify_singular(W, m::Sym, r::Sym)
    W = toterm(W)
    Wmm = diff(W, m, 2)
    Wmr = diff(diff(W, m), r)
    out = SingularStrategy[]
    for s in singular_strategies(W, m, r)
        d = Dict{Term,Term}(m => s, r => s)
        a = simplify(subs(Wmm, d))
        b = simplify(subs(Wmm + Wmr, d))
        es = simplify(Rel(:<, a, ZERO))
        cs = simplify(Rel(:<, b, ZERO))
        de, dc = decide(es), decide(cs)
        kind = if de === nothing || dc === nothing
            :depends
        elseif de && dc
            :CSS
        elseif dc
            :branching
        elseif de
            :garden_of_eden
        else
            :repeller
        end
        push!(out, SingularStrategy(s, es, cs, kind))
    end
    return out
end

"""
    invades(W, m, r; neutral = 0)

The condition for a mutant `m` to invade a resident `r`: `W(m, r) > neutral`
(use `neutral = 1` for discrete-time growth factors).
"""
invades(W, m::Sym, r::Sym; neutral = 0) = simplify(Rel(:>, toterm(W), toterm(neutral)))

# ---- invasion with several mutant classes ------------------------------------------

"""
    invasion_matrix(m, mutants, resident)

The linearised dynamics of rare mutants: the Jacobian of the mutant equations
with respect to the mutant variables `mutants`, at mutants = 0 and the resident
variables at the equilibrium `resident` (a dictionary). In discrete time its
dominant eigenvalue is the mutant's growth factor, in continuous time its
growth rate.
"""
function invasion_matrix(m::DynModel, mutants::AbstractVector, resident::AbstractDict)
    idx = [findfirst(==(v), m.vars) for v in mutants]
    any(isnothing, idx) && throw(ArgumentError("invasion_matrix: the mutants must be variables of the model"))
    d = _pointdict(resident)
    for v in mutants
        d[v] = ZERO
    end
    J = jacobian(Term[m.rhs[i] for i in idx], Sym[v for v in mutants])
    return Term[simplify(subs(x, d)) for x in J]
end

"""
    invasion_fitness(m, mutants, resident) -> (matrix, eigenvalues, condition)

Invasion analysis with several mutant classes (stage or class structure, or
several mutant genotypes): the [`invasion_matrix`](@ref), its eigenvalues, and
the condition under which the mutant invades, i.e. the mutant-free state is
unstable in the mutant directions (some eigenvalue with positive real part in
continuous time, outside the unit circle in discrete time).
"""
function invasion_fitness(m::DynModel, mutants::AbstractVector, resident::AbstractDict)
    A = invasion_matrix(m, mutants, resident)
    vals = something(_safe(_eigvals, A), Term[])
    stable = _iscont(m) ? routh_hurwitz(A) : jury(A)
    cond = stable isa Bool ? !stable : simplify(!stable)
    return (matrix = A, eigenvalues = vals, condition = cond)
end

"""
    selection_gradient(A, m, r; λ = 1)

For a class-structured mutant with projection matrix `A(m, r)` (trait `m`,
resident trait `r`), the derivative of the mutant's growth `∂λ/∂m` at `m = r`
from the eigenvalue sensitivity `v (∂A/∂m) w / (v w)`, with `w` the stable
class distribution and `v` the reproductive values of the resident (`λ = 1` in
discrete time at the resident equilibrium; use `λ = 0` for a continuous-time
rate matrix).
"""
function selection_gradient(A::AbstractMatrix, m::Sym, r::Sym; λ = 1)
    A = symbolic(A)
    Ar = Term[simplify(subs(x, m => r)) for x in A]
    dA = Term[simplify(subs(diff(x, m), m => r)) for x in A]
    w = right_eigvec(Ar, λ)
    v = left_eigvec(Ar, λ)
    n = length(v)
    num = sum(v[i] * dA[i, j] * w[j] for i in 1:n, j in 1:n)
    den = sum(v[i] * w[i] for i in 1:n)
    return simplify(num / den)
end
