# Class-structured populations (Otto & Day ch. 10), R₀, and Markov chains.

"""
    leslie(f, s)

The Leslie matrix with fecundities `f` (first row, length n) and survival
probabilities `s` (sub-diagonal, length n - 1).
"""
function leslie(f::AbstractVector, s::AbstractVector)
    n = length(f)
    length(s) == n - 1 || throw(ArgumentError("leslie: need n - 1 survival probabilities"))
    L = Term[ZERO for _ in 1:n, _ in 1:n]
    for j in 1:n
        L[1, j] = toterm(f[j])
    end
    for i in 1:n-1
        L[i+1, i] = toterm(s[i])
    end
    return L
end

"""
    stable_distribution(A, λ)

The right eigenvector of `A` for the eigenvalue `λ` (usually the dominant
one), scaled to sum to 1: the stable class distribution.
"""
function stable_distribution(A::AbstractMatrix, λ)
    w = right_eigvec(symbolic(A), λ)
    s = sum(w)
    return Term[simplify(x / s) for x in w]
end

"""
    reproductive_values(A, λ)

The left eigenvector of `A` for `λ`, scaled so the first class has value 1.
"""
function reproductive_values(A::AbstractMatrix, λ)
    v = left_eigvec(symbolic(A), λ)
    return Term[simplify(x / v[1]) for x in v]
end

"""
    sensitivity(A, λ)

The sensitivities `∂λ/∂aᵢⱼ = vᵢ wⱼ / (v·w)` of the eigenvalue `λ` to the
entries of `A`.
"""
function sensitivity(A::AbstractMatrix, λ)
    A = symbolic(A)
    w = right_eigvec(A, λ)
    v = left_eigvec(A, λ)
    vw = sum(v[i] * w[i] for i in eachindex(v))
    return Term[simplify(v[i] * w[j] / vw) for i in eachindex(v), j in eachindex(w)]
end

"""
    elasticity(A, λ)

The elasticities `(aᵢⱼ/λ) ∂λ/∂aᵢⱼ`; they sum to 1.
"""
function elasticity(A::AbstractMatrix, λ)
    S = sensitivity(A, λ)
    A = symbolic(A)
    return Term[simplify(A[i, j] / toterm(λ) * S[i, j]) for i in axes(A, 1), j in axes(A, 2)]
end

"""
    next_generation(F, V) -> K

The next-generation matrix `K = F V⁻¹` from the new-infection matrix `F` and
the transition matrix `V` (van den Driessche & Watmough).

    next_generation(infections, transitions, xs, dfe)

The same from vectors of new-infection rates and of the other transitions
(out minus in) of the infected compartments `xs`, linearised at the
disease-free equilibrium `dfe`.
"""
next_generation(F::AbstractMatrix, V::AbstractMatrix) = Term[simplify(x) for x in symbolic(F) * inv(symbolic(V))]
function next_generation(inf::AbstractVector, trans::AbstractVector, xs::AbstractVector, dfe::AbstractDict)
    d = _pointdict(dfe)
    F = Term[simplify(subs(x, d)) for x in jacobian(inf, xs)]
    V = Term[simplify(subs(x, d)) for x in jacobian(trans, xs)]
    return next_generation(F, V)
end

"""
    reproduction_number(F, V)
    reproduction_number(infections, transitions, xs, dfe)

The basic reproduction number: the dominant eigenvalue of the next-generation
matrix. When the matrix has one nonzero eigenvalue (rank one, the usual case
with one type of infection) that is returned; otherwise the vector of nonzero
eigenvalues.
"""
reproduction_number(F::AbstractMatrix, V::AbstractMatrix) = _r0(next_generation(F, V))
reproduction_number(inf::AbstractVector, trans::AbstractVector, xs::AbstractVector, dfe::AbstractDict) = _r0(next_generation(inf, trans, xs, dfe))
function _r0(K)
    size(K, 1) == 1 && return K[1, 1]
    rank(K) == 1 && return tr(K)
    vals = filter(v -> !iszero(v), _eigvals(K))
    return length(vals) == 1 ? vals[1] : vals
end

"""
    absorption(P, transient, absorbing) -> (probabilities, times, N)

For a Markov chain with transition matrix `P` (rows sum to 1), the
probabilities of ending in each absorbing state from each transient state
(`N R`), the expected number of steps to absorption (`N 1`), and the
fundamental matrix `N = (I - Q)⁻¹`.
"""
function absorption(P::AbstractMatrix, transient::AbstractVector{<:Integer}, absorbing::AbstractVector{<:Integer})
    P = symbolic(P)
    Qm = P[transient, transient]
    R = P[transient, absorbing]
    k = length(transient)
    IQ = Term[(i == j ? ONE : ZERO) - Qm[i, j] for i in 1:k, j in 1:k]
    N = inv(IQ)
    B = Term[simplify(x) for x in N * R]
    times = Term[simplify(sum(N[i, :])) for i in 1:k]
    return (probabilities = B, times = times, N = N)
end

"""
    euler_lotka(l, m, λ)

The Euler–Lotka equation `Σₓ λ⁻ˣ lₓ mₓ = 1` for survivorship `l` and fecundity
`m` by age class `x = 1, 2, …`; its positive root is the growth factor of the
age-structured population (the dominant eigenvalue of the Leslie matrix).
"""
euler_lotka(l::AbstractVector, m::AbstractVector, λ) =
    _add(Term[_mul((toterm(l[x]), toterm(m[x]), _pow(toterm(λ), Num(-x)))) for x in eachindex(l)]) ~ ONE
