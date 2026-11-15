# Stochastic models (Otto & Day ch. 13–15) with symbolic parameters:
# stationary distributions of Markov chains, generating functions and
# branching processes, the Moran and Wright–Fisher models, birth–death chains,
# and diffusion approximations. (Distribution families, their moments and
# numeric Markov chains are in PracticalProbability.jl.)

_eye(n) = Term[i == j ? ONE : ZERO for i in 1:n, j in 1:n]

"""
    stationary_distribution(P; continuous = false)

The stationary distribution `π` of a Markov chain, `π P = π` with `Σ π = 1`,
for a transition matrix `P` whose rows sum to 1 (entries may be symbolic). With
`continuous = true`, `P` is a rate matrix `Q` (rows sum to 0) and `π Q = 0`.
Throws if the stationary distribution is not unique.

    @syms a::(0, 1) b::(0, 1)
    stationary_distribution([1-a a; b 1-b])     # [b/(a + b), a/(a + b)]
"""
function stationary_distribution(P::AbstractMatrix; continuous::Bool = false)
    P = symbolic(P)
    n = LinearAlgebra.checksquare(P)
    B = continuous ? P : P - _eye(n)
    ns = _nullspace(permutedims(B))
    length(ns) == 1 || throw(ArgumentError("stationary_distribution: the stationary distribution is not unique ($(length(ns)) independent solutions)"))
    v = ns[1]
    s = sum(v)
    return Term[simplify(x / s) for x in v]
end

# ---- generating functions and branching processes --------------------------------

"""
    pgf(pmf, k, s; lo = 0, hi = ∞)

The probability generating function `G(s) = Σₖ pmf(k) sᵏ` (by
[`summation`](@ref)).

    @syms k::natural s λ::positive
    pgf(exp(-λ) * λ^k / factorial(k), k, s)     # exp(λ(s - 1))
"""
pgf(pmf, k::Sym, s; lo = 0, hi = INF) = summation(toterm(pmf) * _pow(toterm(s), k), k, lo, hi)

"""
    pgf_moments(G, s) -> (mean, variance)

The mean `G'(1)` and variance `G''(1) + G'(1) - G'(1)²` of a distribution on
0, 1, 2, … from its probability generating function.
"""
function pgf_moments(G, s::Sym)
    G = toterm(G)
    m1 = _at(diff(G, s), s, ONE)
    m2 = _at(diff(G, s, 2), s, ONE)
    return (mean = simplify(m1), variance = simplify(m2 + m1 - m1^2))
end

"""
    extinction_probability(G, s)

The probability that a branching process with offspring generating function
`G(s)` eventually goes extinct: the smallest root of `G(s) = s` in `[0, 1]`.
It is 1 when the mean number of offspring `G'(1) ≤ 1`; otherwise the root
below 1. When the comparison of the mean with 1 cannot be decided under the
assumptions, the root other than 1 is returned (the answer when the mean
exceeds 1). Roots that are known to be outside `[0, 1]` are discarded.

    @syms s p::(0, 1)
    extinction_probability((1 - p) + p * s^2, s)     # (1 - p)/p, for p > 1/2
"""
function extinction_probability(G, s::Sym)
    G = toterm(G)
    mean = simplify(_at(diff(G, s), s, ONE))
    decide(Rel(:<=, mean, ONE)) === true && return ONE
    roots = filter(r -> !isequiv(r, ONE), _quiet(() -> solve(G - s, s)))
    if isempty(roots) && isempty(setdiff(free_symbols(G), [s]))
        # no closed form (Poisson offspring): iterate q ← G(q) from 0, which
        # increases to the smallest fixed point
        g = lambdify(G, [s])
        q = 0.0
        for _ in 1:100_000
            qn = Float64(real(g(q)))
            abs(qn - q) < 1e-15 && return Num(qn)
            q = qn
        end
        return Num(q)
    end
    isempty(roots) && throw(ArgumentError("extinction_probability: G(s) = s has no closed-form root here; give the parameters numeric values"))
    roots = filter(r -> decide(Rel(:>=, r, ZERO)) !== false && decide(Rel(:<, r, ONE)) !== false && _isreal_struct(r), roots)
    isempty(roots) && throw(ArgumentError("extinction_probability: no root of G(s) = s in [0, 1) found"))
    length(roots) == 1 && return roots[1]
    sure = filter(r -> decide(Rel(:>=, r, ZERO)) === true && decide(Rel(:<, r, ONE)) === true, roots)
    length(sure) == 1 && return sure[1]
    return roots
end

# ---- birth–death chains, Moran and Wright–Fisher ------------------------------------

"""
    fixation_probability(λ, μ, j, i, N)

For a birth–death chain on `0, 1, …, N` (absorbing at both ends) that moves
from state `j` up with rate or probability `λ` and down with `μ` (terms in the
symbol `j`), the probability of reaching `N` from `i`:

    Σ_{k=0}^{i-1} Πₗ₌₁ᵏ (μₗ/λₗ)  /  Σ_{k=0}^{N-1} Πₗ₌₁ᵏ (μₗ/λₗ).

`N` and `i` may be symbolic when the ratio `μ/λ` is a constant or a product
of powers. In the Moran model with relative fitness `r` the ratio is `1/r`:

    @syms j::natural i::natural N::natural r::positive
    fixation_probability(r * j * (N - j), j * (N - j), j, i, N)   # (1 - r^-i)/(1 - r^-N)
"""
function fixation_probability(λ, μ, j::Sym, i, N)
    k = Sym(gensym(:k), SymInfo(true, true, Q(0), false, nothing, false))
    ρ = simplify(toterm(μ) / toterm(λ))
    Πk = product(ρ, j, 1, k)
    num = summation(Πk, k, 0, toterm(i) - 1)
    den = summation(Πk, k, 0, toterm(N) - 1)
    return simplify(num / den)
end

"""
    moran(N; r = 1) -> Matrix

The transition matrix of the Moran model with `N` individuals, on states
`0, …, N` (the number of copies of an allele with relative fitness `r`): one
individual reproduces, chosen with probability proportional to fitness, and
replaces one chosen at random. Use with [`absorption`](@ref).
"""
function moran(N::Integer; r = 1)
    r = toterm(r)
    P = Term[ZERO for _ in 0:N, _ in 0:N]
    for i in 0:N
        w = r * i + (N - i)
        up = i in (0, N) ? ZERO : simplify(r * i / w * (N - i) / N)
        down = i in (0, N) ? ZERO : simplify((N - i) / w * i / N)
        i < N && (P[i+1, i+2] = up)
        i > 0 && (P[i+1, i] = down)
        P[i+1, i+1] = simplify(1 - up - down)
    end
    return P
end

"""
    wright_fisher(N; s = 0) -> Matrix

The transition matrix of the haploid Wright–Fisher model with `N` individuals
on states `0, …, N`: the next generation is a binomial sample of size `N` with
allele frequency `p` after selection, `p(1 + s)/(1 + p s)`.
"""
function wright_fisher(N::Integer; s = 0)
    s = toterm(s)
    P = Term[ZERO for _ in 0:N, _ in 0:N]
    for i in 0:N
        p = toterm(i // N)
        ps = simplify(p * (1 + s) / (1 + p * s))
        for j in 0:N
            P[i+1, j+1] = simplify(binomial(big(N), big(j)) * _pow(ps, Num(j)) * _pow(1 - ps, Num(N - j)))
        end
    end
    return P
end

# ---- diffusion approximations ---------------------------------------------------------

_quiet(f) = (_SOLVE_WARN[] = false; try f() finally _SOLVE_WARN[] = true end)

# exp(Σ cᵢ log uᵢ + rest) = Π uᵢ^cᵢ exp(rest)
function _exp_logs(arg::Term)
    pows, rest = Term[], Term[]
    for t in _summands(expand(arg))
        if t isa Fn && t.head === :log
            push!(pows, t.args[1])
            continue
        elseif t isa Mul
            i = findfirst(f -> f.first isa Fn && f.first.head === :log && f.second == ONE, t.factors)
            if i !== nothing
                u = t.factors[i].first.args[1]
                c = _mul(Term[Num(t.c); [_pow(b, e) for (j, (b, e)) in enumerate(t.factors) if j != i]])
                if isempty(_collect_sub!(Term[], y -> y isa Fn && y.head === :log, c))
                    push!(pows, _pow(u, c))
                    continue
                end
            end
        end
        push!(rest, t)
    end
    return _mul(vcat(pows, Term[_exp(_add(rest))]))
end

# ψ(y) = exp(-∫ 2M/V dy)
_scale_density(M, V, p::Sym) = simplify(_exp_logs(-integrate(simplify(2 * toterm(M) / toterm(V)), p)))

"""
    diffusion_fixation(M, V, p)

The probability of fixation from frequency `p` for a diffusion with mean
change `M(p)` and variance `V(p)` per unit time (absorbing at 0 and 1):
`u(p) = ∫₀ᵖ ψ / ∫₀¹ ψ` with `ψ(y) = exp(-∫ 2M/V dy)` (Kimura).

    @syms p::(0, 1) s::positive N::positive
    diffusion_fixation(s * p * (1 - p), p * (1 - p) / N, p)
    # (1 - exp(-2Ns p))/(1 - exp(-2Ns))
"""
function diffusion_fixation(M, V, p::Sym)
    ψ = _scale_density(M, V, p)
    Ψ = integrate(ψ, p)
    _hasintegral(Ψ) && throw(ArgumentError("diffusion_fixation: could not integrate $ψ"))
    Ψ0 = _atside(Ψ, p, ZERO)
    Ψ1 = _atside(Ψ, p, ONE)
    return simplify((Ψ - Ψ0) / (Ψ1 - Ψ0))
end

"""
    diffusion_stationary(M, V, p; normalize = true)

The stationary density `φ(p) ∝ exp(∫ 2M/V dp)/V` of a diffusion on `(0, 1)`
(for example mutation–drift balance, a beta density), normalised to integrate
to one when the integral can be found.
"""
function diffusion_stationary(M, V, p::Sym; normalize::Bool = true)
    φ = simplify(_exp_logs(integrate(simplify(2 * toterm(M) / toterm(V)), p)) / toterm(V))

    normalize || return φ
    Z = integrate(φ, p, 0, 1)
    (Z isa Fn && Z.head === :Integral) && return φ
    return simplify(φ / Z)
end

"""
    diffusion_time(M, V, p)

The expected time until absorption (at 0 or 1) from frequency `p`: the
solution of `M T' + (V/2) T'' = -1` with `T(0) = T(1) = 0`.

    @syms p::(0, 1) N::positive
    diffusion_time(0, p * (1 - p) / N, p)      # -2N(p log p + (1 - p) log(1 - p))
"""
function diffusion_time(M, V, p::Sym)
    T = UFun(gensym(:T))
    eq = toterm(M) * diff(T(p), p) + toterm(V) / 2 * diff(T(p), p, 2) ~ -1
    return dsolve(eq, T(p); bc = [T(0) => 0, T(1) => 0])
end
