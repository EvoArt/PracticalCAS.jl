# Evolutionary game theory: symmetric matrix games, Nash equilibria, ESS,
# replicator dynamics.

"""
    MatrixGame(A; strategies = ["1", "2", …])

A symmetric two-player game where `A[i, j]` is the payoff to strategy `i`
against strategy `j`.
"""
struct MatrixGame
    A::Matrix{Term}
    strategies::Vector{String}
end
MatrixGame(A::AbstractMatrix; strategies = [string(i) for i in 1:size(A, 1)]) =
    MatrixGame(Term[toterm(a) for a in A], String[string(s) for s in strategies])

"""
    hawk_dove(V, C)

The Hawk–Dove game with resource value `V` and cost of fighting `C`.
"""
hawk_dove(V, C) = MatrixGame([(toterm(V) - C)/2 toterm(V); ZERO toterm(V)/2]; strategies = ["Hawk", "Dove"])

"""
    payoff(G, x, y)

The expected payoff `xᵀ A y` of mixed strategy `x` against `y`.
"""
payoff(G::MatrixGame, x::AbstractVector, y::AbstractVector) = simplify(sum(x[i] * G.A[i, j] * y[j] for i in eachindex(x), j in eachindex(y)))

"""
    GameEquilibrium

A candidate equilibrium of a matrix game: the strategy (as frequencies), its
support, the condition under which it is a Nash equilibrium or an ESS (simplified
under the assumptions) and whether it holds (`true`, `false`, `nothing` if it
depends on the parameters).
"""
struct GameEquilibrium
    game::MatrixGame
    x::Vector{Term}
    support::Vector{Int}
    condition::CondLike
    holds::Union{Bool,Nothing}
    kind::Symbol
end

function Base.show(io::IO, e::GameEquilibrium)
    s = e.game.strategies
    if length(e.support) == 1
        print(io, e.kind === :ess ? "ESS" : "Nash equilibrium", " (pure ", s[e.support[1]], ")")
    else
        print(io, e.kind === :ess ? "ESS" : "Nash equilibrium", " (mixed: ",
            join(("$(s[i]) = $(e.x[i])" for i in e.support), ", "), ")")
    end
    print(io, " when ", e.condition)
end

function _supports(n::Int)
    out = Vector{Int}[]
    for mask in 1:(2^n-1)
        push!(out, [i for i in 1:n if (mask >> (i - 1)) & 1 == 1])
    end
    sort!(out; by = length)
    return out
end

# the equaliser on support S: (A x)_i equal for i ∈ S, Σ x = 1
function _equaliser(A, S)
    n = size(A, 1)
    k = length(S)
    if k == 1
        x = _tzeros(n)
        x[S[1]] = ONE
        return x
    end
    M = Term[]
    rows = Vector{Term}[]
    for a in 2:k
        push!(rows, Term[A[S[1], S[j]] - A[S[a], S[j]] for j in 1:k])
    end
    push!(rows, Term[ONE for _ in 1:k])
    Mm = Term[rows[i][j] for i in 1:k, j in 1:k]
    rhs = vcat(_tzeros(k - 1), Term[ONE])
    rank(Mm) == k || return nothing
    xs = linsolve(Mm, rhs)
    xs === nothing && return nothing
    x = _tzeros(n)
    for (j, i) in enumerate(S)
        x[i] = xs[j]
    end
    return x
end

function _candidate(G::MatrixGame, S, strict::Bool)
    A = G.A
    n = size(A, 1)
    x = _equaliser(A, S)
    x === nothing && return nothing
    Ax = Term[simplify(sum(A[i, j] * x[j] for j in 1:n)) for i in 1:n]
    conds = Any[]
    if length(S) > 1
        for i in S
            push!(conds, Rel(:>, x[i], ZERO))
        end
    end
    for k in 1:n
        k in S && continue
        push!(conds, Rel(strict ? :< : :<=, Ax[k], Ax[S[1]]))
    end
    return x, Ax, conds
end

"""
    nash(G) -> Vector{GameEquilibrium}

The symmetric Nash equilibria of the game, by support enumeration, each with
the condition on the parameters under which it is one. Candidates that are
never equilibria are dropped.
"""
function nash(G::MatrixGame)
    out = GameEquilibrium[]
    for S in _supports(size(G.A, 1))
        c = _candidate(G, S, false)
        c === nothing && continue
        x, _, conds = c
        cond = simplify(_and(conds))
        h = decide(cond)
        h === false && continue
        push!(out, GameEquilibrium(G, x, S, cond, h, :nash))
    end
    return out
end

"""
    ess(G) -> Vector{GameEquilibrium}

The evolutionarily stable strategies of the game, each with the condition on
the parameters under which it is one (Maynard Smith's conditions for pure
strategies; for a mixed strategy with support `S`, positive frequencies,
strictly lower payoff to strategies outside `S`, and `zᵀ A z < 0` for every
`z ≠ 0` with `Σz = 0` on `S`). Candidates that are never ESSs are dropped.

    @syms V::positive C::positive
    ess(hawk_dove(V, C))     # pure Hawk when V ≥ C; mixed Hawk = V/C when V < C
"""
function ess(G::MatrixGame)
    A = G.A
    n = size(A, 1)
    out = GameEquilibrium[]
    for S in _supports(n)
        if length(S) == 1
            i = S[1]
            x = _tzeros(n)
            x[i] = ONE
            conds = Any[]
            for j in 1:n
                j == i && continue
                strict = Rel(:>, A[i, i], A[j, i])
                tie = _and(Any[eq(A[i, i], A[j, i]), Rel(:>, A[i, j], A[j, j])])
                push!(conds, _or(Any[strict, tie]))
            end
            cond = simplify(_and(conds))
            h = decide(cond)
            h === false && continue
            push!(out, GameEquilibrium(G, x, S, cond, h, :ess))
            continue
        end
        c = _candidate(G, S, true)
        c === nothing && continue
        x, _, conds = c
        # negative definiteness on the tangent space of the support
        k = length(S)
        Z = Term[(S[i] == j ? ONE : (j == S[end] ? MONE : ZERO)) for j in 1:n, i in 1:k-1]
        B = transpose(Z) * A * Z
        Bs = Term[simplify(-(B[i, j] + B[j, i]) / 2) for i in 1:k-1, j in 1:k-1]
        for m in 1:k-1
            push!(conds, Rel(:>, det(Bs[1:m, 1:m]), ZERO))
        end
        cond = simplify(_and(conds))
        h = decide(cond)
        h === false && continue
        push!(out, GameEquilibrium(G, x, S, cond, h, :ess))
    end
    return out
end

"""
    replicator(G, xs = nothing) -> ODEModel

The replicator dynamics `ẋᵢ = xᵢ((A x)ᵢ - xᵀ A x)` of the game, in the first
`n - 1` frequencies (`xₙ = 1 - Σ xᵢ`). For two strategies this is
`ṗ = p (1 - p) ((A x)₁ - (A x)₂)`. Frequencies default to symbols `x₁, x₂, …`
in `[0, 1]`.
"""
function replicator(G::MatrixGame, xs = nothing)
    A = G.A
    n = size(A, 1)
    vars = xs === nothing ? [sym(Symbol("x", Char(0x2080 + i)); lo = 0, hi = 1, lo_open = false, hi_open = false) for i in 1:n-1] : Sym[x for x in xs]
    length(vars) == n - 1 || throw(ArgumentError("replicator: give n - 1 = $(n-1) frequency symbols"))
    x = vcat(Term[v for v in vars], Term[ONE - sum(vars)])
    Ax = Term[sum(A[i, j] * x[j] for j in 1:n) for i in 1:n]
    mean = sum(x[i] * Ax[i] for i in 1:n)
    rhs = Term[factor(simplify(x[i] * (Ax[i] - mean))) for i in 1:n-1]
    return ODEModel(vars, rhs)
end
