# Exact and symbolic linear algebra on matrices of terms.
#
# Entries are kept cancelled (as single fractions) during elimination, and a
# pivot is accepted only if it is not identically zero. Generalises the exact
# Gauss–Jordan of PracticalProbability to entries in ℚ(parameters).

const TermMat = AbstractMatrix{<:Term}

"""
    symbolic(A)

`A` with every entry converted to a term (so the methods here apply to a
numeric matrix).
"""
symbolic(A::AbstractArray) = Term[toterm(x) for x in A]      # Array{Term}, so entries can become any term


_c(x) = cancel(toterm(x))
_nz(x) = !iszero(_c(x))

"""
    rref(A) -> (R, pivots)

Reduced row echelon form, with the pivot columns.
"""
function rref(A::AbstractMatrix)
    R = Term[_c(a) for a in A]
    m, n = size(R)
    pivots = Int[]
    r = 1
    for c in 1:n
        r > m && break
        cands = [i for i in r:m if !iszero(R[i, c])]
        isempty(cands) && continue
        # prefer a numeric pivot, then the simplest
        p = cands[argmin([(R[i, c] isa Num ? 0 : 1, complexity(R[i, c])) for i in cands])]
        if p != r
            R[[r, p], :] = R[[p, r], :]
        end
        piv = R[r, c]
        for j in 1:n
            R[r, j] = _c(R[r, j] / piv)
        end
        for i in 1:m
            i == r && continue
            f = R[i, c]
            iszero(f) && continue
            for j in 1:n
                R[i, j] = _c(R[i, j] - f * R[r, j])
            end
        end
        push!(pivots, c)
        r += 1
    end
    return R, pivots
end

_rank(A::AbstractMatrix) = length(rref(A)[2])

"""
    nullspace(A) -> Vector of basis vectors

A basis of the null space, each vector scaled so its free entry is 1.
"""
function _nullspace(A::AbstractMatrix)
    R, piv = rref(A)
    n = size(A, 2)
    free = [j for j in 1:n if !(j in piv)]
    basis = Vector{Term}[]
    for f in free
        v = _tzeros(n)
        v[f] = ONE
        for (i, p) in enumerate(piv)
            v[p] = _c(-R[i, f])
        end
        push!(basis, v)
    end
    return basis
end

"""
    linsolve(A, b) -> Vector or nothing

The solution of `A x = b` if it is unique (or the particular solution with free
variables zero); `nothing` if the system is inconsistent.
"""
function linsolve(A::AbstractMatrix, b::AbstractVector)
    m, n = size(A)
    M = hcat(symbolic(A), symbolic(b))
    R, piv = rref(M)
    (n + 1) in piv && return nothing
    x = _tzeros(n)
    for (i, p) in enumerate(piv)
        x[p] = simplify(R[i, n+1])
    end
    return x
end


function _inv(A::AbstractMatrix)
    n = LinearAlgebra.checksquare(A)
    I_ = Term[i == j ? ONE : ZERO for i in 1:n, j in 1:n]
    R, piv = rref(hcat(A, I_))
    piv == collect(1:n) || throw(LinearAlgebra.SingularException(0))
    return Term[simplify(R[i, n+j]) for i in 1:n, j in 1:n]
end

"""
    det(A)

The determinant, by cofactor expansion up to 3×3 and fraction-free (Bareiss)
elimination beyond, then factored.
"""
function _det(A::AbstractMatrix)
    n = LinearAlgebra.checksquare(A)
    n == 0 && return ONE
    n == 1 && return simplify(A[1, 1])
    if n == 2
        return simplify(A[1, 1] * A[2, 2] - A[1, 2] * A[2, 1])
    elseif n == 3
        a = A
        d = a[1, 1] * (a[2, 2] * a[3, 3] - a[2, 3] * a[3, 2]) -
            a[1, 2] * (a[2, 1] * a[3, 3] - a[2, 3] * a[3, 1]) +
            a[1, 3] * (a[2, 1] * a[3, 2] - a[2, 2] * a[3, 1])
        return simplify(d)
    end
    M = Term[_c(a) for a in A]
    sgn = 1
    prev = ONE
    for k in 1:n-1
        if iszero(M[k, k])
            p = findfirst(i -> !iszero(M[i, k]), k+1:n)
            p === nothing && return ZERO
            p += k
            M[[k, p], :] = M[[p, k], :]
            sgn = -sgn
        end
        for i in k+1:n, j in k+1:n
            M[i, j] = _c((M[k, k] * M[i, j] - M[i, k] * M[k, j]) / prev)
        end
        prev = M[k, k]
    end
    return simplify(sgn * M[n, n])
end

_tr(A::AbstractMatrix) = simplify(sum(A[i, i] for i in 1:LinearAlgebra.checksquare(A)))

"""
    charpoly(A, λ)

The characteristic polynomial `det(λI - A)`, collected in `λ`.
"""
function charpoly(A::AbstractMatrix, λ::Sym)
    cs = charcoeffs(A)
    n = length(cs) - 1
    return collect(_add(Term[_mul((cs[k+1], _pow(λ, Num(n - k)))) for k in 0:n]), λ)
end

"""
    charcoeffs(A) -> [1, a₁, …, aₙ]

The coefficients of the monic characteristic polynomial
`λⁿ + a₁λⁿ⁻¹ + … + aₙ` (Faddeev–LeVerrier).
"""
function charcoeffs(A::AbstractMatrix)
    A = symbolic(A)
    n = LinearAlgebra.checksquare(A)
    cs = Term[ONE]
    M = Term[ZERO for _ in 1:n, _ in 1:n]
    for k in 1:n
        M = Term[_c(x) for x in A * M]
        for i in 1:n
            M[i, i] = _c(M[i, i] + cs[end])
        end
        AM = A * M
        ak = _c(-sum(AM[i, i] for i in 1:n) / k)
        push!(cs, ak)
    end
    return Term[simplify(c) for c in cs]
end

"""
    eigvals(A) -> Vector{Term}

The eigenvalues, with repetition for repeated roots. Triangular matrices are
read off; otherwise the characteristic polynomial is factored and solved.
"""
function _eigvals(A::AbstractMatrix)
    n = LinearAlgebra.checksquare(A)
    if all(iszero(_c(A[i, j])) for i in 1:n, j in 1:n if i > j) ||
       all(iszero(_c(A[i, j])) for i in 1:n, j in 1:n if i < j)
        return Term[simplify(A[i, i]) for i in 1:n]
    end
    λ = Sym(gensym(:λ), SymInfo(false, false, nothing, false, nothing, false))
    cs = charcoeffs(A)
    p = _add(Term[_mul((cs[k+1], _pow(λ, Num(n - k)))) for k in 0:n])
    _, fs = factor_list(p)
    vals = Term[]
    for (f, k) in fs
        has(f, λ) || continue
        rs = _solve_factor(f, λ)
        for r in rs, _ in 1:k
            push!(vals, simplify(r))
        end
    end
    return vals
end

"""
    eigen(A) -> (values = ..., vectors = ...)

Distinct eigenvalues with a basis of right eigenvectors for each (as columns of
one matrix, in the same order as the values, a value repeated once per vector).
"""
function _eigen(A::AbstractMatrix)
    vals = _dedupe(_eigvals(A))
    n = size(A, 1)
    vs, vecs = Term[], Vector{Term}[]
    for λ in vals
        B = Term[A[i, j] - (i == j ? λ : ZERO) for i in 1:n, j in 1:n]
        for v in _nullspace(B)
            push!(vs, λ)
            push!(vecs, Term[simplify(x) for x in v])
        end
    end
    V = isempty(vecs) ? Matrix{Term}(undef, n, 0) : reduce(hcat, vecs)
    return (values = vs, vectors = V)
end

_eigvecs(A::AbstractMatrix) = _eigen(A).vectors

"""
    left_eigvec(A, λ) -> Vector

A left eigenvector (`v' A = λ v'`) for the eigenvalue `λ`.
"""
function left_eigvec(A::AbstractMatrix, λ)
    n = size(A, 1)
    B = Term[A[j, i] - (i == j ? toterm(λ) : ZERO) for i in 1:n, j in 1:n]
    ns = _nullspace(B)
    isempty(ns) && throw(ArgumentError("left_eigvec: $λ is not an eigenvalue"))
    return Term[simplify(x) for x in ns[1]]
end

"""
    right_eigvec(A, λ) -> Vector

A right eigenvector (`A w = λ w`) for the eigenvalue `λ`.
"""
function right_eigvec(A::AbstractMatrix, λ)
    n = size(A, 1)
    B = Term[A[i, j] - (i == j ? toterm(λ) : ZERO) for i in 1:n, j in 1:n]
    ns = _nullspace(B)
    isempty(ns) && throw(ArgumentError("right_eigvec: $λ is not an eigenvalue"))
    return Term[simplify(x) for x in ns[1]]
end

# ---- functions of a matrix ------------------------------------------------------------

function _diagonalise(A::AbstractMatrix)
    A = symbolic(A)
    e = _eigen(A)
    n = size(A, 1)
    size(e.vectors, 2) == n || throw(ArgumentError("the matrix is not diagonalisable (repeated eigenvalue with too few eigenvectors)"))
    return e.values, e.vectors, inv(e.vectors)
end

"""
    matpow(A, t)

`Aᵗ` for a symbolic `t`, by diagonalisation: `P diag(λᵢᵗ) P⁻¹`. The
matrix must be diagonalisable.
"""
function matpow(A::AbstractMatrix, t)
    t isa Integer && return symbolic(A)^t
    A = symbolic(A)
    d = _safe(_diagonalise, A)
    d === nothing && return _realmatrix(_putzer(A, toterm(t), false), A, t)
    vals, P, Pi = d
    D = Term[i == j ? _pow(vals[i], toterm(t)) : ZERO for i in eachindex(vals), j in eachindex(vals)]
    return _realmatrix(Term[simplify(x) for x in P * D * Pi], A, t)
end

"""
    matexp(A, t = 1)

The matrix exponential `exp(A t)`, by diagonalisation.
"""
function matexp(A::AbstractMatrix, t = 1)
    A = symbolic(A)
    d = _safe(_diagonalise, A)
    d === nothing && return _realmatrix(_putzer(A, toterm(t), true), A, t)
    vals, P, Pi = d
    D = Term[i == j ? _exp(vals[i] * toterm(t)) : ZERO for i in eachindex(vals), j in eachindex(vals)]
    return _realmatrix(Term[simplify(x) for x in P * D * Pi], A, t)
end

# Putzer's algorithm, for any matrix whose eigenvalues λ₁…λₙ are known:
# f(A) = Σₖ rₖ Pₖ₋₁ with P₀ = I, Pₖ = (A - λₖI)Pₖ₋₁ and, for exp(At),
# r₁ = e^(λ₁t), rₖ(t) = ∫₀ᵗ e^(λₖ(t-s)) rₖ₋₁(s) ds; for Aᵗ, r₁ = λ₁ᵗ,
# rₖ(t) = Σ_{s<t} λₖ^(t-1-s) rₖ₋₁(s)
function _putzer(A::AbstractMatrix, t::Term, continuous::Bool)
    n = size(A, 1)
    λs = _eigvals(A)
    length(λs) == n || throw(ArgumentError("matrix function: the eigenvalues could not be found"))
    τ = Sym(gensym(:τ), SymInfo(true, !continuous, Q(0), false, nothing, false))
    s = Sym(gensym(:s), SymInfo(true, !continuous, Q(0), false, nothing, false))
    r = Term[continuous ? _exp(λs[1] * τ) : _pow(λs[1], τ)]
    for k in 2:n
        prev = subs(r[k-1], τ => s)
        rk = continuous ? integrate(_exp(λs[k] * (τ - s)) * prev, s, 0, τ) :
             summation(_pow(λs[k], τ - 1 - s) * prev, s, 0, τ - 1)
        (rk isa Fn && rk.head in (:Integral, :Sum)) && throw(ArgumentError("matrix function: Putzer's algorithm failed"))
        push!(r, simplify(rk))
    end
    Pk = Term[i == j ? ONE : ZERO for i in 1:n, j in 1:n]
    M = Term[ZERO for _ in 1:n, _ in 1:n]
    for k in 1:n
        M = M + r[k] * Pk
        k < n && (Pk = (A - λs[k] * Term[i == j ? ONE : ZERO for i in 1:n, j in 1:n]) * Pk)
    end
    return Term[simplify(subs(x, τ => t)) for x in M]
end

# a real matrix has a real exponential and real powers: rewrite complex
# exponentials and powers through cos and sin
function _realmatrix(M, A, t)
    all(x -> _isreal_struct(x), A) && _isreal_struct(toterm(t)) || return M
    any(x -> has(x, IM), M) || return M
    return Term[has(x, IM) ? realform(x) : x for x in M]

end


# ---- stability criteria -----------------------------------------------------------

function _hurwitz_det(b, k::Int)
    # b[1] = b0 (leading), b[i+1] = b_i; H[i,j] = b_{2j-i}
    n = length(b) - 1
    get_b(m) = (0 <= m <= n) ? b[m+1] : ZERO
    H = Term[get_b(2j - i) for i in 1:k, j in 1:k]
    return _det(H)
end

# conditions (as terms that must be > 0) for b0 zⁿ + b1 zⁿ⁻¹ + … + bn to have
# all roots in the open left half-plane, given b0 > 0 (Liénard–Chipart)
function _lienard_chipart(b)
    n = length(b) - 1
    conds = Term[b[i+1] for i in 1:n]
    k = n - 1
    while k >= 2
        push!(conds, _hurwitz_det(b, k))
        k -= 2
    end
    return conds
end

function _conds(xs)
    out = Any[]
    for x in xs
        c = simplify(Rel(:>, simplify(x), ZERO))
        push!(out, c)
    end
    return _and(out)
end

"""
    routh_hurwitz(A) / routh_hurwitz(coeffs)

The conditions for all eigenvalues of `A` (or all roots of the monic polynomial
with coefficients `[1, a₁, …, aₙ]`) to have negative real part: local
stability of an equilibrium of a continuous-time model with Jacobian `A`.
Returned as a condition (simplified under the assumptions; `true`/`false` when
decided). For 2×2 this is `tr(A) < 0` and `det(A) > 0`.
"""
routh_hurwitz(A::AbstractMatrix) = routh_hurwitz(charcoeffs(A))
routh_hurwitz(cs::AbstractVector) = _conds(_lienard_chipart(Term[toterm(c) for c in cs]))

"""
    jury(A) / jury(coeffs)

The conditions for all eigenvalues of `A` (or roots of the monic polynomial
`[1, a₁, …, aₙ]`) to lie inside the unit circle: local stability of an
equilibrium of a discrete-time model with Jacobian `A`. For 2×2:
`|det A| < 1` and `|tr A| < 1 + det A`.
"""
jury(A::AbstractMatrix) = jury(charcoeffs(A))
function jury(cs::AbstractVector)
    a = Term[toterm(c) for c in cs]
    n = length(a) - 1
    # bilinear transform λ = (1 + z)/(1 - z): q(z) = Σ aₖ (1+z)^(n-k) (1-z)^k
    z = Sym(gensym(:z), SymInfo(true, false, nothing, false, nothing, false))
    q = expand(_add(Term[_mul((a[k+1], _pow(_add((ONE, z)), Num(n - k)), _pow(_add((ONE, -z)), Num(k)))) for k in 0:n]))
    qc = polycoeffs(q, z)
    b = Term[cancel(qc[n-i+1]) for i in 0:n]   # b[1] = leading
    return _conds(vcat(Term[b[1]], _lienard_chipart(b)))
end

# Methods on the LinearAlgebra functions, for both abstract and dense term
# matrices (the dense ones avoid ambiguities with LinearAlgebra's own).
for M in (:(AbstractMatrix{<:Term}), :(Matrix{<:Term}))
    @eval begin
        LinearAlgebra.det(A::$M) = _det(A)
        LinearAlgebra.inv(A::$M) = _inv(A)
        LinearAlgebra.tr(A::$M) = _tr(A)
        LinearAlgebra.rank(A::$M) = _rank(A)
        LinearAlgebra.nullspace(A::$M) = _nullspace(A)
        LinearAlgebra.eigvals(A::$M) = _eigvals(A)
        LinearAlgebra.eigen(A::$M) = _eigen(A)
        LinearAlgebra.eigvecs(A::$M) = _eigvecs(A)
        Base.:\(A::$M, b::AbstractVector) = linsolve(A, b)
    end
end
