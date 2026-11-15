# Recurrence equations (discrete-time models).

_initial(n::Sym) = Sym(Symbol(n.name, "₀"), n.info)

"""
    rsolve(f, n, t; ic = n₀)

Solve the first-order recurrence `n(t+1) = f(n)` for `n(t)`. The initial
value defaults to the symbol `n₀` (named after `n`). Handles:

- linear maps `a n + b` (`n(t) = n̂ + (n₀ - n̂) aᵗ`, or `n₀ + b t` when `a = 1`);
- linear-fractional (Möbius) maps `(a n + b)/(c n + d)`, through `x = 1/n`
  after moving a fixed point to zero; this covers the Beverton–Holt model
  and haploid selection.

    rsolve([f₁, f₂], [x, y], t; ic = [x₀, y₀])

A linear system `n(t+1) = A n + b`, by diagonalisation ([`matpow`](@ref)).
"""
function rsolve(f, n::Sym, t::Sym; ic = nothing)
    f = toterm(f)
    n0 = ic === nothing ? _initial(n) : toterm(ic)
    r = _rsolve1(f, n, t, n0)
    r === nothing && throw(ArgumentError("rsolve: cannot solve n(t+1) = $f"))
    return simplify(r)
end

function _rsolve1(f::Term, n::Sym, t::Sym, n0::Term)
    has(f, t) && return nothing
    cs = polycoeffs(f, n)
    if cs !== nothing && length(cs) <= 2
        length(cs) == 1 && return cs[1]   # constant map
        b, a = cs
        iszero(simplify(a - 1)) && return n0 + b * t
        ns = simplify(b / (1 - a))
        return ns + (n0 - ns) * _pow(a, t)
    end
    g = cancel(f)
    num, den = numerator(g), denominator(g)
    nc, dc = polycoeffs(num, n), polycoeffs(den, n)
    (nc === nothing || dc === nothing || length(nc) > 2 || length(dc) != 2) && return nothing
    b = nc[1]
    a = length(nc) == 2 ? nc[2] : ZERO
    d, c = dc
    if iszero(b)
        # x = 1/n: x(t+1) = c/a + (d/a) x
        x = Sym(gensym(:x), _REAL)
        xs = _rsolve1(c / a + (d / a) * x, x, t, _pow(n0, MONE))
        xs === nothing && return nothing
        return cancel(_pow(xs, MONE))
    end
    # move a fixed point to zero: n = m + n̂
    fps = solve(n * (c * n + d) - (a * n + b), n)
    isempty(fps) && return nothing
    ns = fps[1]
    m = Sym(gensym(:m), _REAL)
    fm = cancel(subs(f, n => m + ns) - ns)
    ms = _rsolve1(fm, m, t, n0 - ns)
    ms === nothing && return nothing
    return ms + ns
end

function rsolve(F::AbstractVector, ns::AbstractVector, t::Sym; ic = nothing)
    F = Term[toterm(f) for f in F]
    A = jacobian(F, ns)
    any(a -> has_any(a, ns) || has(a, t), A) && throw(ArgumentError("rsolve: only linear systems with constant coefficients are supported"))
    zero_ = Dict{Term,Term}(v => ZERO for v in ns)
    b = Term[simplify(subs(f, zero_)) for f in F]
    n0 = ic === nothing ? Term[_initial(v) for v in ns] : Term[toterm(v) for v in ic]
    k = length(ns)
    IA = Term[(i == j ? ONE : ZERO) - A[i, j] for i in 1:k, j in 1:k]
    nstar = all(iszero, b) ? _tzeros(k) : IA \ b
    P = matpow(A, t)
    return Term[simplify(x) for x in nstar + P * (n0 - nstar)]
end

# ---- equations in an undefined function --------------------------------------------

"""
    rsolve(eq, n(t); ic = [n(0), n(1), …], bc = [n(a) => va, n(b) => vb])

Solve a recurrence written as an equation in the undefined function `n` (see
[`@funs`](@ref)) at shifted arguments `n(t + k)`:

- linear with constant coefficients, of any order, `Σ aₖ n(t + k) = g(t)` with
  `g` a sum of polynomial × geometric terms (characteristic roots, repeated
  roots giving `tʲ rᵗ`, undetermined coefficients for `g`);
- first order and linear with coefficients depending on `t`,
  `n(t + 1) = a(t) n(t) + b(t)` (through [`product`](@ref) and
  [`summation`](@ref));
- first order and nonlinear, as `rsolve(f, n, t)`.

`ic` gives the values at `t = 0, 1, …, order - 1`; `bc` gives values at any
points (boundary values, as for fixation probabilities). Without them the
solution has constants `C₁, C₂, …`.

    @funs x
    @syms i::natural N::natural r::positive
    rsolve(x(i + 1) - (1 + r) * x(i) + r * x(i - 1) ~ 0, x(i); bc = [x(0) => 0, x(N) => 1])
    # (1 - r^i)/(1 - r^N)
"""
function rsolve(eq::Eqn, nf::Fn; ic = nothing, bc = nothing)
    length(nf.args) == 1 && nf.args[1] isa Sym || throw(ArgumentError("rsolve: expected n(t) with a symbol t"))
    t = nf.args[1]
    F = eq.lhs - eq.rhs
    apps = _collect_sub!(Term[], z -> z isa Fn && z.head === nf.head, F)
    shifts = Int[]
    for a in apps
        d = _intbound(cancel(a.args[1] - t))
        d === nothing && throw(ArgumentError("rsolve: $a is not $(nf.head) at t plus an integer"))
        push!(shifts, d)
    end
    isempty(shifts) && throw(ArgumentError("rsolve: $(nf.head) does not occur in $eq"))
    lo = minimum(shifts)
    order = maximum(shifts) - lo
    order == 0 && throw(ArgumentError("rsolve: no shift of $(nf.head) in $eq"))
    # shift so the lowest term is n(t)
    lo != 0 && (F = subs(F, t => t - lo))
    Ys = [Sym(gensym(:Y), _REAL) for _ in 0:order]
    G = subs(F, Dict{Term,Term}(Fn(nf.head, Term[t + k]) => Ys[k+1] for k in 0:order))
    sol, consts = _rsolve_n(G, Ys, t, nf)
    sol === nothing && throw(ArgumentError("rsolve: cannot solve $eq"))
    conds = Term[]
    if ic !== nothing
        for (k, v) in enumerate(ic)
            push!(conds, subs(sol, t => k - 1) - toterm(v))
        end
    end
    if bc !== nothing
        for (l, v) in bc
            l isa Fn && l.head === nf.head || throw(ArgumentError("rsolve: boundary values are written $(nf.head)(a) => value"))
            push!(conds, subs(sol, t => l.args[1]) - toterm(v))
        end
    end
    isempty(conds) && return simplify(sol)
    cs = solve(conds, consts)
    isempty(cs) && throw(ArgumentError("rsolve: the conditions cannot be satisfied"))
    return simplify(subs(sol, cs[1]))
end

# G(Y0, …, Ym) = 0 with Yk = n(t + k); returns (solution, constants)
function _rsolve_n(G::Term, Ys, t::Sym, nf::Fn)
    m = length(Ys) - 1
    cs = Term[]
    rest = G
    for Y in Ys
        c = polycoeffs(rest, Y)
        if c === nothing || length(c) > 2 || (length(c) == 2 && any(Z -> has(c[2], Z), Ys))

            # nonlinear: only first order, through rsolve(f, n, t)
            m == 1 || return (nothing, Sym[])
            r = solve(G, Ys[2])
            length(r) == 1 || return (nothing, Sym[])
            C = _const(1)
            y = Sym(gensym(:y), _REAL)
            s = _rsolve1(subs(r[1], Ys[1] => y), y, t, C)
            s === nothing && return (nothing, Sym[])
            return (s, Sym[C])
        end
        push!(cs, length(c) == 2 ? c[2] : ZERO)
        rest = c[1]
    end
    g = simplify(-rest)                       # Σ cₖ Yₖ = g(t)
    lead = cs[end]
    a = Term[simplify(c / lead) for c in cs]
    g = simplify(g / lead)
    if any(c -> has(c, t), a)
        m == 1 || return (nothing, Sym[])
        # n(t+1) = α(t) n(t) + β(t): n(t) = P(t) (C + Σ_{s<t} β(s)/P(s+1)), P(t) = Π_{s<t} α(s)
        α, β = -a[1], g
        s = Sym(gensym(:s), SymInfo(true, true, Q(0), false, nothing, false))
        P = product(subs(α, t => s), s, 0, t - 1)
        Ps1 = subs(P, t => s + 1)

        S = iszero(β) ? ZERO : summation(simplify(subs(β, t => s) / Ps1), s, 0, t - 1)
        C = _const(1)
        return (P * (C + S), Sym[C])
    end
    # characteristic roots
    ρ = Sym(gensym(:ρ), SymInfo(false, false, nothing, false, nothing, false))
    p = _add(Term[_mul((a[k+1], _pow(ρ, Num(k)))) for k in 0:m])
    _, fs = factor_list(p)
    roots = Tuple{Term,Int}[]
    for (f, k) in fs
        has(f, ρ) || continue
        for z in _solve_factor(f, ρ)
            push!(roots, (simplify(z), k))
        end
    end
    sum(last, roots; init = 0) == m || return (nothing, Sym[])
    basis = Term[]
    for (z, k) in roots, j in 0:k-1
        push!(basis, _pow(t, Num(j)) * _pow(z, t))
    end
    consts = Sym[_const(i) for i in eachindex(basis)]
    yh = _add(Term[_mul((c, b)) for (c, b) in zip(consts, basis)])
    iszero(g) && return (yh, consts)
    yp = _rparticular(a, g, t, roots)
    yp === nothing && return (nothing, Sym[])
    return (yh + yp, consts)
end

# undetermined coefficients for g(t) = Σ P(t) zᵗ: try tᵘ Q(t) zᵗ, u the
# multiplicity of z as a characteristic root
function _rparticular(a, g::Term, t::Sym, roots)
    m = length(a) - 1
    out = Term[]
    groups = Dict{Term,Vector{Term}}()           # z => polynomial coefficients
    for term in _summands(expand(g))
        s = _split_summand(term, t)
        (s === nothing || s.kind !== :geom) && return nothing
        P = Term[s.c * c for c in s.P]
        z = s.z
        key = something(findfirst(k -> isequiv(k, z), collect(keys(groups))), 0)
        if key == 0
            groups[z] = P
        else
            z0 = collect(keys(groups))[key]
            old = groups[z0]
            n = max(length(old), length(P))
            groups[z0] = Term[(i <= length(old) ? old[i] : ZERO) + (i <= length(P) ? P[i] : ZERO) for i in 1:n]
        end
    end
    for (z, P) in groups
        μ = 0
        for (r, k) in roots
            isequiv(r, z) && (μ = k)
        end
        d = length(P) - 1
        us = [Sym(gensym(:u), SymInfo(false, false, nothing, false, nothing, false)) for _ in 0:d]
        Qt = _add(Term[_mul((us[i+1], _pow(t, Num(i + μ)))) for i in 0:d])
        # L[Q zᵗ] / zᵗ = Σ aₖ zᵏ Q(t + k)
        L = _add(Term[_mul((a[k+1], _pow(z, Num(k)), subs(Qt, t => t + k))) for k in 0:m])
        eqs = polycoeffs(expand(L - _polyval(P, t)), t)
        eqs === nothing && return nothing
        sol = solve(eqs, us)
        isempty(sol) && return nothing
        push!(out, subs(Qt, Dict{Term,Term}(u => get(sol[1], u, ZERO) for u in us)) * _pow(z, t))
    end
    return _add(out)
end
