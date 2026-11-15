# Ordinary differential equations.

const _REAL = SymInfo(true, false, nothing, false, nothing, false)
_const(i::Int) = Sym(Symbol("C", join(Char(0x2080 + d) for d in reverse(digits(i)))), _REAL)

"""
    dsolve(rhs, y, t; ic = nothing, t0 = 0)

Solve the first-order equation `dy/dt = rhs` (in the symbols `y` and `t`).
Without `ic` the solution contains the constant `C₁`; with `ic = y₀` it
satisfies `y(t0) = y₀`. Tries, in order: direct integration, linear equations
(integrating factor), Bernoulli equations, separable equations. Returns the
solution `y(t)`, or a vector when the implicit solution has several branches.

    @syms n::positive r::positive K::positive t n₀::positive
    dsolve(r*n*(1 - n/K), n, t; ic = n₀)     # K*n₀/(n₀ + (K - n₀)*exp(-r*t))

    dsolve(eq, y(t); ic = (t0, [y0, y0′, …]), bc = [y(a) => ya, y(b) => yb])

Solve an equation in the undefined function `y` (see [`@funs`](@ref)) and its
derivatives `D(y(t), t, k)`: first order as above, linear equations with
constant coefficients (after dividing by the leading coefficient), and
equations without `y` itself (reduced in order). `bc` gives boundary values,
as needed for fixation probabilities from a backward equation.

    dsolve([rhs₁, rhs₂], [x, y], t; ic = [x₀, y₀])

A linear system with constant coefficients, `y' = A y + b`, by
diagonalisation (see [`matexp`](@ref)).
"""
function dsolve(rhs, y::Sym, t::Sym; ic = nothing, t0 = 0)
    f = toterm(rhs)
    sols = _dsolve1(f, y, t)
    sols === nothing && throw(ArgumentError("dsolve: cannot solve dy/dt = $f"))
    if ic !== nothing
        C = _const(1)
        out = Term[]
        for s in sols
            cs = _solve1(subs(s, t => t0) - toterm(ic), C)
            for c in cs
                push!(out, simplify(subs(s, C => c)))
            end
        end
        out = _dedupe(out)
        # keep the branches that really pass through the initial value
        out = filter(s -> isequiv(subs(s, t => t0), ic), out)
        sols = out
    end
    return length(sols) == 1 ? sols[1] : sols
end

function _dsolve1(f::Term, y::Sym, t::Sym)
    C = _const(1)
    if !has(f, y)
        F = integrate(f, t)
        return Term[F + C]
    end
    cs = polycoeffs(f, y)
    if cs !== nothing && length(cs) == 2 && !has(cs[1], y) && !has(cs[2], y)
        b, a = cs
        if !has(a, t) && !has(b, t)
            iszero(a) && return Term[b * t + C]
            return Term[simplify(-b / a + C * _exp(a * t))]
        end
        μ = _exp(-integrate(a, t))
        return Term[simplify((integrate(simplify(b * μ), t) + C) / μ)]
    end
    # Bernoulli: a y + b y^n
    if cs !== nothing && length(cs) >= 3
        nz = [k - 1 for k in eachindex(cs) if !iszero(cs[k])]
        if length(nz) == 2 && nz[1] == 1
            nexp = nz[2]
            a, b = cs[2], cs[nexp+1]
            v = Sym(gensym(:v), _REAL)
            vs = _dsolve1((1 - nexp) * (a * v + b), v, t)
            vs === nothing && return nothing
            return Term[simplify(_pow(s, Num(Q(1) // (1 - nexp)))) for s in vs]
        end
    end
    # separable: g(t) h(y)
    c, fs = factor_list(f)
    gt, hy = Term[c], Term[]
    for (g, k) in fs
        ht, hyy = has(g, t), has(g, y)
        ht && hyy && return nothing
        (hyy ? hy : gt) |> v -> push!(v, _pow(g, Num(k)))
    end
    H = integrate(_pow(_mul(hy), MONE), y)
    G = integrate(_mul(gt), t)
    (H isa Fn && H.head === :Integral) && return nothing
    (G isa Fn && G.head === :Integral) && return nothing
    _SOLVE_WARN[] = false
    sols = try
        solve(H - G - C, y)
    finally
        _SOLVE_WARN[] = true
    end
    isempty(sols) && return nothing
    return sols
end

# ---- equations in an undefined function -------------------------------------------

function dsolve(eq::Eqn, yf::Fn; ic = nothing, bc = nothing)
    t = yf.args[1]
    t isa Sym || throw(ArgumentError("dsolve: expected y(t) with a symbol t"))
    F = eq.lhs - eq.rhs
    derivs = _collect_sub!(Term[], z -> z isa Deriv && z.f == yf, F)
    order = isempty(derivs) ? 0 : maximum(sum(k for (_, k) in d.vars) for d in derivs)
    order == 0 && throw(ArgumentError("dsolve: no derivative of $yf in $eq"))
    Ys = [Sym(gensym(:Y), _REAL) for _ in 0:order]
    d = Dict{Term,Term}(yf => Ys[1])
    for dd in derivs
        d[dd] = Ys[sum(k for (_, k) in dd.vars)+1]
    end
    G = subs(F, d)
    sol, consts = _dsolve_n(G, Ys, t)
    sol === nothing && throw(ArgumentError("dsolve: cannot solve $eq"))
    conds = Term[]
    if ic !== nothing
        t0, vals = ic
        for (k, v) in enumerate(vals)
            push!(conds, _atside(diff(sol, t, k - 1), t, toterm(t0)) - toterm(v))
        end
    end
    if bc !== nothing
        for (lhs, v) in bc
            lhs isa Fn && lhs.head === yf.head || throw(ArgumentError("dsolve: boundary conditions are written $(yf.head)(a) => value"))
            push!(conds, _atside(sol, t, lhs.args[1]) - toterm(v))

        end
    end
    isempty(conds) && return sol
    cs = solve(conds, consts)
    isempty(cs) && throw(ArgumentError("dsolve: the conditions cannot be satisfied"))
    return simplify(subs(sol, cs[1]))
end

# G(Y0, …, Yn) = 0 with Yk = d^k y/dt^k; returns (solution, constants)
function _dsolve_n(G::Term, Ys, t::Sym)
    n = length(Ys) - 1
    if n == 1
        r = solve(G, Ys[2])
        length(r) == 1 || return (nothing, Sym[])
        y = Sym(gensym(:y), _REAL)
        s = _dsolve1(subs(r[1], Ys[1] => y), y, t)
        (s === nothing || length(s) != 1) && return (nothing, Sym[])
        return (s[1], Sym[_const(1)])
    end
    # linear in Y0..Yn?
    cs = Term[]
    rest = G
    for Y in Ys
        c = polycoeffs(rest, Y)
        (c === nothing || length(c) > 2) && return (nothing, Sym[])
        push!(cs, length(c) == 2 ? c[2] : ZERO)
        rest = c[1]
    end
    any(c -> any(Y -> has(c, Y), Ys), cs) && return (nothing, Sym[])
    g = _mul((MONE, rest))           # Σ cₖ Yₖ = g(t)
    lead = cs[end]
    a = Term[simplify(c / lead) for c in cs]
    g = simplify(g / lead)
    if all(c -> !has(c, t), a)
        return _const_coeff(a, g, t)
    end
    # no y: reduce the order with v = y'
    if iszero(a[1])
        Gv = _add(Term[_mul((a[k+1], Ys[k])) for k in 1:n]) - g
        v, cv = _dsolve_n(Gv, Ys[1:n], t)
        v === nothing && return (nothing, Sym[])
        Cn = _const(length(cv) + 1)
        return (simplify(integrate(v, t) + Cn), vcat(cv, Sym[Cn]))
    end
    return (nothing, Sym[])
end

# y⁽ⁿ⁾ + aₙ₋₁ y⁽ⁿ⁻¹⁾ + … + a₀ y = g(t), constant aₖ
function _const_coeff(a, g::Term, t::Sym)
    n = length(a) - 1
    r = Sym(gensym(:r), SymInfo(false, false, nothing, false, nothing, false))
    p = _add(Term[_mul((a[k+1], _pow(r, Num(k)))) for k in 0:n])
    _, fs = factor_list(p)
    roots = Tuple{Term,Int}[]
    for (f, k) in fs
        has(f, r) || continue
        for z in _solve_factor(f, r)
            push!(roots, (simplify(z), k))
        end
    end
    sum(last, roots; init = 0) == n || return (nothing, Sym[])
    basis = Term[]
    used = falses(length(roots))
    for (i, (z, k)) in enumerate(roots)
        used[i] && continue
        re, im_ = _reim(z)
        if !iszero(im_) && !(re isa Fn)
            # pair with the conjugate: e^(re t) cos(im t), e^(re t) sin(im t)
            j = findfirst(jj -> !used[jj] && jj != i && isequiv(roots[jj][1], re - IM * im_), eachindex(roots))
            if j !== nothing
                used[j] = true
                for m in 0:k-1
                    push!(basis, _pow(t, Num(m)) * _exp(re * t) * _cos(im_ * t))
                    push!(basis, _pow(t, Num(m)) * _exp(re * t) * _sin(abs(im_) * t))
                end
                used[i] = true
                continue
            end
        end
        for m in 0:k-1
            push!(basis, _pow(t, Num(m)) * _exp(z * t))
        end
        used[i] = true
    end
    consts = Sym[_const(i) for i in eachindex(basis)]
    yh = _add(Term[_mul((c, b)) for (c, b) in zip(consts, basis)])
    iszero(g) && return (yh, consts)
    yp = _particular(a, g, t, roots)
    yp === nothing && (yp = _varparams(basis, g, t))
    yp === nothing && return (nothing, Sym[])
    return (simplify(yh + yp), consts)
end

# undetermined coefficients for a polynomial forcing g(t)
function _particular(a, g::Term, t::Sym, roots)
    cs = polycoeffs(g, t)
    cs === nothing && return nothing
    m = count(iszero, a[1:end-1]) == 0 ? 0 : findfirst(!iszero, a) - 1   # multiplicity of root 0
    deg = length(cs) - 1 + m
    us = [Sym(gensym(:u), SymInfo(false, false, nothing, false, nothing, false)) for _ in 0:deg]
    yp = _add(Term[_mul((us[k+1], _pow(t, Num(k)))) for k in 0:deg])
    L = _add(Term[_mul((a[k+1], diff(yp, t, k))) for k in 0:length(a)-1])
    eqs = polycoeffs(expand(L - g), t)
    sol = solve(eqs, us)
    isempty(sol) && return nothing
    s = sol[1]
    return subs(yp, Dict{Term,Term}(u => get(s, u, ZERO) for u in us))
end

# variation of parameters: y_p = Σ uᵢ yᵢ with W u' = (0, …, 0, g), W the Wronskian
function _varparams(basis, g::Term, t::Sym)
    n = length(basis)
    W = Term[diff(b, t, i - 1) for i in 1:n, b in basis]
    rhs = Term[i == n ? g : ZERO for i in 1:n]
    up = _safe(M -> linsolve(M, rhs), W)
    up === nothing && return nothing
    parts = Term[]
    for (u, b) in zip(up, basis)
        U = integrate(simplify(u), t)
        _hasintegral(U) && return nothing
        push!(parts, U * b)
    end
    yp = simplify(_add(parts))
    if !isempty(_collect_sub!(Term[], y -> y isa Fn && y.head in (:sin, :cos), yp))
        lin = _safe(trig_linearize, yp)
        lin !== nothing && complexity(lin) < complexity(yp) && (yp = lin)
    end
    return yp

end

# ---- linear systems ----

function dsolve(F::AbstractVector, ys::AbstractVector, t::Sym; ic = nothing)
    F = Term[toterm(f) for f in F]
    A = jacobian(F, ys)
    any(a -> has_any(a, ys) || has(a, t), A) && throw(ArgumentError("dsolve: only linear systems with constant coefficients are supported"))
    zero_ = Dict{Term,Term}(y => ZERO for y in ys)
    b = Term[simplify(subs(f, zero_)) for f in F]
    any(x -> has(x, t), b) && throw(ArgumentError("dsolve: only autonomous linear systems are supported"))
    y0 = ic === nothing ? [Sym(Symbol(y.name, "₀"), y.info) for y in ys] : Term[toterm(v) for v in ic]
    ystar = all(iszero, b) ? _tzeros(length(ys)) : -(symbolic(A) \ b)
    E = matexp(A, t)
    return Term[simplify(x) for x in ystar + E * (Term[toterm(v) for v in y0] - ystar)]
end
