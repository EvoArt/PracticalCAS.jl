# Integration rules: fast special cases and transformations that reduce an
# integrand to ones the complete algorithms (rational functions, Risch–Norman)
# handle, or that give the textbook form of the answer. Each method takes the
# integration context, the integrand and the variable, and returns a candidate
# antiderivative or `nothing`; the driver (integrate.jl) verifies every
# candidate by differentiating it.

const _IREAL = SymInfo(true, false, nothing, false, nothing, false)
const _IPOS = SymInfo(true, false, Q(0), true, nothing, false)
_isym(name::Symbol, info::SymInfo = _IREAL) = Sym(gensym(name), info)

# linear in x: (α, β) with u = αx + β, α ≠ 0
function _linear(u::Term, x::Sym)
    cs = polycoeffs(u, x)
    (cs === nothing || length(cs) != 2 || iszero(cs[2]) || has(cs[2], x)) && return nothing
    return (cs[2], cs[1])
end

# 1/α, with the denominator made real when α = a + b i
function _cinv(α::Term)
    has(α, IM) || return _pow(α, MONE)
    re, im = _reim(α)
    (re isa Fn && re.head === :re) && return _pow(α, MONE)
    return _mul((_add((re, _mul((MONE, IM, im)))), _pow(_add((_pow(re, TWO), _pow(im, TWO))), MONE)))
end

_factors(f::Term) = f isa Mul ? Term[_powraw(p) for p in f.factors] : Term[f]
_coef(f::Term) = f isa Mul ? Num(f.c) : ONE

# the unknowns of a polynomial identity expr ≡ 0 in x, linear in the unknowns
function _undetermined(expr::Term, unknowns::Vector{Sym}, x::Sym)
    cs = polycoeffs(expand(expr), x)
    cs === nothing && return nothing
    zero_ = Dict{Term,Term}(u => ZERO for u in unknowns)
    A = Term[coeff(c, u, 1) for c in cs, u in unknowns]
    b = Term[cancel(-subs(c, zero_)) for c in cs]
    any(a -> has(a, x), A) && return nothing
    sol = linsolve(A, b)
    sol === nothing && return nothing
    return Dict{Term,Term}(u => s for (u, s) in zip(unknowns, sol))
end

# ---- polynomials, constant factors, sums ---------------------------------------

function _im_poly(ctx, f::Term, x::Sym)
    f isa Union{Add,Mul,Pow,Sym} || return nothing
    cs = polycoeffs(f, x)
    cs === nothing && return nothing
    return _add(Term[_mul((c, _pow(x, Num(k)), Num(Q(1) // k))) for (k, c) in enumerate(cs)])
end

function _im_const(ctx, f::Term, x::Sym)
    f isa Mul || return nothing
    cs = Term[Num(f.c)]
    rest = Pair{Term,Term}[]
    for p in f.factors
        (has(p.first, x) || has(p.second, x)) ? push!(rest, p) : push!(cs, _powraw(p))
    end
    (length(cs) == 1 && isone(f.c)) && return nothing
    isempty(rest) && return _mul((f, x))
    F = _irec(ctx, _from_factors(rest), x)
    F === nothing && return nothing
    return _mul(vcat(cs, Term[F]))
end

function _im_sum(ctx, f::Term, x::Sym)
    f isa Add || return nothing
    parts = Term[]
    for s in _summands(f)
        F = _irec(ctx, s, x)
        F === nothing && return nothing
        push!(parts, F)
    end
    return _add(parts)
end

# ---- table of elementary antiderivatives with linear inner argument ------------

function _im_table(ctx, f::Term, x::Sym)
    f == x && return _mul((HALF, _pow(x, TWO)))
    if f isa Pow
        b, e = f.base, f.exp
        if !has(e, x)
            l = _linear(b, x)
            l === nothing && return nothing
            α = l[1]
            e == MONE && return _mul((_log(b), _pow(α, MONE)))
            e1 = _add((e, ONE))
            return _mul((_pow(b, e1), _cinv(_mul((e1, α)))))
        elseif !has(b, x)
            l = _linear(e, x)
            l === nothing && return nothing
            return _mul((f, _cinv(_mul((l[1], _log(b))))))
        end
        return nothing
    end
    f isa Fn && length(f.args) == 1 || return nothing
    u = f.args[1]
    l = _linear(u, x)
    l === nothing && return nothing
    ia = _cinv(l[1])
    h = f.head
    r = if h === :exp
        f
    elseif h === :sin
        -_cos(u)
    elseif h === :cos
        _sin(u)
    elseif h === :tan
        -_log(_cos(u))
    elseif h === :log
        u * _log(u) - u
    elseif h === :sinh
        _fncall(:cosh, Term[u])
    elseif h === :cosh
        _fncall(:sinh, Term[u])
    elseif h === :tanh
        _log(_fncall(:cosh, Term[u]))
    elseif h === :atan
        u * f - _log(1 + u^2) / 2
    elseif h === :asin
        u * f + sqrt(1 - u^2)
    elseif h === :acos
        u * f - sqrt(1 - u^2)
    elseif h === :erf
        u * f + _exp(-u^2) / sqrt(PI)
    elseif h === :erfi
        u * f - _exp(u^2) / sqrt(PI)
    elseif h === :Ei
        u * f - _exp(u)
    elseif h === :Si
        u * f + _cos(u)
    elseif h === :Ci
        u * f - _sin(u)
    else
        nothing
    end
    r === nothing && return nothing
    return _mul((r, ia))
end

# ---- rational functions --------------------------------------------------------

function _im_ratint(ctx, f::Term, x::Sym)
    _isratfun(f, x) || return nothing
    return _ratint(f, x)
end

# ---- integration by parts ------------------------------------------------------

_ispolyin(p::Term, x::Sym) = polycoeffs(p, x) !== nothing

function _im_parts(ctx, f::Term, x::Sym)
    f isa Mul && !isone(f.c) && return nothing
    facs = _factors(f)
    # exp(lin) * sin/cos(lin)
    if length(facs) == 2
        e = findfirst(y -> y isa Fn && y.head === :exp && _linear(y.args[1], x) !== nothing, facs)
        t = findfirst(y -> y isa Fn && y.head in (:sin, :cos) && _linear(y.args[1], x) !== nothing, facs)
        if e !== nothing && t !== nothing
            E, T = facs[e], facs[t]
            a = _linear(E.args[1], x)[1]
            b = _linear(T.args[1], x)[1]
            u = T.args[1]
            den = a^2 + b^2
            r = T.head === :sin ? (a * _sin(u) - b * _cos(u)) : (a * _cos(u) + b * _sin(u))
            return E * r / den
        end
    end
    polys = Term[y for y in facs if _ispolyin(y, x)]
    others = Term[y for y in facs if !_ispolyin(y, x)]
    length(others) == 1 || return nothing
    g = others[1]
    P = _mul(polys)
    if g isa Fn && g.head in (:exp, :sin, :cos, :sinh, :cosh) && _linear(g.args[1], x) !== nothing
        n = degree(P, x)
        (n === nothing || n > 30) && return nothing
        out = Term[]
        G = g
        Pk = P
        sgn = 1
        for k in 0:n
            G = _irec(ctx, G, x)
            G === nothing && return nothing
            push!(out, sgn * Pk * G)
            Pk = diff(Pk, x)
            sgn = -sgn
        end
        return _add(out)
    elseif g isa Fn && g.head in (:log, :atan, :asin, :acos, :erf, :erfi, :Ei, :Si, :Ci) && !isempty(polys) ||
           (g isa Pow && g.base isa Fn && g.base.head === :log && isint(g.exp) && g.exp.val > 0)
        # ∫ P g = (∫P) g - ∫ (∫P) g'
        Pi = _im_poly(ctx, P, x)
        Pi === nothing && return nothing
        rest = _irec(ctx, cancel(Pi * diff(g, x)), x)
        rest === nothing && return nothing
        return Pi * g - rest
    end
    return nothing
end

# ---- substitution (derivative divides) -----------------------------------------

# ∫ f(u) u' dx = ∫ f(U) dU, trying the inner terms u of f, largest first
function _im_subst(ctx, f::Term, x::Sym)
    cands = _collect_sub!(Term[], y -> has(y, x) && y != x, f)
    inner = Term[]
    for y in cands
        if y isa Fn
            append!(inner, y.args)
        elseif y isa Pow
            push!(inner, y.base)
            has(y.exp, x) && push!(inner, y.exp)
        elseif y isa Mul
            for (b, e) in y.factors
                e isa Num && !isint(e) && push!(inner, b)
            end
        end
        y isa Union{Fn,Pow} && push!(inner, y)
    end
    unique!(inner)
    filter!(u -> has(u, x) && u != x && _linear(u, x) === nothing, inner)
    # function applications and radicals first, then the largest
    sort!(inner; by = u -> (u isa Fn || (u isa Pow && !isint(u.exp)) ? 0 : 1, -complexity(u)))
    length(inner) > 12 && resize!(inner, 12)
    for u in inner
        du = diff(u, x)
        iszero(du) && continue
        q = _safe(z -> cancel(f / z), du)
        q === nothing && continue
        U = _isym(:U, SymInfo(_isreal_struct(u), false, nothing, false, nothing, false))
        q2 = subs(q, u => U)
        if has(q2, x)
            # try inverting u = U for x, for kernels of a linear argument
            _invertible_kernel(u, x) || continue
            xs = _safe(z -> (_SOLVE_WARN[] = false; r = _solve1(u - z, x); _SOLVE_WARN[] = true; r), U)
            _SOLVE_WARN[] = true
            (xs === nothing || length(xs) != 1) && continue
            q2 = _safe(cancel, subs(q2, x => xs[1]))
            (q2 === nothing || has(q2, x)) && continue
        end
        complexity(q2) > 3 * complexity(f) + 10 && continue
        G = _irec(ctx, q2, U)
        G === nothing && continue
        return subs(G, U => u)
    end
    return nothing
end

_invertible_kernel(u::Term, x::Sym) =
    (u isa Fn && u.head in (:exp, :log, :sin, :cos, :tan, :asin, :atan) && _linear(u.args[1], x) !== nothing) ||
    (u isa Pow && _linear(u.base, x) !== nothing && !has(u.exp, x))

# ---- Risch–Norman without trigonometric functions (they would become
# tangents of half angles; the trigonometric rules do better)
function _im_risch_notrig(ctx, f::Term, x::Sym)
    isempty(_trigatoms(f, x, (:sin, :cos, :tan))) || return nothing
    isempty(_radicals(f, x)) || return nothing
    return _risch_norman(f, x)
end

# ---- exp(quadratic) times a polynomial: erf ---------------------------------

# the single x-dependent exponential factor of a product, and the rest
function _exp_factor(f::Term, x::Sym)
    facs = _factors(f)
    i = findall(y -> y isa Fn && y.head === :exp && has(y, x), facs)
    length(i) == 1 || return nothing
    E = facs[i[1]]
    rest = _mul(Term[_coef(f); [facs[j] for j in eachindex(facs) if j != i[1]]])
    return (E.args[1], rest)
end

# ∫ exp(a x² + b x + c) dx
function _int_expquad(a::Term, b::Term, c::Term, x::Sym)
    k = _exp(simplify(c - b^2 / (4a)))
    s = x + b / (2a)
    if ispositive(a)
        r = simplify(sqrt(a))
        return _mul((k, sqrt(PI), _pow(2r, MONE), _fncall(:erfi, Term[expand(r * s)])))
    end
    r = simplify(sqrt(-a))
    return _mul((k, sqrt(PI), _pow(2r, MONE), _fncall(:erf, Term[expand(r * s)])))
end

function _im_expquad(ctx, f::Term, x::Sym)
    ef = _exp_factor(f, x)
    ef === nothing && return nothing
    u, P = ef
    cu = polycoeffs(u, x)
    (cu === nothing || length(cu) != 3) && return nothing
    c, b, a = cu
    pc = polycoeffs(P, x)
    pc === nothing && return nothing
    n = length(pc) - 1
    # P = R' + R u' + λ with deg R = n - 1
    rs = Sym[_isym(:r) for _ in 1:n]
    λ = _isym(:λ)
    R = _add(Term[_mul((r, _pow(x, Num(k - 1)))) for (k, r) in enumerate(rs)])
    sol = _undetermined(diff(R, x) + R * diff(u, x) + λ - P, vcat(rs, [λ]), x)
    sol === nothing && return nothing
    Rv = subs(R, sol)
    λv = sol[λ]
    F = _mul((Rv, _exp(u)))
    iszero(λv) && return F
    return F + λv * _int_expquad(a, b, c, x)
end

# ---- exp(linear) over a power of a linear factor: Ei ---------------------------

function _im_expei(ctx, f::Term, x::Sym)
    ef = _exp_factor(f, x)
    ef === nothing && return nothing
    u, R = ef
    l = _linear(u, x)
    l === nothing && return nothing
    α, β = l
    _isratfun(R, x) || return nothing
    R = cancel(R)
    d = denominator(R)
    has(d, x) || return nothing
    _, fs = factor_list(d)
    xf = [(g, k) for (g, k) in fs if has(g, x)]
    length(xf) == 1 || return nothing
    g, k = xf[1]
    lg = _linear(g, x)
    lg === nothing && return nothing
    r = cancel(-lg[2] / lg[1])
    k > 0 || return nothing
    y = _isym(:y)
    Ny = cancel(subs(R, x => y + r) * _pow(y, Num(k)))
    cs = polycoeffs(Ny, y)
    cs === nothing && return nothing
    dmax = length(cs) - 1 - k
    js = collect((-k + 1):max(dmax, -1))
    filter!(!=(0), js)
    push!(js, 0)
    unique!(js)
    rs = Dict{Int,Sym}(j => _isym(:r) for j in js)
    λ = _isym(:λ)
    # Σ r_j (j y^(j-1) + α y^j) + λ/y = Σ cs[i] y^(i-1-k), multiplied by y^k
    lhs = _add(Term[_mul((rj, _add((_mul((Num(j), _pow(y, Num(j - 1 + k)))), _mul((α, _pow(y, Num(j + k))))))))
                    for (j, rj) in rs])
    lhs = lhs + λ * _pow(y, Num(k - 1))
    unknowns = vcat(collect(values(rs)), [λ])
    sol = _undetermined(lhs - Ny, unknowns, y)
    sol === nothing && return nothing
    E = _exp(u)
    F = _add(Term[_mul((sol[rj], _pow(x - r, Num(j)), E)) for (j, rj) in rs])
    λv = sol[λ]
    iszero(λv) && return F
    return F + _mul((λv, _exp(cancel(α * r + β)), _fncall(:Ei, Term[expand(α * (x - r))])))
end

# ---- radicals of one linear polynomial: rationalising substitution -------------

# the x-dependent bases of non-integer rational powers in f, with denominators
function _radicals(f::Term, x::Sym)
    out = Dict{Term,Int}()
    _rad!(out, f, x)
    return out
end
function _rad!(out, t::Term, x::Sym)
    has(t, x) || return
    if t isa Pow
        b, e = t.base, t.exp
        if e isa Num && e.val isa Q && !isint(e) && has(b, x)
            out[b] = lcm(get(out, b, 1), Int(denominator(e.val)))
        end
        _rad!(out, b, x)
        _rad!(out, e, x)
    elseif t isa Mul
        for p in t.factors
            _rad!(out, _powraw(p), x)
        end
    elseif t isa Add
        foreach(p -> _rad!(out, p.first, x), t.terms)
    elseif t isa Fn
        foreach(a -> _rad!(out, a, x), t.args)
    end
end

function _im_radlin(ctx, f::Term, x::Sym)
    rads = _radicals(f, x)
    length(rads) == 1 || return nothing
    L, n = first(rads)
    l = _linear(L, x)
    l === nothing && return nothing
    a1, b0 = l
    t = _isym(:t, _IPOS)
    xt = (_pow(t, Num(n)) - b0) / a1
    G = _safe(z -> cancel(subs(f, x => z) * n * _pow(t, Num(n - 1)) / a1), xt)
    (G === nothing || has(G, x)) && return nothing
    isempty(_radicals(G, t)) || return nothing
    Gt = _irec(ctx, G, t)
    Gt === nothing && return nothing
    return subs(Gt, t => _pow(L, Num(Q(1) // n)))
end

# ---- square roots of a quadratic -----------------------------------------------

# ∫ dx/sqrt(a x² + b x + c)
function _int_invsqrtquad(Qd::Term, a::Term, b::Term, c::Term, x::Sym)
    if isnegative(a)
        A = simplify(-a)
        D = simplify(b^2 + 4 * A * c)
        return _mul((_pow(A, Num(Q(-1) // 2)), _fncall(:asin, Term[cancel((2 * A * x - b) / sqrt(D))])))
    end
    ra = simplify(sqrt(a))
    return _mul((_pow(ra, MONE), _log(_add((sqrt(Qd), cancel((2 * a * x + b) / (2ra)))))))
end

# the quadratic Q with f = R(x) Q^(p/2), p odd: (Q, p, R)
function _sqrtquad_split(f::Term, x::Sym)
    rads = _radicals(f, x)
    length(rads) == 1 || return nothing
    Qd, n = first(rads)
    n == 2 || return nothing
    cq = polycoeffs(Qd, x)
    (cq === nothing || length(cq) != 3) && return nothing
    p = nothing
    rest = Term[_coef(f)]
    for y in _factors(f)
        b, e = _base_exp(y)
        if b == Qd && e isa Num && !isint(e)
            p === nothing || return nothing
            p = Int(numerator(e.val))
        else
            push!(rest, y)
        end
    end
    p === nothing && return nothing
    R = _mul(rest)
    _radicals(R, x) |> isempty || return nothing
    return (Qd, cq, p, R)
end

function _im_sqrtquad(ctx, f::Term, x::Sym)
    s = _sqrtquad_split(f, x)
    s === nothing && return nothing
    Qd, cq, p, R = s
    c, b, a = cq
    P = R
    pc = polycoeffs(P, x)
    pc === nothing && return nothing
    j = (p + 1) ÷ 2
    λ = _isym(:λ)
    dQ = diff(Qd, x)
    J = _int_invsqrtquad(Qd, a, b, c, x)
    if j >= 0
        Pt = expand(P * _pow(Qd, Num(j)))
        m = degree(Pt, x)
        rs = Sym[_isym(:r) for _ in 1:m]
        Rr = _add(Term[_mul((r, _pow(x, Num(k - 1)))) for (k, r) in enumerate(rs)])
        sol = _undetermined(diff(Rr, x) * Qd + Rr * dQ / 2 + λ - Pt, vcat(rs, [λ]), x)
        sol === nothing && return nothing
        F = _mul((subs(Rr, sol), sqrt(Qd)))
    else
        k = -j
        m = max(length(pc) - 1, 2k)
        rs = Sym[_isym(:r) for _ in 1:m]
        Rr = _add(Term[_mul((r, _pow(x, Num(i - 1)))) for (i, r) in enumerate(rs)])
        eq = diff(Rr, x) * Qd + (Q(1) // 2 - k) * Rr * dQ + λ * _pow(Qd, Num(k)) - P
        sol = _undetermined(eq, vcat(rs, [λ]), x)
        sol === nothing && return nothing
        F = _mul((subs(Rr, sol), _pow(Qd, Num(Q(1) // 2 - k))))
    end
    λv = sol[λ]
    iszero(λv) && return F
    return F + λv * J
end

# replace Q^(p/2) by σ^p everywhere in t
function _replpow(t::Term, Qd::Term, σ::Term)::Term
    if t isa Pow
        if t.base == Qd && t.exp isa Num && !isint(t.exp)
            return _pow(σ, Num(2 * t.exp.val))
        end
        return _pow(_replpow(t.base, Qd, σ), _replpow(t.exp, Qd, σ))
    elseif t isa Mul
        return _mul(Term[Num(t.c); [_replpow(_powraw(p), Qd, σ) for p in t.factors]])
    elseif t isa Add
        return _add(Term[_replpow(s, Qd, σ) for s in _summands(t)])
    elseif t isa Fn
        return _fncall(t.head, Term[_replpow(a, Qd, σ) for a in t.args])
    end
    return t
end

# Euler's substitutions for rational functions of x and sqrt(a x² + b x + c)
function _im_euler(ctx, f::Term, x::Sym)
    rads = _radicals(f, x)
    length(rads) == 1 || return nothing
    Qd, n = first(rads)
    n == 2 || return nothing
    cq = polycoeffs(Qd, x)
    (cq === nothing || length(cq) != 3) && return nothing
    c, b, a = cq
    t = _isym(:t)
    if ispositive(a)
        sa = simplify(sqrt(a))
        xt = (t^2 - c) / (b + 2 * sa * t)
        st = t - sa * xt
        back = sqrt(Qd) + sa * x
    elseif ispositive(c)
        sc = simplify(sqrt(c))
        xt = (2 * sc * t - b) / (a - t^2)
        st = xt * t + sc
        back = (sqrt(Qd) - sc) / x
    else
        return nothing
    end
    σ = _isym(:σ)
    h = _replpow(f, Qd, σ)
    G = _safe(z -> cancel(subs(h, Dict{Term,Term}(x => xt, σ => st)) * diff(xt, t)), 0)
    (G === nothing || has(G, x) || !_isratfun(G, t)) && return nothing
    Gt = _irec(ctx, G, t)
    Gt === nothing && return nothing
    return subs(Gt, t => back)
end

# ---- trigonometric integrands ---------------------------------------------------

_trigatoms(f::Term, x::Sym, heads) = _collect_sub!(Term[], y -> y isa Fn && y.head in heads && has(y, x), f)

# sin, cos, sinh, cosh as exponentials
function _trig2exp(t::Term, x::Sym)::Term
    has(t, x) || return t
    t isa Union{Num,Const,Sym} && return t
    y = _map(z -> _trig2exp(z, x), t)
    y isa Fn || return y
    h, u = y.head, y.args[1]
    has(u, x) || return y
    if h === :sin
        return _mul((_add((_exp(_mul((IM, u))), _mul((MONE, _exp(_mul((MONE, IM, u))))))), _pow(_mul((TWO, IM)), MONE)))
    elseif h === :cos
        return _mul((HALF, _add((_exp(_mul((IM, u))), _exp(_mul((MONE, IM, u)))))))
    elseif h === :sinh
        return _mul((HALF, _add((_exp(u), _mul((MONE, _exp(_mul((MONE, u)))))))))
    elseif h === :cosh
        return _mul((HALF, _add((_exp(u), _exp(_mul((MONE, u)))))))
    end
    return y
end

# exponentials (and Ei) of complex arguments back to trigonometric form
function _exp2trig(t::Term)::Term
    t isa Union{Num,Const,Sym} && return t
    y = _map(_exp2trig, t)
    y isa Fn || return y
    if y.head === :exp && has(y.args[1], IM)
        re, im = _reim(y.args[1])
        (re isa Fn && re.head === :re) && return y
        iszero(im) && return y
        return _mul((_exp(re), _add((_cos(im), _mul((IM, _sin(im)))))))
    elseif y.head === :Ei && has(y.args[1], IM)
        re, im = _reim(y.args[1])
        (re isa Fn && re.head === :re) && return y
        (iszero(re) && !iszero(im)) || return y
        if _looks_negative(im)
            θ = _mul((MONE, im))
            return _add((_fncall(:Ci, Term[θ]), _mul((MONE, IM, _fncall(:Si, Term[θ])))))
        end
        return _add((_fncall(:Ci, Term[im]), _mul((IM, _fncall(:Si, Term[im])))))
    end
    return y
end

# an exponential of x in a denominator (not a polynomial in exponentials)
function _expdenom(t::Term, x::Sym)
    t isa Add && return any(s -> _expdenom(s, x), _summands(t))
    t isa Mul && return any(p -> _expdenom(_powraw(p), x), t.factors)
    if t isa Pow
        e = t.exp
        return (e isa Num && e.val < 0 && !isempty(_trigatoms(t.base, x, (:exp,)))) || _expdenom(t.base, x)
    end
    return false
end

# products and powers of sin/cos (and sinh/cosh), times polynomials and
# exponentials: linearise through complex exponentials
function _im_fourier(ctx, f::Term, x::Sym)
    isempty(_trigatoms(f, x, (:sin, :cos))) && return nothing
    isempty(_trigatoms(f, x, (:tan, :tanh))) || return nothing
    h = expand(_trig2exp(f, x))
    _expdenom(h, x) && return nothing
    all(e -> polycoeffs(e.args[1], x) !== nothing, _trigatoms(h, x, (:exp,))) || return nothing
    parts = Term[]
    for s in _summands(h)
        F = _irec(ctx, s, x)
        F === nothing && return nothing
        push!(parts, F)
    end
    F = expand(_exp2trig(_add(parts)))
    _isreal_struct(f) || return F
    # the real part, taking the functions of real arguments as real
    R = expand((F + subs(F, IM => -IM)) / 2)
    return has(R, IM) ? nothing : R
end

# rational functions of sin, cos, tan of one linear argument: Bioche's rules
# choose the substitution u = cos, sin, tan or tan(θ/2)
function _im_bioche(ctx, f::Term, x::Sym; oddonly::Bool = false)
    atoms = _trigatoms(f, x, (:sin, :cos, :tan))
    isempty(atoms) && return nothing
    θ = atoms[1].args[1]
    all(a -> a.args[1] == θ, atoms) || return nothing
    l = _linear(θ, x)
    l === nothing && return nothing
    α = l[1]
    S, C = _isym(:S), _isym(:C)
    R = subs(f, Dict{Term,Term}(_sin(θ) => S, _cos(θ) => C, _tan(θ) => S / C))
    has(R, x) && return nothing
    R = cancel(R)
    _isratfun(R, S) || _isratfun(R, C) || return nothing
    u = _isym(:u)
    G = nothing
    if iszero(cancel(subs(R, S => -S) + R))
        G = _evensub(cancel(-R / S), S, 1 - u^2)
        G = G === nothing ? nothing : subs(G, C => u)
        back = _cos(θ)
    elseif iszero(cancel(subs(R, C => -C) + R))
        G = _evensub(cancel(R / C), C, 1 - u^2)
        G = G === nothing ? nothing : subs(G, S => u)
        back = _sin(θ)
    elseif oddonly
        return nothing
    elseif iszero(cancel(subs(R, Dict{Term,Term}(S => -S, C => -C)) - R))
        G = _evensub(cancel(subs(R, S => u * C)), C, 1 / (1 + u^2))
        G = G === nothing ? nothing : G / (1 + u^2)
        back = _tan(θ)
    else
        G = subs(R, Dict{Term,Term}(S => 2u / (1 + u^2), C => (1 - u^2) / (1 + u^2))) * 2 / (1 + u^2)
        back = _tan(θ / 2)
    end
    G === nothing && return nothing
    G = cancel(G / α)
    (has(G, S) || has(G, C)) && return nothing
    Gu = _irec(ctx, G, u)
    Gu === nothing && return nothing
    return subs(Gu, u => back)
end
_im_bioche_odd(ctx, f, x) = _im_bioche(ctx, f, x; oddonly = true)

# H with v^2 replaced by rep (H must be even in v)
function _evensub(H::Term, v::Sym, rep::Term)
    out = Term[]
    for p in (numerator(H), denominator(H))
        cs = polycoeffs(p, v)
        cs === nothing && return nothing
        any(k -> isodd(k - 1) && !iszero(cs[k]), eachindex(cs)) && return nothing
        push!(out, _add(Term[_mul((cs[k], _pow(rep, Num((k - 1) ÷ 2)))) for k in 1:2:length(cs)]))
    end
    return cancel(out[1] / out[2])
end

# ---- last resorts: other forms of the integrand ---------------------------------

function _im_rewrite(ctx, f::Term, x::Sym)
    for g in (_safe(expand, f), _safe(cancel, f))
        (g === nothing || g == f) && continue
        F = _irec(ctx, g, x)
        F !== nothing && return F
    end
    return nothing
end
