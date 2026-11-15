# The Risch–Norman ("parallel Risch") heuristic, after M. Bronstein's pmint.
#
# The integrand is written as a rational function of x and kernels t₁ … tₙ
# (exponentials, logarithms, tangents, algebraic and symbolic powers, inverse
# trigonometric and special functions; sin and cos become tan of the half
# angle, hyperbolic functions exponentials), closed under differentiation, so
# that d/dx is a derivation D on ℚ(params)(x, t₁, …, tₙ). The antiderivative
# is sought as
#
#     A(x, t)/den + Σ cⱼ log(pⱼ) + Σ dₖ atan(gₖ/wₖ)
#
# with den built from the integrand's denominator (special factors kept,
# normal ones lowered by one), pⱼ the irreducible factors of the denominators
# and the special polynomials, the arctangents from quadratic candidates
# that are sums of two squares, and A a polynomial of bounded total degree with
# unknown coefficients. Equating coefficients of D(candidate) = f gives a
# sparse linear system over ℚ(params). The method is a heuristic (it can miss
# antiderivatives) but every answer it gives is right.

const _RNFNS = (:log, :tan, :atan, :asin, :acos, :erf, :erfi, :Ei, :Si, :Ci, :sin, :cos)

mutable struct _RN
    x::Sym
    exps::Dict{Term,Tuple{Q,Sym}}          # w => (g, T) with T = exp(g w)
    pows::Dict{Term,Tuple{Int,Sym}}        # base => (L, T) with T = base^(1/L)
    spows::Dict{Tuple{Term,Term},Sym}      # (base, exponent) => T, symbolic exponents
    fns::Dict{Term,Sym}                    # kernel function => T
    kers::Vector{Tuple{Sym,Term}}          # T => kernel in x
    ders::Vector{Term}                     # D(T) in the forward variables (same order)
    special::Vector{Term}                  # special polynomials
    tanspecial::Vector{Term}
end

function _rn_rewrite(t::Term, x::Sym)::Term
    has(t, x) || return t
    t isa Union{Num,Const,Sym} && return t
    y = _map(z -> _rn_rewrite(z, x), t)
    y isa Fn || return y
    h = y.head
    length(y.args) == 1 || return y
    u = y.args[1]
    has(u, x) || return y
    if h === :sinh
        return (_exp(u) - _exp(-u)) / 2
    elseif h === :cosh
        return (_exp(u) + _exp(-u)) / 2
    elseif h === :tanh
        return (_exp(2u) - 1) / (_exp(2u) + 1)
    elseif h === :sin
        T = _tan(u / 2)
        return 2T / (1 + T^2)
    elseif h === :cos
        T = _tan(u / 2)
        return (1 - T^2) / (1 + T^2)
    end
    return y
end

function _rn_atoms!(out::Vector{Term}, t::Term, x::Sym)
    has(t, x) || return out
    t == x && return out
    if t isa Add
        foreach(p -> _rn_atoms!(out, p.first, x), t.terms)
    elseif t isa Mul
        foreach(p -> _rn_atoms!(out, _powraw(p), x), t.factors)
    elseif t isa Pow
        if !has(t.exp, x) && isint(t.exp)
            _rn_atoms!(out, t.base, x)
        else
            t in out || push!(out, t)
        end
    else
        t in out || push!(out, t)
    end
    return out
end

_rn_exparg(a::Term, x::Sym) = a isa Fn && a.head === :exp ? a.args[1] :
                              (a isa Pow && has(a.exp, x) ? _mul((a.exp, _log(a.base))) : nothing)

# the kernels of f, closed under differentiation
function _rn_kernels(f::Term, x::Sym)
    queue = _rn_atoms!(Term[], f, x)
    seen = Term[]
    while !isempty(queue)
        a = popfirst!(queue)
        a in seen && continue
        push!(seen, a)
        length(seen) > 10 && return nothing
        u = _rn_exparg(a, x)
        d = if u !== nothing
            diff(u, x)
        elseif a isa Pow
            diff(a.base, x)
        elseif a isa Fn && a.head in _RNFNS && length(a.args) == 1
            diff(a, x)
        else
            return nothing
        end
        for n in _rn_atoms!(Term[], d, x)
            n in seen || n in queue || push!(queue, n)
        end
    end
    return seen
end

_qgcd(a::Q, b::Q) = Q(gcd(numerator(a), numerator(b)), lcm(denominator(a), denominator(b)))

# u = u₀ + c w with u₀ free of x and c rational (w normalised)
function _rn_split(u::Term, x::Sym)
    xs, cs0 = Term[], Term[]
    for s in _summands(u)
        has(s, x) ? push!(xs, s) : push!(cs0, s)
    end
    isempty(xs) && return nothing
    u1 = _add(xs)
    c = if u1 isa Add
        ks = [k for (_, k) in u1.terms]
        all(k -> k isa Q, ks) || return nothing
        g = reduce(_qgcd, ks)
        ks[1] < 0 ? -g : g
    elseif u1 isa Mul
        u1.c isa Q || return nothing
        u1.c
    else
        Q(1)
    end
    return (_add(cs0), c, _mul((Num(inv(c)), u1)))
end

function _rn_build(atoms::Vector{Term}, x::Sym)
    R = _RN(x, Dict(), Dict(), Dict(), Dict(), Tuple{Sym,Term}[], Term[], Term[], Term[])
    groups = Dict{Term,Vector{Q}}()
    powL = Dict{Term,Int}()
    for a in atoms
        u = _rn_exparg(a, x)
        if u !== nothing
            sp = _rn_split(u, x)
            sp === nothing && return nothing
            push!(get!(groups, sp[3], Q[]), sp[2])
        elseif a isa Pow
            b, e = a.base, a.exp
            if e isa Num && e.val isa Q
                powL[b] = lcm(get(powL, b, 1), Int(denominator(e.val)))
            else
                key = (b, _looks_negative(e) ? _mul((MONE, e)) : e)
                if !haskey(R.spows, key)
                    T = _isym(:T)
                    R.spows[key] = T
                    push!(R.kers, (T, _pow(b, key[2])))
                end
            end
        elseif a isa Fn
            T = _isym(:T)
            R.fns[a] = T
            push!(R.kers, (T, a))
        end
    end
    for (w, cs) in groups
        g = abs(reduce(_qgcd, cs))
        T = _isym(:T)
        R.exps[w] = (g, T)
        push!(R.kers, (T, _exp(_mul((Num(g), w)))))
    end
    for (b, L) in powL
        T = _isym(:T)
        R.pows[b] = (L, T)
        push!(R.kers, (T, _pow(b, Num(Q(1) // L))))
    end
    # derivatives of the kernels, and special polynomials
    for (T, k) in R.kers
        d = nothing
        u = _rn_exparg(k, x)
        if u !== nothing
            du = _rn_fwd(R, diff(u, x))
            du === nothing && return nothing
            d = du * T
            push!(R.special, T)
        elseif k isa Pow
            b, e = k.base, k.exp
            db, fb = _rn_fwd(R, diff(b, x)), _rn_fwd(R, b)
            (db === nothing || fb === nothing) && return nothing
            d = e * db / fb * T
            push!(R.special, T)
        else
            d = _rn_fwd(R, diff(k, x))
            d === nothing && return nothing
            if k isa Fn && k.head === :tan
                push!(R.special, 1 + T^2)
                push!(R.tanspecial, 1 + T^2)
            end
        end
        push!(R.ders, d)
    end
    return R
end

# a term in x (after _rn_rewrite) as a term in x and the kernel symbols
function _rn_fwd(R::_RN, t::Term)
    x = R.x
    has(t, x) || return t
    t == x && return t
    if t isa Add || t isa Mul
        parts = Term[]
        t isa Mul && push!(parts, Num(t.c))
        for s in (t isa Add ? _summands(t) : Term[_powraw(p) for p in t.factors])
            y = _rn_fwd(R, s)
            y === nothing && return nothing
            push!(parts, y)
        end
        return t isa Add ? _add(parts) : _mul(parts)
    elseif t isa Pow
        b, e = t.base, t.exp
        has(e, x) && return _rn_fwdexp(R, _mul((e, _log(b))))
        if isint(e)
            y = _rn_fwd(R, b)
            return y === nothing ? nothing : _pow(y, e)
        end
        if e isa Num && e.val isa Q
            haskey(R.pows, b) || return nothing
            L, T = R.pows[b]
            k = e.val * L
            _isint(k) || return nothing
            return _pow(T, Num(k))
        end
        neg = _looks_negative(e)
        T = get(R.spows, (b, neg ? _mul((MONE, e)) : e), nothing)
        T === nothing && return nothing
        return neg ? _pow(T, MONE) : T
    elseif t isa Fn
        t.head === :exp && return _rn_fwdexp(R, t.args[1])
        return get(R.fns, t, nothing)
    end
    return nothing
end
function _rn_fwdexp(R::_RN, u::Term)
    sp = _rn_split(u, R.x)
    sp === nothing && return nothing
    u0, c, w = sp
    haskey(R.exps, w) || return nothing
    g, T = R.exps[w]
    k = c / g
    _isint(k) || return nothing
    return _mul((_exp(u0), _pow(T, Num(k))))
end

_mplcm(a::MP, b::MP) = (g = pgcd(a, b); divexact(a, g) * b)
_vdeg(p::MP, nV::Int) = iszero(p) ? -1 : maximum(sum(e[1:nV]) for e in keys(p.t))
_vdep(p::MP, nV::Int) = any(e -> any(>(0), e[1:nV]), keys(p.t))
_mpshift(p::MP, e::Vector{Int}) = MP(p.nv, Dict(k .+ e => c for (k, c) in p.t))

function _monomials(nV::Int, dg::Int, nv::Int)
    out = Vector{Int}[]
    function rec(prefix, i, left)
        if i > nV
            push!(out, vcat(prefix, zeros(Int, nv - nV)))
            return
        end
        for k in 0:left
            rec(vcat(prefix, [k]), i + 1, left - k)
        end
    end
    rec(Int[], 1, dg)
    return out
end

function _rn_monic(p::MP)
    p = mpnormalize(p)
    return p
end

"""
    _risch_norman(f, x) -> Term or nothing

An elementary (or special-function) antiderivative of `f` found by the parallel
Risch heuristic, or `nothing`.
"""
function _risch_norman(f::Term, x::Sym; maxmon::Int = 300)
    g0 = _rn_rewrite(f, x)
    atoms = _rn_kernels(g0, x)
    (atoms === nothing || isempty(atoms)) && return nothing
    R = _rn_build(atoms, x)
    R === nothing && return nothing
    ff = _rn_fwd(R, g0)
    ff === nothing && return nothing
    Ts = Sym[k[1] for k in R.kers]
    gens = Gens()
    _gen!(gens, x)
    foreach(T -> _gen!(gens, T), Ts)
    nV = 1 + length(Ts)
    ys = Term[_inner(cancel, t) for t in vcat(Term[ff], R.ders, R.special)]
    foreach(y -> _collect_gens!(gens, y), ys)
    for i in nV+1:nvars(gens)
        t = gens.list[i]
        (has(t, x) || any(T -> has(t, T), Ts)) && return nothing
    end
    nv = nvars(gens)
    rfn(y) = begin
        n, d = _rf(y, gens)
        gg = pgcd(n, d)
        if !isconst(gg)
            n, d = divexact(n, gg), divexact(d, gg)
        end
        c = qcontent(d)
        (scale(n, inv(c)), scale(d, inv(c)))
    end
    P, Qd = rfn(ys[1])
    iszero(P) && return ZERO
    # the derivation: D(v_i) = dv_i / q
    dn = MP[mpconst(nv, 1)]
    dd = MP[mpconst(nv, 1)]
    for k in 1:length(Ts)
        n, d = rfn(ys[1+k])
        push!(dn, n)
        push!(dd, d)
    end
    q = reduce(_mplcm, dd)
    dv = MP[divexact(q, dd[i]) * dn[i] for i in 1:nV]
    Dq(p::MP) = begin
        r = MP(nv)
        for i in 1:nV
            deg(p, i) > 0 || continue
            r = r + dv[i] * deriv(p, i)
        end
        r
    end
    specials = MP[rfn(y)[1] for y in ys[2+length(Ts):end]]
    tansp = MP[rfn(_inner(cancel, t))[1] for t in R.tanspecial]
    # candidate denominator and logarithms
    _, facs = factor_poly(Qd)
    cden = mpconst(nv, 1)
    logc = MP[]
    for (p, e) in facs
        _vdep(p, nV) || continue
        isspec = any(s -> divexact(s, p) !== nothing, specials)
        cden = cden * p^(isspec ? e : e - 1)
        push!(logc, mpnormalize(p))
    end
    _, qf = factor_poly(q)
    for (p, _) in qf
        _vdep(p, nV) && push!(logc, mpnormalize(p))
    end
    for s in tansp
        push!(logc, mpnormalize(s))
    end
    # factors of the special polynomials can appear as logs too
    unique!(logc)
    filter!(p -> !any(s -> length(keys(s.t)) == 1 && s == p, specials), logc)
    atans = Tuple{MP,MP,MP,MP}[]
    for p in logc
        for v in 1:nV
            deg(p, v) == 2 || continue
            c, b, a = coeffs(p, v)
            w = mpsqrt(scale(a * c, 4) - b * b)
            (w === nothing || iszero(w)) && continue
            push!(atans, (scale(a * mpvar(nv, v), 2) + b, w, a, p))
            break
        end
    end
    dg = 1 + max(_vdeg(P, nV), _vdeg(Qd, nV))
    while dg > 1 && binomial(nV + dg, nV) > maxmon
        dg -= 1
    end
    for d in (dg, dg + 1)
        binomial(nV + d, nV) > maxmon && break
        F = _rn_solve(P, Qd, q, dv, Dq, cden, logc, atans, d, nV, nv, gens)
        F === nothing && continue
        back = Dict{Term,Term}(T => k for (T, k) in R.kers)
        return subs(F, back)
    end
    return nothing
end

function _rn_solve(P, Qd, q, dv, Dq, cden, logc, atans, dg, nV, nv, gens)
    monos = _monomials(nV, dg, nv)
    nA, nL = length(monos), length(logc)
    M = _mplcm(Qd, q * cden * cden)
    for p in logc
        M = _mplcm(M, q * p)
    end
    for (_, _, a, p) in atans
        M = _mplcm(M, scale(q * a * p, 4))
    end
    W = divexact(M, q * cden * cden)
    CW = cden * W
    DW = Dq(cden) * W
    dCW = MP[dv[i] * CW for i in 1:nV]
    cols = MP[]
    for e in monos
        E = MP(nv)
        for i in 1:nV
            e[i] > 0 || continue
            f = copy(e)
            f[i] -= 1
            E = E + scale(_mpshift(dCW[i], f), e[i])
        end
        push!(cols, E - _mpshift(DW, e))
    end
    for p in logc
        push!(cols, Dq(p) * divexact(M, q * p))
    end
    for (g, w, a, p) in atans
        push!(cols, (w * Dq(g) - g * Dq(w)) * divexact(M, scale(q * a * p, 4)))
    end
    E0 = P * divexact(M, Qd)
    # equations, one per monomial in x and the kernels
    rows = Dict{Vector{Int},Dict{Int,MP}}()
    addcol!(E, col) = for (e, c) in E.t
        row = get!(rows, e[1:nV], Dict{Int,MP}())
        m = get!(row, col, MP(nv))
        pe = copy(e)
        pe[1:nV] .= 0
        _addto!(m.t, pe, c)
    end
    for (j, E) in enumerate(cols)
        addcol!(E, j)
    end
    addcol!(E0, 0)
    ncols = length(cols)
    params = nv > nV
    if params
        # quick test at a random point of the parameters
        vals = Q[i <= nV ? Q(0) : Q(10007 + 7919 * i, 7 + 3i) for i in 1:nv]
        qrows = [Dict{Int,Q}(c => _mpeval(m, vals) for (c, m) in r) for r in values(rows)]
        _sparse_solve(qrows, ncols, Q(0)) === nothing && return nothing
        z = rfconst(nv, 0)
        frows = [Dict{Int,RF}(c => rf(m) for (c, m) in r if !iszero(m)) for r in values(rows)]
    else
        z = Q(0)
        frows = [Dict{Int,Q}(c => constval(m) for (c, m) in r if !iszero(m)) for r in values(rows)]
    end
    sol = _sparse_solve(frows, ncols, z)
    sol === nothing && return nothing
    mono(e) = _mul(Term[_pow(gens.list[i], Num(e[i])) for i in 1:nV if e[i] > 0])
    A = _add(Term[_mul((_coefterm(sol[i], gens), mono(monos[i]))) for i in 1:nA if !iszero(sol[i])])
    out = Term[_mul((A, _pow(_mp2term(cden, gens), MONE)))]
    for (j, p) in enumerate(logc)
        c = sol[nA+j]
        iszero(c) && continue
        push!(out, _mul((_coefterm(c, gens), _log(_mp2term(p, gens)))))
    end
    for (k, (g, w, _, _)) in enumerate(atans)
        c = sol[nA+nL+k]
        iszero(c) && continue
        push!(out, _mul((_coefterm(c, gens), _fncall(:atan, Term[_mp2term(g, gens) / _mp2term(w, gens)]))))
    end
    return _add(out)
end
