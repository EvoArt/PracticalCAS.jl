# Symbolic sums and products.
#
# A summand is split into a constant, a polynomial P(k), a geometric part zᵏ
# (powers and exponentials whose exponents are linear in k) and at most one of
# 1/k! or binomial(n, k). Then
#
#   Σ P(k) zᵏ           antidifference Q(k) zᵏ with z Q(k+1) - Q(k) = P(k)
#                       (Q of degree deg P + 1 and z = 1 for plain polynomials);
#   Σ_{k≥0} k⁽ʲ⁾ zᵏ/k!  = zʲ eᶻ (exponential series, P in falling factorials);
#   Σ_{k=0}^{n} binomial(n, k) k⁽ʲ⁾ xᵏ yⁿ⁻ᵏ = n⁽ʲ⁾ xʲ (x + y)ⁿ⁻ʲ (binomial theorem).
#
# These cover the moments and generating functions of the geometric, Poisson
# and binomial distributions, geometric series in recurrences, and sums of
# powers. An infinite geometric sum assumes |z| < 1.

_islinear_in(e::Term, k::Sym) = (cs = polycoeffs(e, k); cs !== nothing && length(cs) <= 2 && !any(c -> has(c, k), cs) ? cs : nothing)

# falling factorial x(x-1)⋯(x-j+1)
_falling(x::Term, j::Int) = j == 0 ? ONE : _mul(Term[_add((x, Num(-i))) for i in 0:j-1])

# Stirling numbers of the second kind S(m, j), j = 0..m: kᵐ = Σ S(m, j) k⁽ʲ⁾
function _stirling2(m::Int)
    S = zeros(BigInt, m + 1, m + 1)
    S[1, 1] = 1
    for i in 1:m, j in 1:i
        S[i+1, j+1] = j * S[i, j+1] + S[i, j]
    end
    return S[m+1, :]
end

# the summand c P(k) zᵏ ⋅ (kind): kind is :geom, :exp (1/k!) or (:binom, n)
struct _Summand
    c::Term
    P::Vector{Term}       # polynomial coefficients, constant first
    z::Term
    kind::Any
    ybase::Term           # for binomial sums: the y in yⁿ⁻ᵏ (ONE if none)
end

function _split_summand(t::Term, k::Sym)
    c = Term[]
    P = Term[ONE]
    zs = Term[]
    geo = Tuple{Term,Term,Term}[]     # (base, α, β): base^(αk + β)
    kind = :geom
    facs = t isa Mul ? Term[Num(t.c); [_pow(b, e) for (b, e) in t.factors]] : Term[t]
    for f in facs
        if !has(f, k)
            push!(c, f)
            continue
        end
        b, e = f isa Pow ? (f.base, f.exp) : (f, ONE)
        if !has(b, k)
            l = _islinear_in(e, k)
            l === nothing && return nothing
            push!(geo, (b, length(l) == 2 ? l[2] : ZERO, l[1]))
        elseif b isa Fn && b.head === :exp && e == ONE
            l = _islinear_in(b.args[1], k)
            l === nothing && return nothing
            push!(zs, _exp(length(l) == 2 ? l[2] : ZERO))
            push!(c, _exp(l[1]))
        elseif b isa Fn && b.head === :factorial && b.args[1] == k && e == MONE && kind === :geom
            kind = :exp
        elseif b isa Fn && b.head === :binomial && b.args[2] == k && !has(b.args[1], k) && e == ONE && kind === :geom
            kind = (:binom, b.args[1])
        elseif e isa Num && e.val isa Q && _isint(e.val) && e.val > 0 && (pc = polycoeffs(b, k)) !== nothing && !any(x -> has(x, k), pc)
            for _ in 1:Int(numerator(e.val))
                P = _polymul(P, pc)
            end
        else
            return nothing
        end
    end
    ybase = ONE
    for (b, α, β) in geo
        if kind isa Tuple && α == MONE && ybase == ONE
            # yⁿ⁻ᵏ⁺ᵐ = yⁿ⁻ᵏ ⋅ yᵐ⁻ⁿ... kept as the y of the binomial theorem
            ybase = b
            push!(c, _pow(b, _add((β, _mul((MONE, kind[2]))))))
        else
            push!(zs, _pow(b, α))
            push!(c, _pow(b, β))
        end
    end
    return _Summand(_mul(c), P, simplify(_mul(zs)), kind, ybase)
end

function _polymul(a::Vector{Term}, b::Vector{Term})
    out = Term[ZERO for _ in 1:length(a)+length(b)-1]
    for i in eachindex(a), j in eachindex(b)
        out[i+j-1] = out[i+j-1] + a[i] * b[j]
    end
    return out
end

_polyval(P::Vector{Term}, x::Term) = _add(Term[_mul((P[i], _pow(x, Num(i - 1)))) for i in eachindex(P)])

# Q with z Q(k+1) - Q(k) = P(k); for z = 1, Q(0) = 0 and deg Q = deg P + 1
function _antidifference(P::Vector{Term}, z::Term)
    d = length(P) - 1
    if iszero(simplify(z - 1))
        u = Term[ZERO for _ in 0:d+1]       # u[i+1] is the coefficient of kⁱ
        for j in d:-1:0
            s = P[j+1]
            for i in j+2:d+1
                s = s - binomial(big(i), big(j)) * u[i+1]
            end
            u[j+2] = simplify(s / (j + 1))
        end
        return u
    end
    u = Term[ZERO for _ in 0:d]
    for j in d:-1:0
        s = P[j+1]
        for i in j+1:d
            s = s - z * binomial(big(i), big(j)) * u[i+1]
        end
        u[j+1] = simplify(s / (z - 1))
    end
    return u
end

function _sum_one(s::_Summand, k::Sym, a::Term, b::Term)
    if s.kind === :geom
        Qp = _antidifference(s.P, s.z)
        Qa = _polyval(Qp, a) * _pow(s.z, a)
        b == INF && return iszero(simplify(s.z - 1)) ? (all(iszero, s.P) ? ZERO : nothing) : s.c * (-Qa)
        return s.c * (_polyval(Qp, b + 1) * _pow(s.z, b + 1) - Qa)
    elseif s.kind === :exp
        (b == INF && a isa Num && a.val isa Q && _isint(a.val) && a.val >= 0) || return nothing
        tot = Term[]
        # P(k) = Σⱼ (Σₘ pₘ S(m, j)) k⁽ʲ⁾
        for (m1, p) in enumerate(s.P)
            iszero(p) && continue
            S = _stirling2(m1 - 1)
            for j in 0:m1-1
                iszero(S[j+1]) && continue
                push!(tot, _mul((p, Num(Q(S[j+1])), _pow(s.z, Num(j)))))
            end
        end
        r = _mul((_add(tot), _exp(s.z)))
        lo = Int(numerator(a.val))
        head = Term[_mul((_polyval(s.P, Num(i)), _pow(s.z, Num(i)), Num(Q(1, factorial(big(i)))))) for i in 0:lo-1]
        return s.c * (r - _add(head))
    else
        n = s.kind[2]
        a == ZERO && isequiv(b, n) || return nothing
        x, y = s.z, s.ybase
        tot = Term[]
        for (m1, p) in enumerate(s.P)
            iszero(p) && continue
            S = _stirling2(m1 - 1)
            for j in 0:m1-1
                iszero(S[j+1]) && continue
                push!(tot, _mul((p, Num(Q(S[j+1])), _falling(n, j), _pow(x, Num(j)), _pow(_add((x, y)), _add((n, Num(-j)))))))
            end
        end
        return s.c * _add(tot)
    end
end

function _sum(f::Term, k::Sym, a::Term, b::Term; expanded::Bool = false)
    has(f, k) || return b == INF ? (iszero(f) ? ZERO : nothing) : f * (b - a + 1)
    out = Term[]
    for t in _summands(f)
        if !has(t, k)
            b == INF && return nothing
            push!(out, t * (b - a + 1))
            continue
        end
        s = _split_summand(t, k)
        r = s === nothing ? nothing : _sum_one(s, k, a, b)
        if r === nothing
            expanded && return nothing
            e = expand(t)
            e == t && return nothing
            r = _sum(e, k, a, b; expanded = true)
            r === nothing && return nothing
        end
        push!(out, r)
    end
    return _add(out)
end

_intbound(x::Term) = x isa Num && x.val isa Q && _isint(x.val) ? Int(numerator(x.val)) : nothing

"""
    summation(f, k, a, b)

The sum of `f` for the integer `k` from `a` to `b` (`b` may be `∞`), in closed
form when `f` is a polynomial times powers in `k` (`Σ k² xᵏ`, geometric series),
a Poisson-type term `P(k) zᵏ/k!` summed to `∞`, or a binomial term
`binomial(n, k) P(k) xᵏ yⁿ⁻ᵏ` summed from 0 to `n`; numeric ranges of up to
1000 terms are added directly. Otherwise the result is the unevaluated
`Sum(f, k, a, b)`, which [`evalf`](@ref) can still evaluate. Infinite geometric
sums assume the ratio has modulus below one.

    @syms k::natural n::natural p::(0, 1) s λ::positive
    summation(k * binomial(n, k) * p^k * (1 - p)^(n - k), k, 0, n)   # n p
    summation(exp(-λ) * λ^k / factorial(k) * s^k, k, 0, ∞)          # exp(λ(s - 1))
    summation(k^2, k, 1, n)                                          # n(n + 1)(2n + 1)/6
"""
function summation(f, k::Sym, a, b)
    f, a, b = toterm(f), toterm(a), toterm(b)
    lo, hi = _intbound(a), _intbound(b)
    if lo !== nothing && hi !== nothing && hi - lo <= 1000
        hi < lo && return ZERO
        return simplify(_add(Term[subs(f, k => i) for i in lo:hi]))
    end
    r = _sum(f, k, a, b)
    r === nothing && return Fn(:Sum, Term[f, k, a, b])
    return simplify(r)
end

"""
    product(f, k, a, b)

The product of `f` for the integer `k` from `a` to `b`: constants and powers
`c^(αk + β)` in closed form, linear factors `k + m` as factorials (or gamma
functions); numeric ranges of up to 1000 factors directly. Otherwise the
unevaluated `Product(f, k, a, b)`.

    product(k, k, 1, n)            # factorial(n)
    product(r * 2^k, k, 1, n)      # r^n 2^(n(n + 1)/2)
"""
function product(f, k::Sym, a, b)
    f, a, b = toterm(f), toterm(a), toterm(b)
    lo, hi = _intbound(a), _intbound(b)
    if lo !== nothing && hi !== nothing && hi - lo <= 1000
        hi < lo && return ONE
        return simplify(_mul(Term[subs(f, k => i) for i in lo:hi]))
    end
    unev = Fn(:Product, Term[f, k, a, b])
    b == INF && return unev
    n = b - a + 1
    sk = (a + b) * n / 2                    # Σ k
    out = Term[]
    facs = f isa Mul ? Term[Num(f.c); [_pow(bb, e) for (bb, e) in f.factors]] : Term[f]
    for g in facs
        if !has(g, k)
            push!(out, _pow(g, n))
            continue
        end
        gb, ge = g isa Pow ? (g.base, g.exp) : (g, ONE)
        if !has(gb, k)
            # c^(αk + β)
            l = _islinear_in(ge, k)
            l === nothing && return unev
            α = length(l) == 2 ? l[2] : ZERO
            push!(out, _pow(gb, α * sk + l[1] * n))
            continue
        end
        (ge isa Num && ge.val isa Q && _isint(ge.val)) || return unev
        pc = polycoeffs(gb, k)
        (pc === nothing || any(x -> has(x, k), pc)) && return unev
        c, fs = factor_list(gb)
        push!(out, _pow(toterm(c), ge * n))
        for (h, m) in fs
            em = ge * m
            if !has(h, k)
                push!(out, _pow(h, em * n))
                continue
            end
            l = _islinear_in(h, k)
            (l === nothing || length(l) != 2) && return unev
            u, v = l[2], l[1]
            mm = simplify(v / u)                # u k + v = u (k + m)
            push!(out, _pow(u, em * n))
            mi = _intbound(mm)
            r = mi !== nothing ? _factorial(b + mi) / _factorial(a - 1 + mi) : _gamma(b + mm + 1) / _gamma(a + mm)
            push!(out, _pow(r, em))
        end
    end
    return simplify(_mul(out))
end

# ---- Euler integrals ----------------------------------------------------------------

# ∫_{-∞}^{∞} c P(x) exp(Q(x)) dx for a polynomial P and a quadratic Q with
# negative leading coefficient -α: with Q = -α(x - m)² + q₀ and x = y + m,
# Σⱼ pⱼ ∫ yʲ e^(-αy²) dy = Σ_{j even} pⱼ Γ((j+1)/2)/α^((j+1)/2), times c e^(q₀)
# (moments of the normal distribution, to any order)
function _gauss_integral(f::Term, x::Sym)
    facs = f isa Mul ? Term[Num(f.c); [_pow(bb, e) for (bb, e) in f.factors]] : Term[f]
    c, P, quad = Term[], Term[], ZERO
    for g in facs
        has(g, x) || (push!(c, g); continue)
        gb, ge = g isa Pow ? (g.base, g.exp) : (g, ONE)
        if gb isa Fn && gb.head === :exp
            quad = quad + gb.args[1] * ge
        else
            push!(P, g)
        end
    end
    iszero(quad) && return nothing
    qc = polycoeffs(quad, x)

    (qc === nothing || length(qc) != 3 || any(y -> has(y, x), qc)) && return nothing
    α = simplify(-qc[3])
    ispositive(α) || return nothing
    m = simplify(qc[2] / (2α))
    q0 = simplify(qc[1] + α * m^2)
    y = Sym(gensym(:y), SymInfo(true, false, nothing, false, nothing, false))
    Py = expand(subs(_mul(P), x => y + m))
    pc = polycoeffs(Py, y)
    (pc === nothing || any(z -> has(z, y) || has(z, x), pc)) && return nothing
    tot = Term[]
    for (j1, p) in enumerate(pc)
        j = j1 - 1
        (iseven(j) && !iszero(p)) || continue
        h = Num(Q(j + 1, 2))
        push!(tot, p * _gamma(h) / _pow(α, h))
    end
    return simplify(_mul(c) * _exp(q0) * _add(tot))
end


# ∫₀^∞ c xᵖ e^(-βx) dx = c Γ(p+1)/β^(p+1) and ∫₀¹ c xᵖ (1-x)^q dx = c B(p+1, q+1),
# for exponents that are not natural numbers (those integrate elementarily)
function _euler_integral(f::Term, x::Sym, a::Term, b::Term)
    a == MINF && b == INF && return _gauss_integral(f, x)
    a == ZERO || return nothing
    (b == INF || b == ONE) || return nothing
    c, p, q, β = Term[], ZERO, ZERO, ZERO
    facs = f isa Mul ? Term[Num(f.c); [_pow(bb, e) for (bb, e) in f.factors]] : Term[f]
    omx = _add((ONE, _mul((MONE, x))))
    for g in facs
        has(g, x) || (push!(c, g); continue)
        gb, ge = g isa Pow ? (g.base, g.exp) : (g, ONE)
        has(ge, x) && return nothing
        if gb == x
            p = p + ge
        elseif gb == omx && b == ONE
            q = q + ge
        elseif gb isa Fn && gb.head === :exp && b == INF
            l = _islinear_in(gb.args[1] * ge, x)
            (l === nothing || length(l) != 2) && return nothing
            β = β - l[2]
            push!(c, _exp(l[1]))
        else
            return nothing
        end
    end
    _natural(simplify(p)) && _natural(simplify(q)) && return nothing
    if b == INF
        iszero(q) || return nothing
        (ispositive(β) && ispositive(p + 1)) || return nothing
        return simplify(_mul(c) * _gamma(p + 1) / _pow(β, p + 1))
    end
    iszero(β) || return nothing
    (ispositive(p + 1) && ispositive(q + 1)) || return nothing
    return simplify(_mul(c) * _gamma(p + 1) * _gamma(q + 1) / _gamma(p + q + 2))
end
