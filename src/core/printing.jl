# Text and LaTeX output.
#
# Sums are shown constant first and then by degree (`1 - n/K`, `a + b*x +
# c*x^2`), led by a positive term where there is one (`K - n`, not `-n + K`).
# Products are shown as a fraction when they have negative exponents.

const P_ADD, P_MUL, P_POW, P_ATOM = 1, 2, 3, 4

# ---- display order of the terms of a sum --------------------------------------

_deg(::Union{Num,Const}) = 0.0
_deg(::Sym) = 1.0
_deg(x::Pow) = x.exp isa Num ? _deg(x.base) * Float64(x.exp.val) : _deg(x.base)
_deg(x::Mul) = sum(e isa Num ? _deg(b) * Float64(e.val) : _deg(b) for (b, e) in x.factors)
_deg(x::Add) = maximum(_deg(t) for (t, _) in x.terms)
_deg(::Fn) = 1.0
_deg(::Deriv) = 1.0

function _display_terms(x::Add)
    ts = Tuple{NumVal,Term}[(k, t) for (t, k) in x.terms]
    sort!(ts; by = p -> _deg(p[2]), alg = MergeSort)
    iszero(x.c) || pushfirst!(ts, (x.c, ONE))
    if ts[1][1] < 0
        i = findfirst(p -> p[1] > 0, ts)
        if i !== nothing
            p = ts[i]
            deleteat!(ts, i)
            pushfirst!(ts, p)
        end
    end
    return ts
end

# ---- text --------------------------------------------------------------------------

Base.show(io::IO, x::Term) = print(io, _str(x))
Base.show(io::IO, ::MIME"text/plain", x::Term) = print(io, _str(x))
_str(x::Term) = _sp(x)[1]
_paren(s, p, need) = p < need ? "(" * s * ")" : s

function _numstr(v::NumVal)
    v isa Float64 && return string(v)
    isone(denominator(v)) && return string(numerator(v))
    return string(numerator(v), "/", denominator(v))
end

function _sp(x::Num)
    s = _numstr(x.val)
    p = x.val < 0 ? P_ADD : (x.val isa Q && !_isint(x.val) ? P_MUL : P_ATOM)
    return (s, p)
end
_sp(x::Const) = (x.name === :I ? "im" : String(x.name), P_ATOM)
_sp(x::Sym) = (String(x.name), P_ATOM)
function _sp(x::Fn)
    x.head === :exp && x.args[1] == ONE && return ("ℯ", P_ATOM)
    if x.head === :Integral
        return ("∫(" * _str(x.args[1]) * ", " * join(_str.(x.args[2:end]), ", ") * ")", P_ATOM)
    end
    return (string(x.head) * "(" * join((_str(a) for a in x.args), ", ") * ")", P_ATOM)
end
function _sp(x::Deriv)
    parts = String[]
    for (v, k) in x.vars
        push!(parts, k == 1 ? _str(v) : _str(v) * ", " * string(k))
    end
    return ("D(" * _str(x.f) * ", " * join(parts, ", ") * ")", P_ATOM)
end

function _powstr(b::Term, e::Term)
    e == ONE && return _sp(b)
    bs, bp = _sp(b)
    e == HALF && return ("sqrt(" * bs * ")", P_ATOM)
    if e isa Num && e.val < 0
        s, p = _powstr(b, Num(-e.val))
        return ("1/" * _paren(s, p, P_POW), P_MUL)
    end
    es, ep = _sp(e)
    return (_paren(bs, bp, P_ATOM) * "^" * _paren(es, ep, P_ATOM), P_POW)
end
_sp(x::Pow) = _powstr(x.base, x.exp)

function _sp(x::Mul)
    c = x.c
    num, den = String[], String[]
    neg = c < 0
    ac = abs(c)
    if ac isa Float64
        isone(ac) || push!(num, string(ac))
    else
        isone(numerator(ac)) || push!(num, string(numerator(ac)))
        isone(denominator(ac)) || push!(den, string(denominator(ac)))
    end
    nfac = 0
    for (b, e) in x.factors
        if e isa Num && e.val < 0
            s, p = _powstr(b, Num(-e.val))
            push!(den, _paren(s, p, P_MUL + 1))
        else
            s, p = _powstr(b, e)
            push!(num, _paren(s, p, P_MUL + (p == P_MUL ? 1 : 0)))
            nfac += 1
        end
    end
    ns = isempty(num) ? "1" : join(num, "*")
    s = if isempty(den)
        ns
    elseif length(den) == 1
        ns * "/" * den[1]
    else
        ns * "/(" * join(den, "*") * ")"
    end
    return (neg ? "-" * s : s, neg ? P_ADD : P_MUL)
end

function _sp(x::Add)
    ts = _display_terms(x)
    io = IOBuffer()
    for (i, (k, t)) in enumerate(ts)
        s, _ = _sp(_scale_any(t, abs(k)))
        if i == 1
            print(io, k < 0 ? "-" : "", s)
        else
            print(io, k < 0 ? " - " : " + ", s)
        end
    end
    return (String(take!(io)), P_ADD)
end
_scale_any(t::Term, k::NumVal) = t == ONE ? Num(k) : _scale(t, k)

# ---- equations and conditions ------------------------------------------------------

const _OPSTR = Dict(:< => "<", :<= => "≤", :> => ">", :>= => "≥", :(==) => "==", :!= => "≠")
Base.show(io::IO, e::Eqn) = print(io, _str(e.lhs), " ~ ", _str(e.rhs))
Base.show(io::IO, r::Rel) = print(io, _str(r.lhs), " ", _OPSTR[r.op], " ", _str(r.rhs))
Base.show(io::IO, a::And) = join(io, (c isa Or ? "(" * sprint(show, c) * ")" : sprint(show, c) for c in a.args), " ∧ ")
Base.show(io::IO, a::Or) = join(io, (c isa And ? "(" * sprint(show, c) * ")" : sprint(show, c) for c in a.args), " ∨ ")

# ---- LaTeX ---------------------------------------------------------------------------

const _GREEK = Dict(
    'α' => "\\alpha", 'β' => "\\beta", 'γ' => "\\gamma", 'δ' => "\\delta", 'ϵ' => "\\epsilon",
    'ε' => "\\varepsilon", 'ζ' => "\\zeta", 'η' => "\\eta", 'θ' => "\\theta", 'ι' => "\\iota",
    'κ' => "\\kappa", 'λ' => "\\lambda", 'μ' => "\\mu", 'ν' => "\\nu", 'ξ' => "\\xi",
    'π' => "\\pi", 'ρ' => "\\rho", 'σ' => "\\sigma", 'τ' => "\\tau", 'υ' => "\\upsilon",
    'ϕ' => "\\phi", 'φ' => "\\varphi", 'χ' => "\\chi", 'ψ' => "\\psi", 'ω' => "\\omega",
    'Γ' => "\\Gamma", 'Δ' => "\\Delta", 'Θ' => "\\Theta", 'Λ' => "\\Lambda", 'Ξ' => "\\Xi",
    'Π' => "\\Pi", 'Σ' => "\\Sigma", 'Φ' => "\\Phi", 'Ψ' => "\\Psi", 'Ω' => "\\Omega")
const _GREEKNAMES = Set(["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta",
    "iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", "sigma", "tau", "upsilon",
    "phi", "chi", "psi", "omega", "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma",
    "Phi", "Psi", "Omega"])
const _SUBDIGITS = Dict(zip("₀₁₂₃₄₅₆₇₈₉", "0123456789"))
const _ACCENTS = Dict('̂' => "\\hat", '̄' => "\\bar", '̃' => "\\tilde", '̇' => "\\dot")

function _latexbase(s::AbstractString)
    out = IOBuffer()
    chars = collect(s)
    i = 1
    while i <= length(chars)
        ch = chars[i]
        nxt = i < length(chars) ? chars[i+1] : ' '
        body = haskey(_GREEK, ch) ? _GREEK[ch] * " " : string(ch)
        if haskey(_ACCENTS, nxt)
            print(out, _ACCENTS[nxt], "{", strip(body), "}")
            i += 2
        else
            print(out, body)
            i += 1
        end
    end
    r = strip(String(take!(out)))
    s in _GREEKNAMES && return "\\" * s
    if length(s) > 1 && all(isletter, s) && !any(c -> haskey(_GREEK, c), s)
        return "\\mathrm{" * s * "}"
    end
    return r
end

function _latexname(name::Symbol)
    s = String(name)
    sub = ""
    m = match(r"^(.*?)_(.+)$", s)
    if m !== nothing
        s, sub = m.captures[1], m.captures[2]
    else
        m2 = match(r"^(.*?[^0-9₀-₉])([0-9₀-₉]+)$", s)
        if m2 !== nothing
            s, sub = m2.captures[1], map(c -> get(_SUBDIGITS, c, c), m2.captures[2])
        end
    end
    b = _latexbase(s)
    isempty(sub) && return b
    subl = all(isdigit, sub) ? sub : _latexbase(sub)
    return b * "_{" * subl * "}"
end

"""
    latex(x) -> String

LaTeX for a term, an equation, a condition, or a vector or matrix of terms.
Terms also display as LaTeX in notebooks and Quarto documents.
"""
latex(x::Term) = _lx(x)[1]
latex(x::Number) = latex(toterm(x))
latex(e::Eqn) = latex(e.lhs) * " = " * latex(e.rhs)
const _OPTEX = Dict(:< => "<", :<= => "\\le", :> => ">", :>= => "\\ge", :(==) => "=", :!= => "\\ne")
latex(r::Rel) = latex(r.lhs) * " " * _OPTEX[r.op] * " " * latex(r.rhs)
latex(a::And) = join((c isa Or ? "\\left(" * latex(c) * "\\right)" : latex(c) for c in a.args), " \\land ")
latex(a::Or) = join((c isa And ? "\\left(" * latex(c) * "\\right)" : latex(c) for c in a.args), " \\lor ")
latex(b::Bool) = b ? "\\mathrm{true}" : "\\mathrm{false}"
function latex(A::AbstractMatrix)
    rows = [join((latex(A[i, j]) for j in axes(A, 2)), " & ") for i in axes(A, 1)]
    return "\\begin{pmatrix}" * join(rows, " \\\\ ") * "\\end{pmatrix}"
end
latex(v::AbstractVector) = "\\begin{pmatrix}" * join((latex(y) for y in v), " \\\\ ") * "\\end{pmatrix}"

for T in (Term, Eqn, Cond)
    @eval Base.show(io::IO, ::MIME"text/latex", x::$T) = print(io, "\$", latex(x), "\$")
end

_lparen(s, p, need) = p < need ? "\\left(" * s * "\\right)" : s

function _lx(x::Num)
    v = x.val
    v isa Float64 && return (string(v), v < 0 ? P_ADD : P_ATOM)
    isone(denominator(v)) && return (string(numerator(v)), v < 0 ? P_ADD : P_ATOM)
    s = "\\frac{" * string(abs(numerator(v))) * "}{" * string(denominator(v)) * "}"
    return (v < 0 ? "-" * s : s, v < 0 ? P_ADD : P_MUL)
end
_lx(x::Const) = (x.name === :I ? "i" : x.name === :π ? "\\pi" : "\\infty", P_ATOM)
_lx(x::Sym) = (_latexname(x.name), P_ATOM)
const _FNTEX = Dict(:log => "\\log", :sin => "\\sin", :cos => "\\cos", :tan => "\\tan",
    :asin => "\\arcsin", :acos => "\\arccos", :atan => "\\arctan", :sinh => "\\sinh",
    :cosh => "\\cosh", :tanh => "\\tanh", :sign => "\\operatorname{sign}",
    :erf => "\\operatorname{erf}", :erfi => "\\operatorname{erfi}", :Ei => "\\operatorname{Ei}",
    :Si => "\\operatorname{Si}", :Ci => "\\operatorname{Ci}")
function _lx(x::Fn)
    h = x.head
    if h === :exp
        x.args[1] == ONE && return ("e", P_ATOM)
        return ("e^{" * latex(x.args[1]) * "}", P_POW)
    elseif h === :abs
        return ("\\left|" * latex(x.args[1]) * "\\right|", P_ATOM)
    elseif h === :Integral
        return ("\\int " * latex(x.args[1]) * " \\, d" * latex(x.args[2]), P_MUL)
    elseif h === :factorial
        a, p = _lx(x.args[1])
        return (_lparen(a, p, P_ATOM) * "!", P_POW)
    elseif h === :gamma
        return ("\\Gamma\\left(" * latex(x.args[1]) * "\\right)", P_ATOM)
    elseif h === :binomial
        return ("\\binom{" * latex(x.args[1]) * "}{" * latex(x.args[2]) * "}", P_ATOM)
    elseif h in (:Sum, :Product)
        g, k, a, b = x.args
        op = h === :Sum ? "\\sum" : "\\prod"
        body, p = _lx(g)
        return (op * "_{" * latex(k) * "=" * latex(a) * "}^{" * latex(b) * "} " * _lparen(body, p, P_MUL), P_ADD)
    elseif h === :RootOf
        return ("\\operatorname{Root}_{" * latex(x.args[3]) * "}\\left(" * latex(x.args[1]) * "\\right)", P_ATOM)
    end
    name = get(_FNTEX, h, _latexname(h))
    return (name * "\\left(" * join((latex(a) for a in x.args), ", ") * "\\right)", P_ATOM)
end
function _lx(x::Deriv)
    f = x.f
    fname = f isa Fn ? _latexname(f.head) : latex(f)
    n = sum(k for (_, k) in x.vars)
    top = n == 1 ? "d" : "d^{$n}"
    bot = join(("d" * latex(v) * (k == 1 ? "" : "^{$k}") for (v, k) in x.vars), " \\, ")
    return ("\\frac{" * top * " " * fname * "}{" * bot * "}", P_MUL)
end
function _lpow(b::Term, e::Term)
    e == ONE && return _lx(b)
    bs, bp = _lx(b)
    e == HALF && return ("\\sqrt{" * bs * "}", P_ATOM)
    if e isa Num && e.val isa Q && numerator(e.val) == 1 && denominator(e.val) > 2
        return ("\\sqrt[" * string(denominator(e.val)) * "]{" * bs * "}", P_ATOM)
    end
    if e isa Num && e.val < 0
        s, _ = _lpow(b, Num(-e.val))
        return ("\\frac{1}{" * s * "}", P_MUL)
    end
    if b isa Fn && b.head === :exp && b.args[1] != ONE
        return ("\\left(" * bs * "\\right)^{" * latex(e) * "}", P_POW)
    end
    return (_lparen(bs, bp, P_ATOM) * "^{" * latex(e) * "}", P_POW)
end
_lx(x::Pow) = _lpow(x.base, x.exp)
function _ljoin(parts)
    io = IOBuffer()
    for (i, p) in enumerate(parts)
        if i > 1
            prev = parts[i-1]
            print(io, (isdigit(last(prev)) && isdigit(first(p))) ? " \\cdot " : " ")
        end
        print(io, p)
    end
    return String(take!(io))
end
function _lx(x::Mul)
    c = x.c
    neg = c < 0
    ac = abs(c)
    num, den = String[], String[]
    if ac isa Float64
        isone(ac) || push!(num, string(ac))
    else
        isone(numerator(ac)) || push!(num, string(numerator(ac)))
        isone(denominator(ac)) || push!(den, string(denominator(ac)))
    end
    nden = count(f -> f.second isa Num && f.second.val < 0, x.factors) + length(den)
    for (b, e) in x.factors
        if e isa Num && e.val < 0
            s, p = _lpow(b, Num(-e.val))
            push!(den, nden == 1 ? s : _lparen(s, p, P_MUL))
        else
            s, p = _lpow(b, e)
            push!(num, _lparen(s, p, P_MUL))
        end
    end
    ns = isempty(num) ? "1" : _ljoin(num)
    s = isempty(den) ? ns : "\\frac{" * ns * "}{" * _ljoin(den) * "}"
    return (neg ? "-" * s : s, neg ? P_ADD : P_MUL)
end
function _lx(x::Add)
    ts = _display_terms(x)
    io = IOBuffer()
    for (i, (k, t)) in enumerate(ts)
        s, _ = _lx(_scale_any(t, abs(k)))
        print(io, i == 1 ? (k < 0 ? "-" : "") : (k < 0 ? " - " : " + "), s)
    end
    return (String(take!(io)), P_ADD)
end
