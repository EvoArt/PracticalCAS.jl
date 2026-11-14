# Polynomial and rational-function operations on terms.

"""
    cancel(x)

`x` as a single fraction `p/q` with `p` and `q` coprime polynomials (in the
symbols and other generators of `x`), with `q` having positive leading
coefficient. Function arguments are cancelled too.
"""
function cancel(x::Term)::Term
    x isa Union{Num,Const,Sym} && return x
    n, d, g, fl = ratfun(x)
    return _quot(_mp2term(n, g; float = fl), _mp2term(d, g; float = fl))
end
cancel(x::Number) = toterm(x)
cancel(x::AbstractArray) = map(cancel, x)

_quot(n::Term, d::Term) = d == ONE ? n : _mul((n, _pow(d, MONE)))

"""
    together(x)

Combine `x` over a common denominator (the same as [`cancel`](@ref)).
"""
together(x) = cancel(x)

"""
    numerator(x), denominator(x)

The numerator and denominator of `x` after [`cancel`](@ref).
"""
Base.numerator(x::Term) = (r = ratfun(x); _mp2term(r[1], r[3]; float = r[4]))
Base.denominator(x::Term) = (r = ratfun(x); _mp2term(r[2], r[3]; float = r[4]))

"""
    expand(x)

Multiply out products and positive integer powers of sums, in `x` and inside
function arguments. Denominators are kept (and expanded) as they are.
"""
expand(x::Number) = toterm(x)
expand(x::AbstractArray) = map(expand, x)
expand(x::Union{Num,Const,Sym,Deriv}) = x
expand(x::Add) = _add(Term[Num(x.c); [_mul((Num(k), expand(t))) for (t, k) in x.terms]])
expand(x::Fn) = _fncall(x.head, Term[expand(a) for a in x.args])
expand(x::Pow) = _expandpow(expand(x.base), x.exp)
function expand(x::Mul)
    acc = Term[Num(x.c)]
    for (b, e) in x.factors
        f = _expandpow(expand(b), e)
        acc = _mulsums(acc, _summands(f))
    end
    return _add(acc)
end
function _expandpow(b::Term, e::Term)::Term
    if b isa Add && isint(e) && e.val > 0
        n = Int(numerator(e.val))
        terms = _summands(b)
        acc = Term[ONE]
        for _ in 1:n
            acc = _mulsums(acc, terms)
        end
        return _add(acc)
    elseif b isa Add && isint(e) && e.val < 0
        return _pow(_expandpow(b, Num(-e.val)), MONE)
    elseif b isa Mul && isint(e)
        return expand(_pow(b, e))
    end
    return _pow(b, expand(e))
end
function _mulsums(as::Vector{Term}, bs::Vector{Term})
    out = Term[]
    for a in as, b in bs
        push!(out, _mul((a, b)))
    end
    return out
end

"""
    factor(x)

Factor `x` (a polynomial or rational function in its symbols) over the
rationals. The result keeps its factored shape: `factor(2x + 2)` is `2(x + 1)`.
"""
function factor(x::Term)::Term
    x isa Union{Num,Const,Sym} && return x
    c, fs = factor_list(x)
    xs = Pair{Term,Term}[]
    for (f, k) in fs
        b, e = _base_exp(f)
        push!(xs, b => _mul((e, Num(k))))
    end
    isempty(xs) && return c
    sort!(xs; by = p -> p.second isa Num && p.second.val < 0, alg = MergeSort)
    cv = c.val
    length(xs) == 1 && isone(cv) && return _pow(xs[1].first, xs[1].second)
    return Mul(cv, xs)
end
factor(x::Number) = toterm(x)
factor(x::AbstractArray) = map(factor, x)

"""
    factor_list(x) -> (c, [f₁ => k₁, …])

The factorisation of `x` as a constant and a list of irreducible factors with
multiplicities (negative for denominator factors).
"""
function factor_list(x::Term)
    x isa Num && return (x, Pair{Term,Int}[])
    n, d, g, fl = ratfun(x; inner = factor_inner)
    cn, fn = factor_poly(n)
    cd, fd = factor_poly(d)
    out = Pair{Term,Int}[]
    for (f, k) in fn
        push!(out, _mp2term(f, g; float = fl) => k)
    end
    for (f, k) in fd
        push!(out, _mp2term(f, g; float = fl) => -k)
    end
    c = cn / cd
    return (Num(fl ? Float64(c) : c), out)
end

# inside function arguments use the simplest of the cancelled and factored forms
factor_inner(x::Term) = (c = cancel(x); x isa Union{Num,Const,Sym} ? x : c)

"""
    polycoeffs(x, v) -> Vector{Term} or nothing

The coefficients of `x` as a polynomial in `v` (constant term first), or
`nothing` if `x` is not a polynomial in `v`. Coefficients may contain other
symbols and are cancelled.
"""
function polycoeffs(x::Term, v::Term)
    y = expand(x)
    d = Dict{Int,Vector{Term}}()
    for t in _summands(y)
        k, c = _vpower(t, v)
        k === nothing && return nothing
        push!(get!(d, k, Term[]), c)
    end
    isempty(d) && return Term[ZERO]
    n = maximum(keys(d))
    return Term[cancel(_add(get(d, k, Term[ZERO]))) for k in 0:n]
end
polycoeffs(x::Number, v::Term) = Term[toterm(x)]

# split a monomial term into (power of v, coefficient), nothing if v appears
# other than as a nonnegative integer power
function _vpower(t::Term, v::Term)
    has(t, v) || return (0, t)
    t == v && return (1, ONE)
    if t isa Pow && t.base == v && isint(t.exp) && t.exp.val >= 0
        return (Int(numerator(t.exp.val)), ONE)
    end
    if t isa Mul
        k = 0
        rest = Term[Num(t.c)]
        for (b, e) in t.factors
            if b == v && isint(e) && e.val >= 0
                k += Int(numerator(e.val))
            elseif has(b, v) || has(e, v)
                return (nothing, ZERO)
            else
                push!(rest, _powraw(b => e))
            end
        end
        return (k, _mul(rest))
    end
    return (nothing, ZERO)
end

"""
    degree(x, v)

The degree of `x` as a polynomial in `v` (`-1` for zero, `nothing` if not a
polynomial).
"""
function degree(x, v::Term)
    cs = polycoeffs(toterm(x), v)
    cs === nothing && return nothing
    i = findlast(c -> !iszero(c), cs)
    return i === nothing ? -1 : i - 1
end

"""
    coeff(x, v, k = 1)

The coefficient of `v^k` in `x` (a polynomial in `v`).
"""
function coeff(x, v::Term, k::Integer = 1)
    cs = polycoeffs(toterm(x), v)
    cs === nothing && throw(ArgumentError("coeff: $x is not a polynomial in $v"))
    return k + 1 <= length(cs) ? cs[k+1] : ZERO
end

"""
    collect(x, v)

`x` as a polynomial in `v` with each coefficient factored:
`collect(a*x + b*x + c, x)` is `c + (a + b)*x`.
"""
function Base.collect(x::Term, v::Term)
    n, d = numerator(x), denominator(x)
    cs = polycoeffs(n, v)
    cs === nothing && return x
    num = _add(Term[_mul((factor(c), _pow(v, Num(k - 1)))) for (k, c) in enumerate(cs)])
    return d == ONE ? num : _quot(num, factor(d))
end
