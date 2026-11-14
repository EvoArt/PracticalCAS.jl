# Taylor polynomials and linearisation.

# f at x = a, by substitution or, where that is singular, as a limit
function _at(f::Term, x::Sym, a::Term)
    v = _safe(y -> subs(f, x => y), a)
    (v !== nothing && !_singular(v)) && return simplify(v)
    return limit(f, x, a)
end

"""
    taylor(f, x, a, n)
    taylor(f, xs, as, n)

The Taylor polynomial of `f` about `x = a` up to and including order `n` (a
polynomial in `x - a`). With vectors `xs` and `as`, the multivariate Taylor
polynomial of total order `n` about the point `as`.

    taylor(exp(x), x, 0, 3)              # 1 + x + x^2/2 + x^3/6
    taylor(R*n/(1 + a*n), n, 0, 2)       # R*n - a*R*n^2
"""
function taylor(f, x::Sym, a, n::Integer)
    f, a = toterm(f), toterm(a)
    out = Term[]
    g = f
    fact = big(1)
    for k in 0:n
        k > 0 && (fact *= k; g = diff(g, x))
        c = _at(g, x, a)
        c isa Fn && c.head === :Limit && throw(ArgumentError("taylor: $f has no Taylor expansion of order $n about $x = $a"))
        push!(out, _mul((c, Num(Q(1) // fact), _pow(_add((x, _mul((MONE, a)))), Num(k)))))
    end
    return _add(out)
end
function taylor(f, xs::AbstractVector, as::AbstractVector, n::Integer)
    s = Sym(gensym(:s), SymInfo(true, false, nothing, false, nothing, false))
    d = Dict{Term,Term}(x => toterm(a) + s * (x - toterm(a)) for (x, a) in zip(xs, as))
    g = subs(toterm(f), d)
    return subs(taylor(g, s, 0, n), s => 1)
end

"""
    linearize(f, xs, point)

The first-order Taylor polynomial of `f` (a term or a vector of terms) about
`point` (a vector, or a dictionary from the symbols to values).
"""
linearize(f, xs::AbstractVector, point::AbstractVector) = f isa AbstractVector ?
    Term[taylor(g, xs, point, 1) for g in f] : taylor(f, xs, point, 1)
linearize(f, xs::AbstractVector, point::AbstractDict) = linearize(f, xs, [point[x] for x in xs])

"""
    series(f, x, a = 0, n = 5)

The same as [`taylor`](@ref), with defaults.
"""
series(f, x::Sym, a = 0, n::Integer = 5) = taylor(f, x, a, n)
