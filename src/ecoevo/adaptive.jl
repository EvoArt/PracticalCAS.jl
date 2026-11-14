# Evolutionary invasion analysis and adaptive dynamics (Otto & Day ch. 12).

"""
    selection_gradient(W, m, r)

`∂W/∂m` at `m = r`, for an invasion fitness `W(m, r)` of a mutant with trait
`m` in a resident population with trait `r`.
"""
selection_gradient(W, m::Sym, r::Sym) = simplify(subs(diff(toterm(W), m), m => r))

"""
    singular_strategies(W, m, r) -> Vector{Term}

The resident traits where the selection gradient vanishes.
"""
singular_strategies(W, m::Sym, r::Sym) = solve(selection_gradient(W, m, r), r)

"""
    SingularStrategy

A singular strategy `value` with the conditions for evolutionary stability
(`∂²W/∂m² < 0`: no nearby mutant invades) and convergence stability
(`∂²W/∂m² + ∂²W/∂m∂r < 0`: nearby residents evolve towards it), and the
resulting type: `:CSS` (both: an evolutionary end point), `:branching` (CS but
not ES), `:garden_of_eden` (ES but not CS), `:repeller` (neither), or
`:depends`.
"""
struct SingularStrategy
    value::Term
    ess::CondLike
    convergence::CondLike
    kind::Symbol
end

function Base.show(io::IO, s::SingularStrategy)
    println(io, "Singular strategy ", s.value, " (", s.kind, ")")
    println(io, "  evolutionarily stable if: ", s.ess)
    print(io, "  convergence stable if:    ", s.convergence)
end

"""
    classify_singular(W, m, r) -> Vector{SingularStrategy}

Find and classify the singular strategies of the invasion fitness `W(m, r)`.
The classification uses second derivatives, so it does not depend on whether
`W` is a growth rate (neutral value 0) or a growth factor (neutral value 1).
"""
function classify_singular(W, m::Sym, r::Sym)
    W = toterm(W)
    Wmm = diff(W, m, 2)
    Wmr = diff(diff(W, m), r)
    out = SingularStrategy[]
    for s in singular_strategies(W, m, r)
        d = Dict{Term,Term}(m => s, r => s)
        a = simplify(subs(Wmm, d))
        b = simplify(subs(Wmm + Wmr, d))
        es = simplify(Rel(:<, a, ZERO))
        cs = simplify(Rel(:<, b, ZERO))
        de, dc = decide(es), decide(cs)
        kind = if de === nothing || dc === nothing
            :depends
        elseif de && dc
            :CSS
        elseif dc
            :branching
        elseif de
            :garden_of_eden
        else
            :repeller
        end
        push!(out, SingularStrategy(s, es, cs, kind))
    end
    return out
end

"""
    invades(W, m, r; neutral = 0)

The condition for a mutant `m` to invade a resident `r`: `W(m, r) > neutral`
(use `neutral = 1` for discrete-time growth factors).
"""
invades(W, m::Sym, r::Sym; neutral = 0) = simplify(Rel(:>, toterm(W), toterm(neutral)))
