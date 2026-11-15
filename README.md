# PracticalCAS.jl

A computer algebra system in pure Julia, aimed first at mathematical modelling
in ecology and evolution: everything needed for Otto & Day's *A Biologist's
Guide to Mathematical Modeling in Ecology and Evolution*, plus evolutionary game
theory and adaptive dynamics.

- Exact arithmetic in canonical form, with **assumptions** on symbols
  (`r::positive`, `p::(0, 1)`) and between them (`assuming(V < C)`).
- Polynomials: `expand`, `cancel`, `factor` (multivariate), `collect`, `apart`.
- `simplify`, and conditions (`r*(K - n) > 0`) that simplify under the assumptions.
- `solve` for equations and systems with parameters (equilibria).
- Symbolic linear algebra: `det`, `inv`, `eigvals`, `eigen`, `charpoly`, `matpow`,
  `matexp`, Routh–Hurwitz and Jury stability conditions.
- Calculus: `diff`, `limit`, `taylor`, and `integrate` (definite and
  indefinite): complete for rational functions (Hermite, Lazard–Rioboo–Trager,
  real arctangent forms), a Risch–Norman integrator for exponentials,
  logarithms and the like, rules for trigonometric and algebraic integrands,
  `erf`/`Ei`/`Si`/`Ci` for the classic non-elementary ones; every
  antiderivative is checked by differentiation.
- `dsolve` (first-order, linear constant-coefficient, boundary values, linear
  systems) and `rsolve` (linear and linear-fractional maps, linear systems).
- Ecology and evolution: `equilibria` and `stability` of continuous- and
  discrete-time models, `invasion_fitness`, `classify_singular` (CSS, branching
  points), matrix games (`ess`, `nash`, `replicator`), Leslie matrices,
  sensitivities, `reproduction_number`, absorbing Markov chains.
- LaTeX output (`latex(x)`, and automatically in notebooks and Quarto).

## Example

```julia
using PracticalCAS

@syms n::nonneg r::positive K::positive t n₀::positive

logistic = ode(n => r*n*(1 - n/K))
equilibria(logistic)                 # n = 0 and n = K
stability(logistic)                  # n = 0 unstable, n = K stable (eigenvalue -r)
dsolve(r*n*(1 - n/K), n, t; ic = n₀) # K n₀ / (n₀ + (K - n₀) e^(-r t))

# discrete logistic: n = K is stable when 0 < r < 2
stability(recurrence(n => n + r*n*(1 - n/K)), Dict(n => K)).condition

# Hawk–Dove: mixed ESS p = V/C when C > V
@syms V::positive C::positive
ess(hawk_dove(V, C))

# adaptive dynamics
@syms m x a
classify_singular(-(m - a)^2 + (x - a)^2, m, x)   # x = a is a CSS

# integration
@syms x μ σ::positive
integrate(1/(x^4 + 1), x)          # logarithms and arctangents with √2
integrate(x*exp(x)*sin(x), x)      # eˣ(x sin x - x cos x + cos x)/2
integrate(exp(-(x - μ)^2/(2σ^2))/σ, x, -∞, ∞)   # √(2π)
```

## Status

Version 0.1, under active development. See [ROADMAP.md](ROADMAP.md).
