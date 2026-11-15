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
  `matexp` (also for matrices that cannot be diagonalised, and with oscillations
  as `cos`/`sin`: `realform`), Routh–Hurwitz and Jury stability conditions.
- Calculus: `diff`, `limit`, `taylor`, and `integrate` (definite and
  indefinite): complete for rational functions (Hermite, Lazard–Rioboo–Trager,
  real arctangent forms), a Risch–Norman integrator for exponentials,
  logarithms and the like, rules for trigonometric and algebraic integrands,
  `erf`/`Ei`/`Si`/`Ci` for the classic non-elementary ones, and the gamma and
  beta integrals; every antiderivative is checked by differentiation.
- Sums and products: `summation` (powers, geometric series, Poisson and
  binomial sums, to `∞`), `product`, `factorial`, `binomial`, `gamma`;
  `perturb` for roots as series in a small parameter.
- `dsolve` (first-order, linear constant-coefficient with any forcing,
  boundary values, linear systems) and `rsolve` (linear and linear-fractional
  maps, linear recurrences of any order with boundary values, non-autonomous
  first-order recurrences, linear systems).
- Ecology and evolution: `equilibria` and `stability` of continuous- and
  discrete-time models, `invasion_fitness`, `classify_singular` (CSS, branching
  points), matrix games (`ess`, `nash`, `replicator`), Leslie matrices,
  sensitivities, `reproduction_number`, absorbing Markov chains; `cycles` of
  maps, `hopf` conditions, `conserved_quantity`; `quasi_steady_state`;
  invasion with class structure; stochastic models (`stationary_distribution`,
  `extinction_probability`, `fixation_probability`, `moran`, `wright_fisher`,
  diffusion fixation, absorption times and stationary densities); `simulate`,
  `cobweb` and `bifurcation_data` for numerical exploration, and `gillespie`,
  `markov_path` and `wright_fisher_path` for stochastic simulation.

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

## Plotting

Load PracticalBayesPlot to enable plotting (the algebra package keeps its single
LinearAlgebra dependency). If needed, install it with
`Pkg.add(url="https://github.com/EvoArt/PracticalBayesPlot.jl")`.

```julia
using PracticalCAS
import PracticalBayesPlot as PBP

@syms x::positive y::positive a::positive
model = ode(x => x*(1-y), y => y*(a*x-1))
dynamicsplot(model; selfloops=false)  # signed influences from the Jacobian
phaseplot(model; parameters=Dict(a=>1), xlim=(0, 3), ylim=(0, 3),
          initials=[[0.5, 1.0], [0.25, 1.0]], steps=420, equilibria=:auto)

rps = MatrixGame([0 -1 1; 1 0 -1; -1 1 0];
                 strategies=["Rock", "Paper", "Scissors"])
fig = ternaryplot(rps; initials=[[0.2, 0.3, 0.5]], steps=2000, equilibria=:auto)
PBP.save("rps.svg", fig)  # also .tex (TikZ), .typ (CeTZ), .html

@syms p q s
frequencies = ode(p=>p*(s-q), q=>q*(p-s), s=>s*(q-p))
ternaryplot(frequencies; labels=["Rock", "Paper", "Scissors"])
# Two independent equations also work, with s replaced by 1-p-q.
```

`dynamicsplot` draws an **influence graph**, not inferred compartment transfers:
`x → y` means `∂rhs_y/∂x ≠ 0`. Positive influences are blue (`+`), negative
vermilion (`−`), and undecidable signs grey (`?`); nodes widen to fit long
names. Use `point=Dict(...)` for local
signs or `edgelabels=:derivative` for symbolic edge labels. Cycles and
self-loops are allowed. A derivative that vanishes at `point` is labelled `0`.
For recurrences, edges describe the next-state map.

`phaseplot` and `ternaryplot` draw phase portraits at fixed numeric parameters.
Ternary vertices are strategy 1 on the left, 2 on the right, and 3 at the top;
initial states are triples summing to one. Three-equation inputs must conserve
total frequency; sampled boundary rates must point inward or along the edges.
Arrows show direction by default (`normalize=false` shows relative speed).
Optional trajectories use fixed-step RK4 and stop at the domain boundary;
check convergence with a smaller `dt`, particularly for fast dynamics. Each
trajectory gets its own colour, a dot at its start and arrowheads along it.
`equilibria=:auto` solves for the equilibria in the window and marks them by
local stability (numerical Jacobian): filled stable, open unstable (saddles
included), grey neutral (e.g. a centre); a vector of states marks given
points. These functions do not find bifurcations.

`dynamics_graph`, `phase_data`, and `ternary_data` expose the underlying data
without a plotting dependency. The `!` plotting forms draw into an existing
PracticalBayesPlot `Axis` and return those data. Figure-level functions accept
`figure=(; size=(800, 600))` and `axis=(; title="...")` for customisation.
See [examples/plotting.jl](examples/plotting.jl) for runnable examples.

## Otto & Day, chapter by chapter

Every chapter has a worked notebook in [examples/](examples/) (Quarto, Julia
engine); each notebook is also run by the test suite, with hidden cells
checking the results.

| Chapter | Topics | Notebook |
| --- | --- | --- |
| Primer 1 | derivatives, limits, Taylor series, logs, sums, integrals | [primer1-functions](examples/primer1-functions.qmd) |
| 2–3 | deriving models: selection, mutation, migration, discrete vs continuous time | [ch02-03-building-models](examples/ch02-03-building-models.qmd) |
| 4 | simulation, cobwebs, bifurcation diagrams, nullclines (plots via the PracticalBayesPlot extension) | [ch04-numerical](examples/ch04-numerical.qmd) |
| 5 | equilibria and stability, one variable | [ch05-one-variable-equilibria](examples/ch05-one-variable-equilibria.qmd) |
| 6 | general solutions, one variable | [ch06-one-variable-solutions](examples/ch06-one-variable-solutions.qmd) |
| Primer 2, 7 | matrices, eigenvalues, linear models | [ch07-linear-multivariable](examples/ch07-linear-multivariable.qmd) |
| 8 | nonlinear models with several variables | [ch08-nonlinear-multivariable](examples/ch08-nonlinear-multivariable.qmd) |
| 9 | general solutions with several variables, transformations, forcing | [ch09-general-solutions-multivariable](examples/ch09-general-solutions-multivariable.qmd) |
| 10 | class-structured populations, Euler–Lotka, reproductive value | [ch10-class-structured](examples/ch10-class-structured.qmd) |
| 11 | cycles, Hopf bifurcations, constants of motion | [ch11-periodic](examples/ch11-periodic.qmd) |
| 12 | invasion analysis, ESS, branching, class structure | [ch12-invasion](examples/ch12-invasion.qmd) |
| Primer 3, 13 | distributions, moments, generating functions | [ch13-probability](examples/ch13-probability.qmd) |
| 14 | Markov chains, Wright–Fisher, Moran, branching processes | [ch14-discrete-stochastic](examples/ch14-discrete-stochastic.qmd) |
| 15 | continuous-time chains, birth–death processes, diffusions | [ch15-continuous-stochastic](examples/ch15-continuous-stochastic.qmd) |
| Appendix | perturbation, separation of time scales | [appendix-perturbation](examples/appendix-perturbation.qmd) |

The sibling package [PracticalProbability.jl](https://github.com/EvoArt/PracticalProbability.jl)
covers the probability side of primer 3 and chapters 13–14 by name: named
distribution families with their moments and generating functions, the algebra
of events and conditional probability, and numeric Markov chains.

## Status


Version 0.1, under active development. See [ROADMAP.md](ROADMAP.md).
