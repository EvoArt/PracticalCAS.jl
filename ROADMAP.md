# Roadmap

## Goal

First: everything needed to work through Otto & Day (*A Biologist's Guide to
Mathematical Modeling in Ecology and Evolution*), plus evolutionary game theory
and adaptive dynamics, pleasantly. Then: a general CAS more complete than
Symbolics.jl, split into packages along the layers (core, then the rest), with
PracticalProbability.jl using it for the algebra inside probability expressions.

## Done (0.1)

- [x] Canonical terms, exact rationals, floats, `π`, `im`, `∞`; elementary
      functions with automatic always-valid rules.
- [x] Assumptions on symbols (sign, integer, bounds) and facts between symbols;
      sign engine (structure + exact interval arithmetic + factorisation).
- [x] Text and LaTeX printing; `evalf`, `lambdify`.
- [x] Multivariate polynomials over ℚ: gcd, `cancel`, `expand`, `factor`
      (content, square-free, linear factors, quadratic discriminants, polynomials
      in xᵏ), `collect`, `polycoeffs`.
- [x] `simplify` (cancel/factor/expand/trig, sqrt and abs under assumptions,
      logs of positives); conditions simplified and decided under assumptions.
- [x] `solve`: polynomial and rational equations and systems with parameters,
      exp/log/power inversion.
- [x] Linear algebra: det, inv, rref, rank, nullspace, linsolve, charpoly,
      eigenvalues and eigenvectors, left eigenvectors, matpow, matexp,
      Routh–Hurwitz and Jury conditions.
- [x] Calculus: diff (with undefined functions), limit, Taylor (one and several
      variables), linearize, apart.
- [x] `integrate`: rational functions completely (Hermite reduction,
      Lazard–Rioboo–Trager, Rioboo's real arctangents, real factors of
      biquadratics and binomial cubics, `RootOf` sums otherwise); the
      Risch–Norman parallel integrator (exp, log, tan, powers, inverse trig,
      special functions as kernels); rules: table, parts, derivative-divides
      with inversion, Bioche's substitutions and Fourier linearisation for
      trigonometric integrands, rationalising substitutions for radicals of
      linear polynomials, √quadratic reduction and Euler substitutions;
      `erf`, `erfi`, `Ei`, `Si`, `Ci` (with numerics); every result verified by
      differentiation at sample points; definite integrals with infinite
      bounds, poles inside the interval detected, jumps of tan accounted for.
- [x] `dsolve`: first order (integrate, linear, Bernoulli, separable) with
      initial values; linear constant coefficient of any order with polynomial
      forcing; reduction of order when y is missing; boundary values; linear
      constant-coefficient systems.
- [x] `rsolve`: linear and Möbius first-order maps; linear systems.
- [x] Eco-evo: `ode`/`recurrence` models, `equilibria`, `stability` (eigenvalues
      plus exact conditions), `nullclines`, `invasion_fitness`; `ess`, `nash`,
      `replicator`, `hawk_dove`; `selection_gradient`, `classify_singular`;
      Leslie matrices, stable distribution, reproductive values, sensitivity,
      elasticity; next-generation matrix and `reproduction_number`;
      absorption probabilities and times.

- [x] Otto & Day coverage (0.2): a tested Quarto notebook for every chapter,
      primer and the perturbation appendix (`examples/`, table in the README).
      New for it: `factorial`, `binomial`, `gamma` and the gamma/beta integrals;
      `summation` (polynomial × geometric, Poisson and binomial sums) and
      `product`; `perturb` (regular perturbation of roots); `rsolve` for linear
      recurrences of any order with initial or boundary values and for
      non-autonomous first-order ones; `dsolve` with any forcing (variation of
      parameters); `matexp`/`matpow` for non-diagonalisable matrices (Putzer)
      and in real form (`realform`, `trig_linearize`); `cycles` and their
      stability, `hopf` (and Neimark–Sacker), `conserved_quantity`;
      `quasi_steady_state`; `invasion_matrix`, structured `invasion_fitness`
      and `selection_gradient`, `euler_lotka`; `stationary_distribution`,
      `pgf`, `pgf_moments`, `extinction_probability`, `fixation_probability`,
      `moran`, `wright_fisher`, `diffusion_fixation`, `diffusion_time`,
      `diffusion_stationary`; `simulate` (maps; adaptive Dormand–Prince for
      ODEs), `cobweb`, `bifurcation_data`; stochastic simulation with
      `gillespie`, `markov_path`, `wright_fisher_path`; Gaussian moments
      `∫ P(x) e^(quadratic)` over the real line.


- [x] Optional PracticalBayesPlot extension: symbolic influence graphs,
      two-variable phase portraits, and ternary game/frequency dynamics, with
      numerical trajectories, equilibria marked by local stability, and SVG,
      TikZ, and CeTZ output, in the style of PracticalProbability's diagrams.

## Next, for Otto & Day

- [ ] Kolmogorov equations through generating-function PDEs (first-order
      linear PDEs by characteristics); tau-leaping for large stochastic models.
- [ ] Singular perturbation (roots that move to infinity as ε → 0, matched
      asymptotics); averaging for weakly nonlinear oscillations.
- [ ] `dsolve`: exact and homogeneous first-order equations; linear equations
      with variable coefficients beyond reduction of order.
- [ ] Real forms of complex powers and exponentials with symbolic (sign
      unknown) discriminants; explicit Jordan forms.
- [ ] Numerical fallbacks for transcendental extinction and fixed-point
      equations with symbolic parameters (`RootOf`-style answers).

- [ ] PIP plotting, nullcline overlays, and parameter bifurcation diagrams.
- [ ] Optional Makie rendering of the backend-independent plotting data.

## Next, general CAS

- [ ] Full univariate factorisation over ℤ (Zassenhaus) and multivariate (Wang).
- [ ] Gröbner bases for polynomial systems; `RootOf` arithmetic.
- [ ] Integration, beyond the current heuristic completeness: the full Risch
      decision procedure for transcendental towers (proving non-integrability),
      algebraic functions beyond √quadratic (Trager), real forms of `RootOf`
      sums of higher degree, polylogarithms, Fresnel integrals, incomplete
      gamma; hyperbolic forms of results; precompiled workloads for latency.
- [ ] Gruntz algorithm for limits.
- [ ] Symbolic sums and products (Gosper), recurrence solving (Petkovšek).
- [ ] Piecewise functions and conditions in results (`x^(n+1)/(n+1)` for
      `n ≠ -1`).
- [ ] Inequality solving (intervals in one variable, CAD later).
- [ ] Split `core/` into `PracticalCASCore` once the API settles.
- [ ] Make PracticalProbability use this package for its numeric literals.
