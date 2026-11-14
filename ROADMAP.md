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
      variables), linearize, apart, integrate (table, rational functions,
      substitution, parts), definite integrals with infinite bounds.
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

## Next, for Otto & Day

- [ ] Worked examples of every chapter as Quarto notebooks (`examples/`), each
      also a test.
- [ ] Periodic behaviour (ch. 11): 2-cycles of maps (`f(f(n)) = n`), Hopf
      conditions (trace = 0 with det > 0).
- [ ] Perturbation and separation of time scales (appendix): series in a small
      parameter, quasi-steady states.
- [ ] Probability primer and stochastic chapters (13–15): distributions,
      generating functions, branching-process extinction (`G(s) = s`),
      Wright–Fisher/Moran fixation, diffusion approximations (link to
      PracticalProbability).
- [ ] `dsolve` with exponential/trigonometric forcing (undetermined
      coefficients), exact equations, homogeneous equations.
- [ ] `rsolve` for linear recurrences of higher order and non-autonomous terms.
- [ ] Real forms of complex solutions of linear systems (cos/sin instead of
      complex exponentials); Jordan forms for non-diagonalisable matrices.
- [ ] Phase-plane and PIP plotting (Makie extension, via PracticalBayesPlot).

## Next, general CAS

- [ ] Full univariate factorisation over ℤ (Zassenhaus) and multivariate (Wang).
- [ ] Gröbner bases for polynomial systems; `RootOf` arithmetic.
- [ ] Risch integration for elementary functions; integrals of quadratic powers.
- [ ] Gruntz algorithm for limits.
- [ ] Symbolic sums and products (Gosper), recurrence solving (Petkovšek).
- [ ] Piecewise functions and conditions in results (`x^(n+1)/(n+1)` for
      `n ≠ -1`).
- [ ] Inequality solving (intervals in one variable, CAD later).
- [ ] Split `core/` into `PracticalCASCore` once the API settles.
- [ ] Make PracticalProbability use this package for its numeric literals.
