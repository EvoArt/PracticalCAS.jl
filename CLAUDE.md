# PracticalCAS.jl — notes for Claude

A computer algebra system in pure Julia (only LinearAlgebra as a dependency).
The first goal is everything needed to work through Otto & Day, *A Biologist's
Guide to Mathematical Modeling in Ecology and Evolution*, plus evolutionary game
theory (ESS) and adaptive dynamics. The long-term goal is a general CAS more
complete than Symbolics.jl. The probability layer is the sibling package
PracticalProbability.jl (`~/.julia/dev/CAS`), which should eventually use this
package for the algebra of numbers inside probability expressions.

## Running code — never locally

**Do not run Julia on the user's Windows machine** (local runs have crashed it;
even a test suite counts). Test through either:

- **GitHub Actions CI** (`.github/workflows/CI.yml`, Ubuntu, Julia 1.10 and 1):
  push to `main`, then `gh run watch` / `gh run view --log-failed`.
- **Athena** (Exeter HPC, needs the VPN): `ssh l01.athena.cles.ex.ac.uk` (or l02), Slurm
  partition `hmq`, Julia at `~/julia-1.11.1/bin/julia`. Copy the repo with
  `tar -C . -cf - --exclude=Manifest.toml . | ssh … 'tar -xf - -C ~/pcas'` and run
  `julia --project -e 'using Pkg; Pkg.test()'` in an `sbatch` job. Use a private
  directory (`~/pcas`); `~/pprob` belongs to PracticalProbability sessions.

Precompilation runs an integration workload (`src/calculus/precompile.jl`,
about 100 s); export `PRACTICALCAS_FAST_PRECOMPILE=1` in test jobs while
iterating to skip it.

## Layout and layering

`src/` is one module with directories in dependency order; a layer may use only
the layers above it in this list (keep it that way so layers can become separate
packages later, Makie-style: `PracticalCASCore` + umbrella):

1. `core/`: term types (`types.jl`), canonicalising arithmetic (`arith.jl`),
   elementary functions (`functions.jl`), symbols and assumptions (`syms.jl`,
   `assume.jl`: the sign engine with bit masks NEG/ZER/POS/CPX and exact interval
   arithmetic), traversal and `subs` (`traverse.jl`), equations and conditions
   (`relations.jl`), `diff` (`diff.jl`), numeric evaluation (`numeric.jl`), text and
   LaTeX printing (`printing.jl`).
2. `poly/`: sparse multivariate polynomials over ℚ (`mpoly.jl`: gcd by primitive
   PRS, exact division, square roots), term ↔ polynomial in "generators"
   (`convert.jl`), factorisation (`factor.jl`), the term-level API `cancel`,
   `expand`, `factor`, `polycoeffs`, … (`api.jl`).
3. `simplify/`: `simplify`, `sign_of` (sign engine + factorisation), `decide`,
   simplification of conditions.
4. `solve/`: `solve` for equations and systems (factor and branch).
5. `linalg/`: det, inv, rref, nullspace, eigen, charpoly (Faddeev–LeVerrier),
   matpow/matexp, Routh–Hurwitz and Jury (via the bilinear transform).
6. `calculus/`: limits (classify t → 0⁺ then L'Hôpital), Taylor, apart, and
   integration: `intpoly.jl` (ℚ(params) field, univariate polynomials,
   subresultants, sparse linear systems), `ratint.jl` (Hermite +
   Lazard–Rioboo–Trager), `risch_norman.jl`, `intrules.jl` (rules), and the
   driver `integrate.jl`, which verifies every candidate by differentiation.
7. `ode/`: `dsolve` (first order: integrate/linear/Bernoulli/separable; constant
   coefficient linear; order reduction; boundary values; linear systems) and
   `rsolve` (linear and Möbius maps; linear systems).
8. `ecoevo/`: models (`ode`, `recurrence`, `equilibria`, `stability`), games
   (`ess`, `nash`, `replicator`), adaptive dynamics (`classify_singular`),
   structured populations, R₀, absorbing Markov chains.

Code outside `core/` builds terms with operators or the smart constructors
(`_add`, `_mul`, `_pow`, `_exp`, `_fncall`), never the raw structs, except where a
deliberately non-canonical shape is wanted (`factor` returns `Mul(2, [(x+1) => 1])`
so it prints `2*(1 + x)`).

## Design decisions to keep

- **Canonical forms make `==` meaningful.** `Add` is constant + sorted
  `term => coeff`; `Mul` is coefficient + sorted `base => exponent`; a Mul with
  coefficient 1 and one factor is a `Pow`. Numbers distribute over a sum
  (`2(x+y) = 2x + 2y`), `exp(a)exp(b) = exp(a+b)`. Only always-valid rules are
  automatic; anything needing a sign asks the sign engine.
- **Symbols are real by default** (`@syms z::complex` to opt out). Assumptions
  live on the symbol (`SymInfo`: real, integer, bounds); relations between
  symbols are facts (`assume!`, `assuming(V < C) do … end`).
- **Numbers**: exact `Rational{BigInt}` or `Float64`. Never let a Rational meet a
  Float64 directly (it promotes to BigFloat): use `_nadd`/`_nmul`.
- **Type annotations only where they earn their place**: for dispatch, for
  extending Base on our own types (`Base.:+(a::Term, b::Number)`, avoiding
  piracy), and return annotations like `_mul(xs)::Term` (so inference gives
  `Term` and generic code such as `A * B` makes a `Matrix{Term}`). Do not annotate
  arguments of internal helpers otherwise, and never with concrete container
  types: `Pair{Term,Term}` rejects a `Pair{Sym,Num}` (parametric types are
  invariant); that caused most failures of the first test run.
- **Typed containers**: `fill(ZERO, n)` is a `Vector{Num}`; use `_tzeros(n)` or
  `Term[...]` when entries will become other terms.
- **Exports avoid common model symbols**: numeric evaluation is `evalf` (not
  `N`, population size), R₀ is `reproduction_number`; `D`, `lhs`, `rhs` are not
  exported.
- Conditions (`a < b` on terms) are `Rel` objects; `decide` returns
  `true`/`false`/`nothing`; `simplify` on a condition drops factors of known sign.

## Tests

`test/runtests.jl` includes one file per layer. Tests check results by
`isequiv` (`≅`) or numerically (`numeq`), not by printed form, except in the
printing tests. Every Otto & Day style result should get a test (equilibria,
stability verdicts and conditions, solutions checked by substituting back).

## Docs

`README.md` (overview and examples), `ROADMAP.md` (what is done and what is
next; keep it current).
