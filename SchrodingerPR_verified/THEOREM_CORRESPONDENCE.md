# Step 1 — theorem correspondence

## Statement of record

The Lean theorem to prove is `CubicNLS.phase_retrieval_interval` in `showcase.lean`.
Its statement and the canonical definitions it consumes are fixed; only the `sorry` in
its proof may be replaced. It is the formal counterpart of
`cor:interval-version` in the blueprint. `CubicNLS.phase_retrieval_cubic_NLS` is the
special case `(a,b) = (0,1)` and is already derived from the interval theorem.

## Objects in the statement

- `σ : ℝ` is the real cubic coupling constant.
- `CubicNLS.L2` is Mathlib's `Lp ℂ 2 volume` on `ℝ`.
- `CubicNLS.freeProp t` is the L² Schrödinger propagator obtained by conjugating
  multiplication by `exp (-4π² i t ξ²)` through the unitary L² Fourier transform.
- `CubicNLS.GlobalSolution σ` is a continuous curve `u : ℝ → L2`, together with a
  local L⁶ spacetime bound, an L²-valued cubic nonlinearity agreeing almost everywhere
  with `|u|²u`, interval integrability of the Duhamel integrand, and the global Duhamel
  identity.
- `u v : GlobalSolution σ` are the two global mild solutions.
- `a b : ℝ` determine the observed open time interval.

## Hypotheses and conclusion

The interval is nonempty (`hab : a < b`). The product-measure hypothesis `hJ` says
that for almost every spacetime point `(t,x)`, whenever `t ∈ (a,b)`, the pointwise
norms of `u(t,x)` and `v(t,x)` agree. The conclusion is the existence of one complex
scalar `ζ` with `‖ζ‖ = 1` such that `v.u t = ζ • u.u t` in L² for every real time
`t`. The scalar is global: it does not depend on time or space.

## Direct blueprint path

The interval corollary uses `thm:main` and global uniqueness/gauge covariance from
`thm:GWP`. The main theorem uses `lem:F-vanishing`, `lem:Hilbert-wedge`, `thm:GWP`,
and `cor:all-time-density`. `lem:F-vanishing` in turn consumes the exterior-product
and coordinate definitions, the equations for `F` and `G`, the potential bounds,
the zero-extension jump formula, distributional products, and `thm:halfspace-UC`.
The resulting exterior product vanishes at every time; `lem:Hilbert-wedge` converts
that fact and equality of L² norms into a unimodular scalar at one time; uniqueness
and gauge covariance propagate that relation globally.

Blueprint anchors: `def:global-mild-solution`, `thm:GWP`,
`def:exterior-product`, `def:normal-tangential-coords`, `prop:F-equation`,
`prop:G-equation`, `lem:Q-bounds`, `prop:zero-extension-jump`,
`thm:halfspace-UC`, `lem:F-vanishing`, `lem:Hilbert-wedge`, `thm:main`, and
`cor:interval-version`.

The audit's executive verdict is that this path is mathematically self-contained down
to the pinned Mathlib foundations, but formalizing it is a large development. The
highest-risk parts are the Carleman/half-space argument, the diagonal Neumann trace,
and the critical H^{±1/2} quadratic-form interface.
