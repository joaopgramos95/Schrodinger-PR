# Blueprint build order

Generated mechanically from `paper_blueprint.tex`. Statement and proof `\uses` are kept separate.

- Numbered declarations: **144**
- Dependency edges: **370**
- Missing dependency labels: **0**
- Topologically emitted declarations: **144**
- Cyclic declarations: **0**
- Appendix module-order violations: **1**
- DAG verdict: **acyclic and closed**

## Appendix module-order exceptions

The declaration DAG remains acyclic, but these source-level `\uses` edges point from an earlier appendix module to a later one. The implementation must make the utility generic, relocate it, or refine imports without introducing a cycle.

- `lem:distributional-products` (Utilities.lean) uses `def:exterior-product` (WronskianExterior.lean).

## Leaves-first order grouped by Lean module

### Setup — `Lean_Code/Setup.lean`

Blueprint chapter: `chap:setup` (The equation and the solution class). Declarations: 1.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:cubic-nls` | — | — | — |

### Module 0 — `Lean_Code/ScalarMixedNorms.lean`

Blueprint chapter: `chap:mixed-norms` (Scalar mixed norms and representatives). Declarations: 12.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | convention | `conv:joint-representatives` | — | — | — |
| 2 | lemma | `lem:measurable-esssup-section` | `conv:joint-representatives` | `conv:joint-representatives` | — |
| 3 | definition | `def:scalar-mixed-norm` | `conv:joint-representatives`, `lem:measurable-esssup-section` | — | — |
| 4 | lemma | `lem:scalar-endpoint-complete` | `def:scalar-mixed-norm` | `def:scalar-mixed-norm` | paper.tex L328-L358 |
| 5 | lemma | `lem:scalar-mixed-minkowski` | `def:scalar-mixed-norm` | `def:scalar-mixed-norm`, `lem:measurable-esssup-section` | — |
| 6 | lemma | `lem:countable-norming-Linfty` | — | — | — |
| 7 | proposition | `prop:endpoint-norming` | `def:scalar-mixed-norm`, `lem:countable-norming-Linfty` | `def:scalar-mixed-norm`, `lem:countable-norming-Linfty` | paper.tex L441-L472 |
| 8 | lemma | `lem:mixed-subsequence-uniform` | `def:scalar-mixed-norm`, `lem:scalar-endpoint-complete` | `lem:scalar-endpoint-complete` | — |
| 9 | lemma | `lem:C0-limit-identification` | `lem:mixed-subsequence-uniform` | `lem:mixed-subsequence-uniform` | — |
| 10 | definition | `def:sum-intersection-norm` | `def:scalar-mixed-norm` | — | — |
| 11 | lemma | `lem:sum-intersection-complete` | `def:sum-intersection-norm` | `def:sum-intersection-norm` | — |
| 12 | lemma | `lem:joint-representative-L2` | `conv:joint-representatives`, `def:scalar-mixed-norm` | `conv:joint-representatives`, `def:scalar-mixed-norm` | paper.tex L567-L600 |

### Module 1 — `Lean_Code/FourierSobolev.lean`

Blueprint chapter: `chap:fourier` (Fourier analysis and the $H^{s}$ calculus). Declarations: 16.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:fourier-convention` | — | — | — |
| 2 | definition | `def:homogeneous-multiplier` | `def:fourier-convention` | — | — |
| 3 | definition | `def:Hs-space` | `def:fourier-convention`, `def:homogeneous-multiplier` | — | — |
| 4 | definition | `def:Hs-neg-pairing` | `def:Hs-space` | — | — |
| 5 | definition | `def:Hs-loc` | `def:Hs-space` | — | — |
| 6 | lemma | `lem:gagliardo-fourier-identity` | `def:Hs-space` | `def:fourier-convention` | — |
| 7 | lemma | `lem:gagliardo-mollification` | `def:Hs-space` | `lem:gagliardo-fourier-identity` | — |
| 8 | lemma | `lem:gagliardo-cutoff-error` | `def:Hs-space` | — | — |
| 9 | lemma | `lem:gagliardo-density` | `def:Hs-space` | `lem:gagliardo-fourier-identity`, `lem:gagliardo-mollification`, `lem:gagliardo-cutoff-error` | — |
| 10 | theorem | `thm:fourier-gagliardo` | `def:Hs-space` | `lem:gagliardo-fourier-identity`, `lem:gagliardo-mollification`, `lem:gagliardo-cutoff-error`, `lem:gagliardo-density` | paper.tex L669-L772 |
| 11 | lemma | `lem:smooth-multiplier-quantitative` | `def:Hs-space` | `thm:fourier-gagliardo` | — |
| 12 | lemma | `lem:translation-dq` | `def:Hs-space` | — | — |
| 13 | lemma | `lem:Wp-difference-quotient` | — | — | paper.tex L825-L851 |
| 14 | lemma | `lem:H1-C0` | `lem:Wp-difference-quotient` | — | paper.tex L853-L887 |
| 15 | lemma | `lem:realpart-logform` | `lem:H1-C0` | `lem:H1-C0` | — |
| 16 | lemma | `lem:tensor-norm` | — | — | — |

### Module 2 — `Lean_Code/FreeSchrodinger.lean`

Blueprint chapter: `chap:free-group` (The free Schr\"odinger group). Declarations: 6.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:propagator` | `def:fourier-convention` | — | — |
| 2 | lemma | `lem:propagator-unitary` | `def:propagator` | `def:propagator` | — |
| 3 | lemma | `lem:complex-gaussian-kernel` | — | — | — |
| 4 | lemma | `lem:free-kernel-explicit` | `lem:complex-gaussian-kernel`, `def:propagator` | `lem:complex-gaussian-kernel`, `def:propagator`, `lem:propagator-unitary` | — |
| 5 | lemma | `lem:dispersive-1d` | `lem:free-kernel-explicit`, `def:propagator` | `lem:free-kernel-explicit` | — |
| 6 | lemma | `lem:propagator-compatibility` | `def:propagator`, `lem:free-kernel-explicit` | `lem:free-kernel-explicit`, `lem:complex-gaussian-kernel`, `lem:propagator-unitary` | — |

### Module 3 — `Lean_Code/FractionalIntegration.lean`

Blueprint chapter: `chap:frac-int` (Interpolation and fractional integration). Declarations: 7.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:three-lines-explicit` | — | — | paper.tex L1024-L1055 |
| 2 | lemma | `lem:riesz-thorin-used` | — | `lem:three-lines-explicit` | paper.tex L1080-L1111 |
| 3 | definition | `def:maximal-function` | — | — | — |
| 4 | lemma | `lem:maximal-weak11` | `def:maximal-function` | `def:maximal-function` | — |
| 5 | lemma | `lem:maximal-strongp` | `def:maximal-function` | `lem:maximal-weak11` | — |
| 6 | lemma | `lem:hedberg` | `def:maximal-function` | `def:maximal-function` | — |
| 7 | lemma | `lem:HLS-time` | — | `lem:maximal-strongp`, `lem:hedberg` | paper.tex L1139-L1204 |

### Module 12 — `Lean_Code/Utilities.lean`

Blueprint chapter: `chap:utilities` (Distributional utilities). Declarations: 3.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:tensor-test-density` | — | — | paper.tex L4313–L4356 |
| 2 | lemma | `lem:distribution-slicing` | `lem:tensor-test-density` | `lem:tensor-test-density` | — |
| 3 | lemma | `lem:distributional-products` | `def:exterior-product` | `def:exterior-product` | — |

### Module 4 — `Lean_Code/Strichartz1D.lean`

Blueprint chapter: `chap:strichartz` (Strichartz estimates). Declarations: 8.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:admissible-pairs` | — | — | — |
| 2 | lemma | `lem:TTstar-finite` | `def:admissible-pairs`, `def:propagator`, `def:scalar-mixed-norm` | `lem:dispersive-1d`, `lem:HLS-time`, `lem:propagator-compatibility` | — |
| 3 | lemma | `lem:TTstar-endpoint` | `def:propagator`, `def:scalar-mixed-norm` | `lem:dispersive-1d`, `lem:HLS-time`, `prop:endpoint-norming` | — |
| 4 | lemma | `lem:strichartz-endpoint-identification` | `def:propagator`, `def:scalar-mixed-norm` | `lem:mixed-subsequence-uniform` | — |
| 5 | theorem | `thm:hom-strichartz` | `def:admissible-pairs`, `def:propagator` | `lem:TTstar-finite`, `lem:TTstar-endpoint`, `lem:strichartz-endpoint-identification`, `lem:dispersive-1d`, `prop:endpoint-norming`, `lem:propagator-unitary` | paper.tex L1225-L1320 |
| 6 | lemma | `lem:CK` | — | — | — |
| 7 | theorem | `thm:inhom-str` | `def:propagator` | `thm:hom-strichartz`, `lem:CK` | — |
| 8 | lemma | `lem:retarded-continuous` | `thm:inhom-str`, `def:sum-intersection-norm`, `def:propagator` | `thm:inhom-str`, `lem:propagator-unitary`, `lem:scalar-mixed-minkowski` | — |

### Module 5 — `Lean_Code/CubicFlow.lean`

Blueprint chapter: `chap:wellposed` (Global $L^2$ well-posedness). Declarations: 12.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:fixed-point-space` | `def:scalar-mixed-norm` | — | — |
| 2 | definition | `def:mild-solution` | `def:cubic-nls`, `def:propagator` | — | — |
| 3 | definition | `def:global-mild-solution` | `def:mild-solution`, `def:fixed-point-space`, `def:scalar-mixed-norm`, `lem:joint-representative-L2` | — | — |
| 4 | lemma | `lem:cubic-65` | `def:fixed-point-space` | `def:scalar-mixed-norm` | — |
| 5 | lemma | `lem:cubic-lip` | `def:fixed-point-space`, `lem:cubic-65` | `lem:cubic-65` | — |
| 6 | theorem | `thm:LWP` | `def:fixed-point-space`, `thm:inhom-str`, `lem:retarded-continuous`, `lem:cubic-65`, `lem:cubic-lip` | `thm:hom-strichartz`, `thm:inhom-str`, `lem:cubic-65`, `lem:cubic-lip`, `lem:retarded-continuous` | paper.tex L1536-L1576 |
| 7 | lemma | `lem:cubic-derivative-map` | `def:fixed-point-space` | `lem:cubic-65` | paper.tex L1608-L1622 |
| 8 | lemma | `lem:H1-persistence` | `lem:cubic-derivative-map`, `lem:Wp-difference-quotient`, `def:fixed-point-space` | `thm:inhom-str`, `lem:cubic-derivative-map`, `lem:Wp-difference-quotient`, `lem:H1-C0` | paper.tex L1639-L1701 |
| 9 | lemma | `lem:gelfand-chain-rule` | `def:Hs-space` | `def:Hs-space` | paper.tex L1722-L1743 |
| 10 | lemma | `lem:mass-H1` | `lem:gelfand-chain-rule`, `lem:H1-persistence` | `lem:gelfand-chain-rule` | — |
| 11 | proposition | `prop:mass-L2` | `thm:LWP` | `thm:LWP`, `lem:H1-persistence`, `lem:mass-H1` | — |
| 12 | theorem | `thm:GWP` | `thm:LWP`, `prop:mass-L2`, `def:fixed-point-space` | `thm:LWP`, `prop:mass-L2` | — |

### Module 6 — `Lean_Code/EndpointRegularity.lean`

Blueprint chapter: `chap:endpoint` (Persistence and endpoint regularity). Declarations: 7.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:Xk-space` | `def:fixed-point-space`, `def:Hs-space` | — | — |
| 2 | lemma | `lem:cubic-Hk-leibniz` | `def:Xk-space`, `def:scalar-mixed-norm`, `lem:cubic-derivative-map` | `lem:cubic-derivative-map` | — |
| 3 | proposition | `prop:Hk-persistence` | `def:Xk-space`, `lem:cubic-Hk-leibniz`, `thm:GWP` | `lem:H1-persistence`, `thm:LWP`, `thm:inhom-str`, `lem:cubic-Hk-leibniz`, `lem:cubic-derivative-map`, `lem:Wp-difference-quotient`, `thm:GWP` | paper.tex L1891-L1994 |
| 4 | lemma | `lem:schwartz-smooth` | `prop:Hk-persistence` | `prop:Hk-persistence` | — |
| 5 | lemma | `lem:interp-L8L4` | `def:scalar-mixed-norm` | — | — |
| 6 | proposition | `prop:endpoint` | `thm:hom-strichartz`, `thm:GWP`, `lem:scalar-mixed-minkowski`, `lem:interp-L8L4` | `thm:hom-strichartz`, `thm:GWP`, `lem:scalar-mixed-minkowski`, `lem:interp-L8L4`, `lem:retarded-continuous` | paper.tex L2024-L2063 |
| 7 | corollary | `cor:C0-slices` | `prop:endpoint`, `lem:H1-C0`, `lem:C0-limit-identification` | `prop:Hk-persistence`, `prop:endpoint`, `lem:mixed-subsequence-uniform`, `lem:H1-C0`, `lem:C0-limit-identification` | — |

### Module 7 — `Lean_Code/LocalSmoothing1D.lean`

Blueprint chapter: `chap:smoothing` (Local smoothing by one half derivative). Declarations: 7.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:homogeneous-smoothing-identity` | `def:propagator`, `def:homogeneous-multiplier`, `def:Hs-space` | `def:propagator`, `def:homogeneous-multiplier` | — |
| 2 | definition | `def:Ax-representative` | `def:homogeneous-multiplier`, `def:propagator`, `lem:homogeneous-smoothing-identity` | — | — |
| 3 | lemma | `lem:point-smoothing` | `def:Ax-representative`, `lem:homogeneous-smoothing-identity`, `def:propagator`, `def:homogeneous-multiplier` | `lem:homogeneous-smoothing-identity`, `def:Ax-representative` | paper.tex L2109-L2156 |
| 4 | corollary | `cor:hom-smoothing` | `lem:point-smoothing`, `def:propagator`, `def:Hs-space`, `def:scalar-mixed-norm` | `lem:point-smoothing` | — |
| 5 | lemma | `lem:Duhamel-smoothing` | `cor:hom-smoothing`, `thm:inhom-str`, `def:propagator`, `def:Hs-space`, `def:scalar-mixed-norm` | `cor:hom-smoothing` | — |
| 6 | corollary | `cor:NLS-smoothing` | `lem:Duhamel-smoothing`, `prop:endpoint` | `lem:Duhamel-smoothing`, `prop:endpoint` | — |
| 7 | lemma | `lem:countable-full-measure` | `cor:NLS-smoothing`, `cor:C0-slices`, `def:Hs-loc` | `cor:NLS-smoothing`, `cor:C0-slices` | — |

### Module 8 — `Lean_Code/CriticalQuadraticForms.lean`

Blueprint chapter: `chap:critical-calculus` (Critical $H^{1/2}$ calculus and the current). Declarations: 9.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:gagliardo-product` | `def:Hs-space` | `thm:fourier-gagliardo`, `lem:smooth-multiplier-quantitative` | — |
| 2 | lemma | `lem:lipschitz-composition` | `def:Hs-space` | `thm:fourier-gagliardo`, `lem:gagliardo-product` | — |
| 3 | lemma | `lem:mollification-critical-uniform` | `def:Hs-space`, `def:fourier-convention` | `def:fourier-convention`, `thm:fourier-gagliardo` | — |
| 4 | definition | `def:Teps-regularizer` | — | — | — |
| 5 | lemma | `lem:Teps` | `def:Teps-regularizer`, `def:Hs-loc` | `def:Teps-regularizer`, `thm:fourier-gagliardo` | paper.tex L2348-L2372 |
| 6 | definition | `def:multiplier-test-algebra` | `def:Hs-space` | — | — |
| 7 | definition | `def:quadratic-form-current` | `def:Hs-neg-pairing`, `def:multiplier-test-algebra`, `def:Hs-loc` | — | — |
| 8 | lemma | `lem:current-locality` | `def:quadratic-form-current`, `def:Hs-loc` | `def:quadratic-form-current`, `lem:smooth-multiplier-quantitative` | — |
| 9 | lemma | `lem:quadratic-form-extension` | `def:quadratic-form-current`, `def:multiplier-test-algebra` | `lem:gagliardo-product`, `lem:smooth-multiplier-quantitative`, `def:Hs-neg-pairing` | paper.tex L2420-L2436 |

### Module 9 — `Lean_Code/DensityCurrent.lean`

Blueprint chapter: `chap:current` (The density determines the current). Declarations: 5.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | corollary | `cor:all-time-density` | `thm:GWP`, `cor:C0-slices` | `thm:GWP`, `cor:C0-slices` | — |
| 2 | lemma | `lem:smooth-continuity-equation` | `def:propagator` | `lem:gelfand-chain-rule` | paper.tex L2545–L2573 |
| 3 | definition | `def:endpoint-current` | `def:quadratic-form-current`, `def:Hs-neg-pairing`, `lem:current-locality` | — | — |
| 4 | theorem | `thm:current-recovery` | `def:endpoint-current`, `def:quadratic-form-current` | `def:endpoint-current`, `lem:smooth-continuity-equation`, `lem:realpart-logform`, `lem:tensor-test-density`, `lem:distribution-slicing`, `lem:quadratic-form-extension`, `cor:all-time-density`, `prop:endpoint`, `cor:NLS-smoothing` | paper.tex L2599–L2671 |
| 5 | corollary | `cor:density-equal-current` | `def:endpoint-current` | `thm:current-recovery`, `cor:all-time-density` | — |

### Module 10 — `Lean_Code/WronskianExterior.lean`

Blueprint chapter: `chap:wronskian-exterior` (Wronskian and the exterior product). Declarations: 9.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:wronskian-smooth-approx` | `def:Hs-space`, `def:Hs-loc` | `prop:endpoint`, `cor:NLS-smoothing` | — |
| 2 | lemma | `lem:wronskian-zero-set-safe` | `def:Hs-space`, `def:Teps-regularizer` | `lem:lipschitz-composition`, `lem:gagliardo-product` | — |
| 3 | definition | `def:exterior-product` | `def:fixed-point-space` | — | — |
| 4 | lemma | `lem:wronskian-current-form` | `def:quadratic-form-current`, `def:Teps-regularizer` | `lem:quadratic-form-extension`, `lem:mollification-critical-uniform`, `lem:Teps`, `cor:density-equal-current` | — |
| 5 | theorem | `thm:critical-wronskian` | `def:Hs-space`, `def:Hs-loc`, `def:Hs-neg-pairing` | `lem:wronskian-smooth-approx`, `lem:wronskian-zero-set-safe`, `lem:wronskian-current-form` | paper.tex L2696-L2781 |
| 6 | corollary | `cor:diagonal-W` | `thm:critical-wronskian` | `thm:critical-wronskian`, `thm:current-recovery`, `lem:countable-full-measure`, `cor:density-equal-current` | — |
| 7 | proposition | `prop:F-equation` | `def:exterior-product`, `cor:diagonal-W` | `lem:tensor-norm`, `prop:endpoint`, `prop:mass-L2`, `thm:GWP` | paper.tex L2846-L2898 |
| 8 | definition | `def:normal-tangential-coords` | `def:exterior-product`, `prop:F-equation` | — | — |
| 9 | lemma | `lem:Q-bounds` | `def:normal-tangential-coords`, `prop:F-equation` | `prop:endpoint` | — |

### Module 11 — `Lean_Code/DiagonalTrace.lean`

Blueprint chapter: `chap:traces` (Distribution-valued diagonal traces). Declarations: 13.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:interior-first-derivative` | `def:Hs-space` | — | — |
| 2 | lemma | `lem:H2-weak-limit` | `lem:interior-first-derivative` | `lem:interior-first-derivative` | — |
| 3 | theorem | `thm:local-H2-characterization` | `def:Hs-space` | `lem:H2-weak-limit`, `lem:H1-C0` | paper.tex L3009--L3026 |
| 4 | lemma | `lem:translated-test-multiplier` | `lem:smooth-multiplier-quantitative` | `lem:smooth-multiplier-quantitative` | — |
| 5 | lemma | `lem:scalarization-normal` | `def:normal-tangential-coords`, `def:exterior-product` | `prop:F-equation`, `thm:local-H2-characterization` | — |
| 6 | definition | `def:dirichlet-trace` | `lem:scalarization-normal`, `thm:local-H2-characterization` | — | — |
| 7 | proposition | `prop:Dirichlet-trace` | `def:dirichlet-trace` | `def:exterior-product`, `lem:scalarization-normal` | — |
| 8 | definition | `def:neumann-trace` | `lem:scalarization-normal`, `thm:local-H2-characterization` | — | — |
| 9 | lemma | `lem:neumann-localization` | `def:neumann-trace` | `cor:NLS-smoothing` | — |
| 10 | lemma | `lem:neumann-strong-convergence` | `lem:translated-test-multiplier`, `def:Hs-neg-pairing`, `lem:translation-dq` | `lem:translation-dq`, `lem:neumann-localization` | — |
| 11 | proposition | `prop:Neumann-trace` | `def:neumann-trace` | `lem:neumann-localization`, `lem:neumann-strong-convergence`, `lem:translated-test-multiplier`, `cor:diagonal-W` | paper.tex L3087--L3205 |
| 12 | proposition | `prop:zero-extension-jump` | `prop:Dirichlet-trace`, `prop:Neumann-trace`, `def:exterior-product` | `prop:Dirichlet-trace`, `prop:Neumann-trace`, `lem:tensor-test-density` | paper.tex L3223--L3248 |
| 13 | proposition | `prop:G-equation` | `def:normal-tangential-coords`, `prop:F-equation`, `prop:zero-extension-jump`, `def:exterior-product` | `prop:zero-extension-jump`, `prop:F-equation`, `lem:Q-bounds` | paper.tex L3207-L3257 |

### Module 13 — `Lean_Code/Carleman2D.lean`

Blueprint chapter: `chap:carleman` (A self-contained half-space Carleman theorem). Declarations: 15.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:carleman-spaces` | `def:scalar-mixed-norm`, `def:sum-intersection-norm` | — | — |
| 2 | definition | `def:conjugated-operator` | `def:propagator` | — | — |
| 3 | definition | `def:Tbeta` | `def:conjugated-operator` | — | — |
| 4 | lemma | `lem:Tbeta-symbol` | `def:Tbeta`, `def:conjugated-operator` | `def:Tbeta` | — |
| 5 | lemma | `lem:vandercorput-kernel` | — | — | paper.tex L3373-3412 |
| 6 | lemma | `lem:K-homogeneous` | `def:conjugated-operator`, `def:scalar-mixed-norm` | `lem:Tbeta-symbol`, `lem:vandercorput-kernel`, `lem:riesz-thorin-used`, `lem:HLS-time` | paper.tex L3447-3491 |
| 7 | lemma | `lem:Tbeta-kernel` | `def:Tbeta` | `lem:Tbeta-symbol`, `lem:vandercorput-kernel`, `lem:complex-gaussian-kernel`, `lem:riesz-thorin-used` | paper.tex L3352-3433 |
| 8 | lemma | `lem:XY-multiplier` | `def:carleman-spaces` | `def:carleman-spaces` | — |
| 9 | proposition | `prop:linear-carleman` | `def:conjugated-operator`, `def:carleman-spaces` | `lem:Tbeta-kernel`, `lem:K-homogeneous`, `lem:HLS-time`, `def:Tbeta`, `lem:sum-intersection-complete` | paper.tex L3503-3547 |
| 10 | lemma | `lem:spatial-mollification-source` | `def:carleman-spaces` | — | — |
| 11 | lemma | `lem:compact-support-ODE` | — | — | — |
| 12 | lemma | `lem:parameterwise-distribution-ODE` | `def:conjugated-operator` | — | paper.tex L3581-L3643 |
| 13 | lemma | `lem:fourier-section-identification` | `def:conjugated-operator`, `def:carleman-spaces`, `def:Tbeta` | `lem:parameterwise-distribution-ODE`, `lem:compact-support-ODE`, `def:Tbeta`, `prop:linear-carleman` | paper.tex L3689-3720 |
| 14 | lemma | `lem:carleman-closure` | `def:conjugated-operator`, `def:carleman-spaces` | `lem:spatial-mollification-source`, `lem:fourier-section-identification`, `prop:linear-carleman` | paper.tex L3732-3779 |
| 15 | lemma | `lem:exponential-separation` | `def:carleman-spaces`, `def:conjugated-operator` | `lem:carleman-closure`, `lem:XY-multiplier` | — |

### Module 14 — `Lean_Code/HalfspacePropagation.lean`

Blueprint chapter: `chap:halfspace` (Half-space propagation). Declarations: 7.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | definition | `def:moving-interface-scale` | `def:carleman-spaces` | — | — |
| 2 | lemma | `lem:moving-galilean-distribution` | `def:conjugated-operator` | — | paper.tex L3838-L3866 |
| 3 | lemma | `lem:moment-error` | `def:carleman-spaces` | — | paper.tex L3819-L3833 |
| 4 | lemma | `lem:one-slab` | `def:carleman-spaces` | `lem:carleman-closure`, `lem:XY-multiplier`, `lem:exponential-separation` | — |
| 5 | lemma | `lem:one-step-propagation` | `lem:one-slab`, `def:moving-interface-scale` | `lem:one-slab`, `lem:XY-multiplier`, `lem:moving-galilean-distribution`, `lem:moment-error`, `def:moving-interface-scale` | paper.tex L3920-L4033 |
| 6 | theorem | `thm:halfspace-UC` | `def:scalar-mixed-norm` | `lem:one-step-propagation`, `def:moving-interface-scale` | paper.tex L4051-L4079 |
| 7 | corollary | `cor:halfspace-XY` | `def:carleman-spaces` | `thm:halfspace-UC`, `lem:XY-multiplier`, `lem:one-slab` | — |

### Module 15 — `Lean_Code/PhaseRetrieval.lean`

Blueprint chapter: `chap:completion` (Completion of the phase-retrieval proof). Declarations: 7.

| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |
|---:|---|---|---|---|---|
| 1 | lemma | `lem:F-vanishing` | `def:exterior-product`, `def:normal-tangential-coords`, `prop:G-equation`, `prop:F-equation`, `lem:Q-bounds` | `prop:G-equation`, `prop:zero-extension-jump`, `thm:halfspace-UC`, `lem:distributional-products` | paper.tex L4106-L4142 |
| 2 | lemma | `lem:Hilbert-wedge` | — | — | — |
| 3 | theorem | `thm:main` | `thm:GWP` | `lem:F-vanishing`, `lem:Hilbert-wedge`, `thm:GWP`, `cor:all-time-density` | — |
| 4 | corollary | `cor:interval-version` | `thm:GWP` | `thm:main`, `thm:GWP` | — |
| 5 | corollary | `cor:H1-case` | — | `thm:main`, `lem:H1-persistence` | — |
| 6 | lemma | `lem:integral-gronwall` | — | — | — |
| 7 | corollary | `cor:linear-common-potential` | — | `thm:critical-wronskian`, `prop:zero-extension-jump`, `cor:halfspace-XY`, `lem:Hilbert-wedge`, `lem:integral-gronwall` | — |
