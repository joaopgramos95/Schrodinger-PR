# Step 0 — pinned Mathlib foundation report

Verified with Lean 4.32.0 and Mathlib v4.32.0 at commit
`81a5d257c8e410db227a6665ed08f64fea08e997` using:

```text
lake env lean FoundationChecks.lean
lake build
```

Both commands succeeded.

| Entry point requested by the workflow | Exists verbatim? | Actual name to use |
|---|---:|---|
| L² Fourier isometry | yes | `MeasureTheory.Lp.fourierTransformₗᵢ` |
| Fourier norm identity | yes | `MeasureTheory.Lp.norm_fourier_eq` |
| Fourier inner-product identity | yes | `MeasureTheory.Lp.inner_fourier_eq` |
| Fourier/tempered-distribution bridge | yes | `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` |
| Sobolev predicate | yes | `TemperedDistribution.MemSobolev` |
| Directional derivative on Sobolev distributions | yes | `TemperedDistribution.MemSobolev.lineDerivOp` |
| Laplacian on Sobolev distributions | yes | `TemperedDistribution.MemSobolev.laplacian` |
| Bessel potential | yes | `TemperedDistribution.besselPotential` |
| p=2 Fourier characterization under the name `memSobolev_two_iff_fourier` | no | `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` |
| Bessel-potential characterization | yes | `TemperedDistribution.memSobolev_besselPotential_iff` |
| du Bois–Reymond leaf | yes | `ae_eq_zero_of_integral_contDiff_smul_eq_zero` |

The remaining foundational categories named by the workflow are supplied by the
successfully imported top-level `Mathlib` at this revision. Their source modules are
the Gaussian Fourier transform, `AbsMax`, `PhragmenLindelof`, weak dual/Banach–Alaoglu,
convolution/Young, simple-function and Schwartz density, and the interval-integral FTC
and absolute-continuity modules. The only absent leaf identified by the workflow is the
off-main-path variable-coefficient integral Grönwall lemma, which the blueprint proves.
