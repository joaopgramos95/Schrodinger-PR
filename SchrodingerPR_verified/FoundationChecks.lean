import Mathlib

/-! Step 0: pinned Mathlib foundation checks. -/

#check MeasureTheory.Lp.fourierTransformₗᵢ
#check MeasureTheory.Lp.norm_fourier_eq
#check MeasureTheory.Lp.inner_fourier_eq
#check MeasureTheory.Lp.fourier_toTemperedDistribution_eq
#check TemperedDistribution.MemSobolev
#check TemperedDistribution.MemSobolev.lineDerivOp
#check TemperedDistribution.MemSobolev.laplacian
#check TemperedDistribution.besselPotential
#check TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier
#check TemperedDistribution.memSobolev_besselPotential_iff
#check ae_eq_zero_of_integral_contDiff_smul_eq_zero
