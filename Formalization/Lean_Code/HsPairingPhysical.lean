import Lean_Code.SmoothCriticalCurrent

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

private def besselNegativeHalfSchwartz :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ negativeHalfWeight

private lemma negativeHalfWeight_even (x : ℝ) :
    negativeHalfWeight (-x) = negativeHalfWeight x := by
  simp [negativeHalfWeight]

private lemma dualBesselTest_eq (g : SchwartzMap ℝ ℂ) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ negativeHalfWeight (𝓕⁻ g)) =
      besselNegativeHalfSchwartz g := by
  rw [besselNegativeHalfSchwartz,
    SchwartzMap.fourierMultiplierCLM_apply]
  let A : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ negativeHalfWeight (𝓕⁻ g)
  let B : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ negativeHalfWeight (𝓕 g)
  have hAB : A =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv B := by
    apply SchwartzMap.ext
    intro y
    rw [show A y = negativeHalfWeight y * (𝓕⁻ g : SchwartzMap ℝ ℂ) y by
      dsimp [A]
      exact congrFun (SchwartzMap.smulLeftCLM_apply
        hasTemperateGrowth_negativeHalfWeight _) y]
    rw [show (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv B) y =
        negativeHalfWeight (-y) * (𝓕 g : SchwartzMap ℝ ℂ) (-y) by
      rw [congrFun (SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv B) y]
      dsimp [B, Function.comp_def]
      exact congrFun (SchwartzMap.smulLeftCLM_apply
        hasTemperateGrowth_negativeHalfWeight _) (-y)]
    have hinv : (𝓕⁻ g : SchwartzMap ℝ ℂ) y =
        (𝓕 g : SchwartzMap ℝ ℂ) (-y) := by
      rw [congrFun (SchwartzMap.fourierInv_coe g) y,
        congrFun (SchwartzMap.fourier_coe g) (-y)]
      exact Real.fourierInv_eq_fourier_neg (g : ℝ → ℂ) y
    rw [hinv, negativeHalfWeight_even]
  change 𝓕 A = 𝓕⁻ B
  rw [hAB]
  apply SchwartzMap.ext
  intro x
  rw [congrFun (SchwartzMap.fourier_coe _) x,
    congrFun (SchwartzMap.fourierInv_coe B) x]
  rw [show (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv B) : ℝ → ℂ) =
      fun y : ℝ => (B : ℝ → ℂ) (-y) by
    exact SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv B]
  exact congrFun (Real.fourierInv_eq_fourier_comp_neg
    (B : ℝ → ℂ)) x |>.symm

private lemma besselNegativeHalfSchwartz_pairing_symm
    (f g : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (besselNegativeHalfSchwartz f) x * g x =
      ∫ x : ℝ, f x * (besselNegativeHalfSchwartz g) x := by
  have hdist := congrArg (fun T : 𝓢'(ℝ, ℂ) => T g)
    (TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
      hasTemperateGrowth_negativeHalfWeight f)
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply,
    dualBesselTest_eq] at hdist
  simpa [besselNegativeHalfSchwartz, mul_comm] using hdist.symm

private lemma hsHalfToL2CLM_schwartz (f : SchwartzMap ℝ ℂ) :
    hsHalfToL2CLM (f.toLp 2 volume) =
      (besselNegativeHalfSchwartz f).toLp 2 volume := by
  apply sobolevFourier.injective
  rw [hsHalfToL2CLM_apply, fourier_Hs_toL2]
  change boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
      (by norm_num) norm_negativeHalfWeight_le (𝓕 (f.toLp 2 volume)) =
    𝓕 ((besselNegativeHalfSchwartz f).toLp 2 volume)
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [coe_boundedMulCLM negativeHalfWeight
      continuous_negativeHalfWeight 1 (by norm_num)
      norm_negativeHalfWeight_le ((𝓕 f).toLp 2 volume),
    (𝓕 f).coeFn_toLp 2 volume,
    (𝓕 (besselNegativeHalfSchwartz f)).coeFn_toLp 2 volume]
      with x hmul hf hout
  rw [hmul, hf, hout]
  have hfourier : 𝓕 (besselNegativeHalfSchwartz f) =
      SchwartzMap.smulLeftCLM ℂ negativeHalfWeight (𝓕 f) := by
    rw [besselNegativeHalfSchwartz,
      SchwartzMap.fourierMultiplierCLM_apply,
      FourierTransform.fourier_fourierInv_eq]
  rw [hfourier]
  simpa [smul_eq_mul] using
    (congrFun (SchwartzMap.smulLeftCLM_apply
      hasTemperateGrowth_negativeHalfWeight (𝓕 f)) x).symm

private def besselPairLeft (p : L2 × L2) : ℂ :=
  MeasureTheory.L1.integralCLM' ℂ
    (densityProductCLM (hsHalfToL2CLM p.1) p.2)

private def besselPairRight (p : L2 × L2) : ℂ :=
  MeasureTheory.L1.integralCLM' ℂ
    (densityProductCLM p.1 (hsHalfToL2CLM p.2))

private lemma continuous_besselPairLeft : Continuous besselPairLeft := by
  apply (MeasureTheory.L1.integralCLM' ℂ).continuous.comp
  exact (densityProductCLM.continuous.comp
    (hsHalfToL2CLM.continuous.comp continuous_fst)).clm_apply continuous_snd

private lemma continuous_besselPairRight : Continuous besselPairRight := by
  apply (MeasureTheory.L1.integralCLM' ℂ).continuous.comp
  exact (densityProductCLM.continuous.comp continuous_fst).clm_apply
    (hsHalfToL2CLM.continuous.comp continuous_snd)

private lemma besselPairLeft_schwartz (f g : SchwartzMap ℝ ℂ) :
    besselPairLeft (f.toLp 2 volume, g.toLp 2 volume) =
      ∫ x : ℝ, (besselNegativeHalfSchwartz f) x * g x := by
  rw [besselPairLeft, hsHalfToL2CLM_schwartz]
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_densityProductL1
      ((besselNegativeHalfSchwartz f).toLp 2 volume) (g.toLp 2 volume),
    (besselNegativeHalfSchwartz f).coeFn_toLp 2 volume,
    g.coeFn_toLp 2 volume] with x hprod hf hg
  change (densityProductCLM
      ((besselNegativeHalfSchwartz f).toLp 2 volume)
      (g.toLp 2 volume) : ℝ → ℂ) x = _
  rw [show densityProductCLM
      ((besselNegativeHalfSchwartz f).toLp 2 volume) (g.toLp 2 volume) =
      densityProductL1 ((besselNegativeHalfSchwartz f).toLp 2 volume)
        (g.toLp 2 volume) by rfl]
  rw [hprod, hf, hg]

private lemma besselPairRight_schwartz (f g : SchwartzMap ℝ ℂ) :
    besselPairRight (f.toLp 2 volume, g.toLp 2 volume) =
      ∫ x : ℝ, f x * (besselNegativeHalfSchwartz g) x := by
  rw [besselPairRight, hsHalfToL2CLM_schwartz]
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_densityProductL1 (f.toLp 2 volume)
      ((besselNegativeHalfSchwartz g).toLp 2 volume),
    f.coeFn_toLp 2 volume,
    (besselNegativeHalfSchwartz g).coeFn_toLp 2 volume]
      with x hprod hf hg
  change (densityProductCLM (f.toLp 2 volume)
      ((besselNegativeHalfSchwartz g).toLp 2 volume) : ℝ → ℂ) x = _
  rw [show densityProductCLM (f.toLp 2 volume)
      ((besselNegativeHalfSchwartz g).toLp 2 volume) =
      densityProductL1 (f.toLp 2 volume)
        ((besselNegativeHalfSchwartz g).toLp 2 volume) by rfl]
  rw [hprod, hf, hg]

/-- The order-minus-one-half Bessel operator is symmetric for the complex
bilinear integral pairing. -/
theorem besselNegativeHalf_pairing_symm (f g : L2) :
    besselPairLeft (f, g) = besselPairRight (f, g) := by
  let e : SchwartzMap ℝ ℂ → L2 :=
    SchwartzMap.toLpCLM ℝ ℂ 2 volume
  have he : DenseRange e :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (μ := volume) (by norm_num)
  have hep : DenseRange (Prod.map e e) := he.prodMap he
  have hfun : besselPairLeft = besselPairRight := by
    apply hep.equalizer continuous_besselPairLeft continuous_besselPairRight
    funext p
    rcases p with ⟨p, q⟩
    change besselPairLeft (p.toLp 2 volume, q.toLp 2 volume) =
      besselPairRight (p.toLp 2 volume, q.toLp 2 volume)
    rw [besselPairLeft_schwartz, besselPairRight_schwartz]
    exact besselNegativeHalfSchwartz_pairing_symm p q
  exact congrFun hfun (f, g)

private lemma besselPairLeft_eq_integral (f g : L2) :
    besselPairLeft (f, g) =
      ∫ x : ℝ, (hsHalfToL2CLM f : ℝ → ℂ) x * (g : ℝ → ℂ) x := by
  rw [besselPairLeft, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_densityProductL1 (hsHalfToL2CLM f) g]
    with x hx
  change (densityProductCLM (hsHalfToL2CLM f) g : ℝ → ℂ) x = _
  rw [show densityProductCLM (hsHalfToL2CLM f) g =
    densityProductL1 (hsHalfToL2CLM f) g by rfl, hx]

private lemma besselPairRight_eq_integral (f g : L2) :
    besselPairRight (f, g) =
      ∫ x : ℝ, (f : ℝ → ℂ) x * (hsHalfToL2CLM g : ℝ → ℂ) x := by
  rw [besselPairRight, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_densityProductL1 f (hsHalfToL2CLM g)]
    with x hx
  change (densityProductCLM f (hsHalfToL2CLM g) : ℝ → ℂ) x = _
  rw [show densityProductCLM f (hsHalfToL2CLM g) =
    densityProductL1 f (hsHalfToL2CLM g) by rfl, hx]

/-- The canonical `H^{-1/2}` coordinate of a physical `L²` function. -/
def hsNegOfL2 (q : L2) : Hs (-(1 / 2 : ℝ)) :=
  hsHalfToL2CLM q

lemma hsNegOfL2_toTempered (q : L2) :
    Hs.toTempered (-(1 / 2 : ℝ)) (hsNegOfL2 q) =
      MeasureTheory.Lp.toTemperedDistribution q := by
  have hneg : TemperedDistribution.besselPotential ℝ ℂ (-(1 / 2 : ℝ))
      (MeasureTheory.Lp.toTemperedDistribution q) =
      MeasureTheory.Lp.toTemperedDistribution (hsHalfToL2CLM q) := by
    apply tempered_eq_of_fourier_eq
    rw [fourier_besselNegativeHalf_toTemperedDistribution,
      MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    congr 1
    change boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
        (by norm_num) norm_negativeHalfWeight_le (sobolevFourier q) =
      sobolevFourier (sobolevFourier.symm
        (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
          (by norm_num) norm_negativeHalfWeight_le (sobolevFourier q)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  unfold Hs.toTempered hsNegOfL2 besselMultiplier
  convert (show TemperedDistribution.besselPotential ℝ ℂ (1 / 2 : ℝ)
      (MeasureTheory.Lp.toTemperedDistribution (hsHalfToL2CLM q)) =
        MeasureTheory.Lp.toTemperedDistribution q by
      rw [← hneg]
      simp) using 1 <;> norm_num

/-- When the negative-order input is represented by an `L²` function, the
critical coordinate pairing is the ordinary complex-bilinear integral in
physical space. -/
theorem hsNegPairing_hsNegOfL2 (q : L2) (f : Hs (1 / 2 : ℝ)) :
    hsNegPairing (hsNegOfL2 q) f =
      ∫ x : ℝ, (q : ℝ → ℂ) x *
        (Hs.toL2 (by norm_num) f : ℝ → ℂ) x := by
  rw [hsNegPairing, hsNegOfL2]
  rw [← besselPairLeft_eq_integral, besselNegativeHalf_pairing_symm,
    besselPairRight_eq_integral]
  rw [hsHalfToL2CLM_apply]

end CubicNLSPhaseRetrieval
