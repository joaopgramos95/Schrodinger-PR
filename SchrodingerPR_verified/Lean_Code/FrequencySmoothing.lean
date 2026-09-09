import Lean_Code.NLSLocalSmoothing

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- Resolvent regularizer in frequency.  The scale is `n+1`, so there is no
exceptional index. -/
def resolventSymbol (n : ℕ) (ξ : ℝ) : ℂ :=
  (((1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ : ℝ) : ℂ)

lemma continuous_resolventSymbol (n : ℕ) :
    Continuous (resolventSymbol n) := by
  unfold resolventSymbol
  have hden : Continuous (fun ξ : ℝ => 1 + ξ ^ 2 / (n + 1 : ℝ)) :=
    continuous_const.add ((continuous_id.pow 2).div_const (n + 1 : ℝ))
  exact Complex.continuous_ofReal.comp
    (hden.inv₀ (fun ξ => ne_of_gt (by positivity)))

lemma norm_resolventSymbol_le_one (n : ℕ) (ξ : ℝ) :
    ‖resolventSymbol n ξ‖ ≤ 1 := by
  rw [resolventSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_pos (by positivity : 0 < 1 + ξ ^ 2 / (n + 1 : ℝ))]
  rw [inv_le_one₀ (by positivity)]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg ξ) (by positivity))

/-- Spatial frequency regularization on `L²`. -/
def frequencySmoothCLM (n : ℕ) : L2 →L[ℂ] L2 :=
  fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
      1 (by norm_num) (norm_resolventSymbol_le_one n)).comp
        fourierL2.toContinuousLinearEquiv.toContinuousLinearMap)

lemma fourier_frequencySmoothCLM (n : ℕ) (f : L2) :
    fourierL2 (frequencySmoothCLM n f) =
      boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
        1 (by norm_num) (norm_resolventSymbol_le_one n) (fourierL2 f) := by
  simp [frequencySmoothCLM]

lemma coe_fourier_frequencySmoothCLM (n : ℕ) (f : L2) :
    (fourierL2 (frequencySmoothCLM n f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => resolventSymbol n ξ * (fourierL2 f : ℝ → ℂ) ξ := by
  rw [fourier_frequencySmoothCLM]
  exact coe_boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
    1 (by norm_num) (norm_resolventSymbol_le_one n) _

lemma norm_frequencySmoothCLM_le (n : ℕ) (f : L2) :
    ‖frequencySmoothCLM n f‖ ≤ ‖f‖ := by
  rw [← fourierL2.norm_map]
  rw [fourier_frequencySmoothCLM]
  calc
    _ ≤ ‖boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
        1 (by norm_num) (norm_resolventSymbol_le_one n)‖ * ‖fourierL2 f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖fourierL2 f‖ := by
      gcongr
      exact norm_boundedMulCLM_le _ _ _ _ _
    _ = ‖f‖ := by rw [one_mul, fourierL2.norm_map]

lemma frequencySmoothCLM_comm_freeProp (n : ℕ) (t : ℝ) (f : L2) :
    frequencySmoothCLM n (freeProp t f) =
      freeProp t (frequencySmoothCLM n f) := by
  apply fourierL2.injective
  apply Lp.ext
  filter_upwards [coe_fourier_frequencySmoothCLM n (freeProp t f),
    fourier_freeProp t f,
    fourier_freeProp t (frequencySmoothCLM n f),
    coe_fourier_frequencySmoothCLM n f] with ξ hl hfree hr hs
  rw [hl, hfree, hr, hs]
  ring

private lemma resolventSymbol_tendsto_one (ξ : ℝ) :
    Tendsto (fun n : ℕ => resolventSymbol n ξ) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1 <;>
      simp [Function.comp_def]
  have hi : Tendsto (fun n : ℕ => ξ ^ 2 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hn.inv_tendsto_atTop
  have hreal : Tendsto (fun n : ℕ =>
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹) atTop (𝓝 1) := by
    have hadd : Tendsto (fun n : ℕ => 1 + ξ ^ 2 / (n + 1 : ℝ))
        atTop (𝓝 (1 : ℝ)) :=
      by
        convert (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hi using 1 <;>
          norm_num
    convert hadd.inv₀ one_ne_zero using 1 <;> norm_num
  change Tendsto (fun n : ℕ =>
    (((1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ : ℝ) : ℂ)) atTop (𝓝 1)
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal

theorem frequencySmoothCLM_tendsto (f : L2) :
    Tendsto (fun n : ℕ => frequencySmoothCLM n f) atTop (𝓝 f) := by
  let g := fourierL2 f
  have hfreq : Tendsto (fun n : ℕ =>
      boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
        1 (by norm_num) (norm_resolventSymbol_le_one n) g) atTop (𝓝 g) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hraw (n : ℕ) :
        eLpNorm
          ((boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
              1 (by norm_num) (norm_resolventSymbol_le_one n) g : ℝ → ℂ) -
            (g : ℝ → ℂ)) 2 volume =
        eLpNorm (fun ξ => (resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ)
          2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [coe_boundedMulCLM (resolventSymbol n)
        (continuous_resolventSymbol n) 1 (by norm_num)
        (norm_resolventSymbol_le_one n) g] with ξ hm
      rw [Pi.sub_apply, hm]
      ring
    simp_rw [hraw]
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    have hint : Tendsto (fun n : ℕ =>
        ∫⁻ ξ, ‖(resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)
          ∂volume) atTop (𝓝 0) := by
      have hmeas (n : ℕ) : AEMeasurable (fun ξ =>
          ‖(resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) volume :=
        ((((continuous_resolventSymbol n).aestronglyMeasurable.sub
          continuous_const.aestronglyMeasurable).mul
            (Lp.aestronglyMeasurable g)).enorm.pow_const 2)
      have hbound (n : ℕ) : ∀ᵐ ξ : ℝ ∂volume,
          ‖(resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ≤
            4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
        filter_upwards with ξ
        have hs : ‖resolventSymbol n ξ - 1‖ ≤ 2 :=
          (norm_sub_le _ _).trans (by
            rw [norm_one]
            linarith [norm_resolventSymbol_le_one n ξ])
        have hse : ‖resolventSymbol n ξ - 1‖ₑ ≤ 2 := by
          rw [← ofReal_norm]
          simpa using ENNReal.ofReal_le_ofReal hs
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        calc
          _ ≤ (2 : ℝ≥0∞) ^ (2 : ℝ) * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by gcongr
          _ = _ := by norm_num
      have hfin : (∫⁻ ξ : ℝ, 4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂volume) ≠ ⊤ := by
        rw [lintegral_const_mul' 4 _ (by norm_num)]
        exact ENNReal.mul_ne_top (by norm_num)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
            (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp g).2).ne
      have hpoint (ξ : ℝ) : Tendsto (fun n : ℕ =>
          ‖(resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ))
          atTop (𝓝 0) := by
        have hz : Tendsto (fun n : ℕ =>
            (resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ) atTop (𝓝 0) := by
          simpa using (resolventSymbol_tendsto_one ξ).sub_const 1 |>.mul_const
            ((g : ℝ → ℂ) ξ)
        convert (ENNReal.continuous_rpow_const
          (y := (2 : ℝ))).continuousAt.tendsto.comp hz.enorm using 1 <;>
          simp [Function.comp_def]
      simpa using tendsto_lintegral_of_dominated_convergence'
        (F := fun n ξ => ‖(resolventSymbol n ξ - 1) * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ))
        (f := fun _ => 0) (bound := fun ξ => 4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ))
          hmeas hbound hfin (Filter.Eventually.of_forall hpoint)
    convert (ENNReal.continuous_rpow_const
      (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hint using 1 <;>
      simp [Function.comp_def,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
  convert fourierL2.symm.continuous.continuousAt.tendsto.comp hfreq using 1
  · funext n
    change frequencySmoothCLM n f = fourierL2.symm
      (boundedMulCLM (resolventSymbol n) (continuous_resolventSymbol n)
        1 (by norm_num) (norm_resolventSymbol_le_one n) g)
    dsimp [g]
    rw [← fourier_frequencySmoothCLM, fourierL2.symm_apply_apply]
  · rw [show fourierL2.symm g = f by simp [g]]

lemma frequencySmooth_generator_memLp (n : ℕ) (f : L2) :
    MemLp (fun ξ : ℝ => schrodingerGenerator ξ *
      (fourierL2 (frequencySmoothCLM n f) : ℝ → ℂ) ξ) 2 volume := by
  have hcoe := coe_fourier_frequencySmoothCLM n f
  let C : ℝ := 4 * Real.pi ^ 2 * (n + 1)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ((Lp.memLp (fourierL2 f)).const_mul (C : ℂ)).mono
    (continuous_schrodingerGenerator.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (fourierL2 (frequencySmoothCLM n f)))) ?_
  filter_upwards [hcoe] with ξ hξ
  rw [hξ, norm_mul, norm_mul, norm_schrodingerGenerator]
  have hden : 0 < 1 + ξ ^ 2 / (n + 1 : ℝ) := by positivity
  have hm : ‖resolventSymbol n ξ‖ =
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ := by
    rw [resolventSymbol, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hden]
  rw [hm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  rw [← mul_assoc]
  gcongr
  change 4 * Real.pi ^ 2 * ξ ^ 2 *
    (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ ≤ C
  dsimp [C]
  rw [show 4 * Real.pi ^ 2 * ξ ^ 2 *
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ =
      4 * Real.pi ^ 2 *
        (ξ ^ 2 / (1 + ξ ^ 2 / (n + 1 : ℝ))) by ring]
  gcongr
  rw [div_le_iff₀ hden]
  calc
    ξ ^ 2 ≤ (n + 1 : ℝ) + ξ ^ 2 := by
      linarith [show 0 ≤ (n + 1 : ℝ) by positivity]
    _ = (n + 1 : ℝ) * (1 + ξ ^ 2 / (n + 1 : ℝ)) := by
      field_simp
      <;> ring

/-- The strong derivative of a free orbit whose Fourier transform is in the
domain of the Schrödinger generator. -/
def freePropDerivative (f : L2)
    (hgen : MemLp (fun ξ : ℝ => schrodingerGenerator ξ *
      (fourierL2 f : ℝ → ℂ) ξ) 2 volume) (t : ℝ) : L2 :=
  fourierL2.symm ((generator_symbol_mul_memLp (fourierL2 f) hgen t).toLp
    (fun ξ : ℝ => schrodingerGenerator ξ * schrodingerSymbol t ξ *
      (fourierL2 f : ℝ → ℂ) ξ))

lemma hasDerivAt_freeProp_of_generator (f : L2)
    (hgen : MemLp (fun ξ : ℝ => schrodingerGenerator ξ *
      (fourierL2 f : ℝ → ℂ) ξ) 2 volume) (t : ℝ) :
    HasDerivAt (fun s => freeProp s f) (freePropDerivative f hgen t) t := by
  let S : L2 →L[ℂ] L2 :=
    fourierL2.symm.toLinearIsometry.toContinuousLinearMap
  let SR : L2 →L[ℝ] L2 := S.restrictScalars ℝ
  have h : HasDerivAt
      (S ∘ fun s => multSymbol s (fourierL2 f))
      (S ((generator_symbol_mul_memLp (fourierL2 f) hgen t).toLp
        (fun ξ : ℝ => schrodingerGenerator ξ * schrodingerSymbol t ξ *
          (fourierL2 f : ℝ → ℂ) ξ))) t :=
    HasFDerivAt.comp_hasDerivAt (f := fun s => multSymbol s (fourierL2 f))
      (l := SR) t SR.hasFDerivAt
        (hasDerivAt_multSymbol (fourierL2 f) hgen t)
  simpa [S, SR, freeProp, freePropDerivative, Function.comp_def] using h

set_option maxHeartbeats 800000

/-- Product rule for a strongly continuous free group acting on a
differentiable curve.  Only the single vector at the base point is required
to lie in the generator domain; no operator-norm differentiability is used. -/
lemma hasDerivAt_freeProp_comp {y : ℝ → L2} {y' : L2} {t : ℝ}
    (hy : HasDerivAt y y' t)
    (hgen : MemLp (fun ξ : ℝ => schrodingerGenerator ξ *
      (fourierL2 (y t) : ℝ → ℂ) ξ) 2 volume) :
    HasDerivAt (fun s => freeProp s (y s))
      (freePropDerivative (y t) hgen t + freeProp t y') t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hySlope := hy.tendsto_slope_zero
  have htime : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ => t + h) 0 :=
      continuousAt_const.add continuousAt_id
    change Tendsto (fun h : ℝ => t + h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 t)
    have hle : nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) ≤ 𝓝 0 := inf_le_left
    simpa using hc.mono_left hle
  have hvar : Tendsto (fun h : ℝ =>
      freeProp (t + h) (h⁻¹ • (y (t + h) - y t))) (𝓝[≠] 0)
      (𝓝 (freeProp t y')) := by
    have hp : Tendsto (fun h : ℝ =>
        (t + h, h⁻¹ • (y (t + h) - y t))) (𝓝[≠] 0) (𝓝 (t, y')) :=
      htime.prodMk_nhds hySlope
    have hj := continuous_freeProp_joint.continuousAt.tendsto.comp hp
    simpa [Function.comp_def] using hj
  have hfix := (hasDerivAt_freeProp_of_generator (y t) hgen t).tendsto_slope_zero
  have hsum := hvar.add hfix
  convert hsum using 1
  · funext h
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) h⁻¹
        (freeProp (t + h) (y (t + h)) - freeProp t (y t)),
      RCLike.real_smul_eq_coe_smul (K := ℂ) h⁻¹ (y (t + h) - y t),
      RCLike.real_smul_eq_coe_smul (K := ℂ) h⁻¹
        (freeProp (t + h) (y t) - freeProp t (y t))]
    rw [freeProp_smul, freeProp_sub]
    module
  · simp only [add_comm]

end CubicNLSPhaseRetrieval
