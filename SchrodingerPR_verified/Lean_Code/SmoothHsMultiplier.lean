import Lean_Code.BoundedHsAlgebra
import Lean_Code.LocalSmoothingExtension

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

private lemma schwartz_toLp_eLpNorm_top_lt (φ : SchwartzMap ℝ ℂ) :
    eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume < ⊤ := by
  rw [eLpNorm_congr_ae (φ.coeFn_toLp 2 volume)]
  exact (φ.memLp ⊤ volume).2

def schwartzProductL2 (f : FourierL2) (φ : SchwartzMap ℝ ℂ) : FourierL2 :=
  boundedProductL2 f (φ.toLp 2 volume) (schwartz_toLp_eLpNorm_top_lt φ)

lemma coe_schwartzProductL2 (f : FourierL2) (φ : SchwartzMap ℝ ℂ) :
    (schwartzProductL2 f φ : ℝ → ℂ) =ᵐ[volume]
      fun x => (f : ℝ → ℂ) x * φ x := by
  filter_upwards [coe_boundedProductL2 f (φ.toLp 2 volume)
      (schwartz_toLp_eLpNorm_top_lt φ), φ.coeFn_toLp 2 volume] with x hp hφ
  rw [schwartzProductL2, hp, hφ]

private lemma schwartz_deriv_norm_le (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖deriv (φ : ℝ → ℂ) x‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ := by
  simpa using (SchwartzMap.le_seminorm' ℂ 0 1 φ x)

lemma schwartz_difference_norm_le_deriv (φ : SchwartzMap ℝ ℂ) (x h : ℝ) :
    ‖φ (x + h) - φ x‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ * |h| := by
  have hdiff : ∀ y ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (φ : ℝ → ℂ) y := fun y _ => φ.differentiableAt
  simpa [Real.norm_eq_abs] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff
      (fun y _ => schwartz_deriv_norm_le φ y) (Set.mem_univ x)
      (Set.mem_univ (x + h)) :
        ‖φ (x + h) - φ x‖ ≤
          SchwartzMap.seminorm ℂ 0 1 φ * ‖(x + h) - x‖)

lemma schwartz_difference_norm_le_sup (φ : SchwartzMap ℝ ℂ) (x h : ℝ) :
    ‖φ (x + h) - φ x‖ ≤ 2 * SchwartzMap.seminorm ℂ 0 0 φ := by
  calc
    ‖φ (x + h) - φ x‖ ≤ ‖φ (x + h)‖ + ‖φ x‖ := norm_sub_le _ _
    _ ≤ SchwartzMap.seminorm ℂ 0 0 φ +
        SchwartzMap.seminorm ℂ 0 0 φ := by
      gcongr
      · simpa using (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 0 (x + h))
      · simpa using (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 0 x)
    _ = 2 * SchwartzMap.seminorm ℂ 0 0 φ := by ring

private lemma coe_translate_schwartz (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    (translateL2 h (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun x => φ (x + h) := by
  have hφ := (MeasureTheory.measurePreserving_add_right
    (volume : Measure ℝ) h).quasiMeasurePreserving.ae (φ.coeFn_toLp 2 volume)
  filter_upwards [coe_translateL2 h (φ.toLp 2 volume), hφ] with x ht hp
  rw [ht, hp]

private lemma eLpNorm_schwartzDifference_top_le_deriv
    (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    eLpNorm ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
      ℝ → ℂ) ⊤ volume ≤
      ENNReal.ofReal (SchwartzMap.seminorm ℂ 0 1 φ * |h|) := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [coe_translate_schwartz φ h, φ.coeFn_toLp 2 volume,
    Lp.coeFn_sub (translateL2 h (φ.toLp 2 volume)) (φ.toLp 2 volume)]
      with x ht hp hs
  rw [hs, Pi.sub_apply, ht, hp]
  exact schwartz_difference_norm_le_deriv φ x h

private lemma eLpNorm_schwartzDifference_top_le_sup
    (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    eLpNorm ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
      ℝ → ℂ) ⊤ volume ≤
      ENNReal.ofReal (2 * SchwartzMap.seminorm ℂ 0 0 φ) := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [coe_translate_schwartz φ h, φ.coeFn_toLp 2 volume,
    Lp.coeFn_sub (translateL2 h (φ.toLp 2 volume)) (φ.toLp 2 volume)]
      with x ht hp hs
  rw [hs, Pi.sub_apply, ht, hp]
  exact schwartz_difference_norm_le_sup φ x h

private lemma eLpNorm_schwartzDifference_top_lt
    (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    eLpNorm ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
      ℝ → ℂ) ⊤ volume < ⊤ :=
  (eLpNorm_schwartzDifference_top_le_sup φ h).trans_lt ENNReal.ofReal_lt_top

private lemma schwartzProduct_translate_sub_identity
    (f : FourierL2) (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    translateL2 h (schwartzProductL2 f φ) - schwartzProductL2 f φ =
      boundedProductL2 (translateL2 h f - f)
        (translateL2 h (φ.toLp 2 volume)) (by
          rw [eLpNorm_translate_top]
          exact schwartz_toLp_eLpNorm_top_lt φ) +
      boundedProductL2 f
        (translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume)
        (eLpNorm_schwartzDifference_top_lt φ h) := by
  apply Lp.ext
  have hφshift := (MeasureTheory.measurePreserving_add_right
    (volume : Measure ℝ) h).quasiMeasurePreserving.ae (φ.coeFn_toLp 2 volume)
  filter_upwards [coe_translateL2 h (schwartzProductL2 f φ),
    (MeasureTheory.measurePreserving_add_right
      (volume : Measure ℝ) h).quasiMeasurePreserving.ae
        (coe_schwartzProductL2 f φ),
    coe_schwartzProductL2 f φ,
    coe_translateL2 h f, coe_translateL2 h (φ.toLp 2 volume),
    hφshift, φ.coeFn_toLp 2 volume,
    Lp.coeFn_sub (translateL2 h f) f,
    Lp.coeFn_sub (translateL2 h (φ.toLp 2 volume)) (φ.toLp 2 volume),
    Lp.coeFn_sub (translateL2 h (schwartzProductL2 f φ))
      (schwartzProductL2 f φ),
    coe_boundedProductL2 (translateL2 h f - f)
      (translateL2 h (φ.toLp 2 volume)) (by
        rw [eLpNorm_translate_top]
        exact schwartz_toLp_eLpNorm_top_lt φ),
    coe_boundedProductL2 f
      (translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume)
      (eLpNorm_schwartzDifference_top_lt φ h),
    Lp.coeFn_add
      (boundedProductL2 (translateL2 h f - f)
        (translateL2 h (φ.toLp 2 volume)) (by
          rw [eLpNorm_translate_top]
          exact schwartz_toLp_eLpNorm_top_lt φ))
      (boundedProductL2 f
        (translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume)
        (eLpNorm_schwartzDifference_top_lt φ h))]
      with x hprodShift hprodAtShift hprod htf htφ hφatShift hφ
        hdf hdφ hout hl hr hadd
  rw [hout, hadd]
  change
    (translateL2 h (schwartzProductL2 f φ) : ℝ → ℂ) x -
        (schwartzProductL2 f φ : ℝ → ℂ) x =
      (boundedProductL2 (translateL2 h f - f)
          (translateL2 h (φ.toLp 2 volume)) _ : ℝ → ℂ) x +
        (boundedProductL2 f
          (translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume) _ : ℝ → ℂ) x
  rw [hl, hr, hdf, hdφ]
  simp only [Pi.sub_apply]
  rw [hprodShift, hprodAtShift, hprod, htf, htφ, hφatShift, hφ]
  ring

lemma enorm_translate_schwartzProduct_sub_le
    (f : FourierL2) (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    ‖translateL2 h (schwartzProductL2 f φ) - schwartzProductL2 f φ‖ₑ ≤
      ‖translateL2 h f - f‖ₑ *
        eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume +
      ‖f‖ₑ * eLpNorm
        ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
          ℝ → ℂ) ⊤ volume := by
  rw [schwartzProduct_translate_sub_identity f φ h]
  calc
    _ ≤ ‖boundedProductL2 (translateL2 h f - f)
          (translateL2 h (φ.toLp 2 volume)) (by
            rw [eLpNorm_translate_top]
            exact schwartz_toLp_eLpNorm_top_lt φ)‖ₑ +
        ‖boundedProductL2 f
          (translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume)
          (eLpNorm_schwartzDifference_top_lt φ h)‖ₑ := enorm_add_le _ _
    _ ≤ ‖translateL2 h f - f‖ₑ *
          eLpNorm (translateL2 h (φ.toLp 2 volume) : ℝ → ℂ) ⊤ volume +
        ‖f‖ₑ * eLpNorm
          ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
            ℝ → ℂ) ⊤ volume :=
      add_le_add (norm_boundedProductL2_le _ _ _)
        (norm_boundedProductL2_le _ _ _)
    _ = _ := by rw [eLpNorm_translate_top]

private lemma sq_div_le_two_mul_smooth (n a b A B d : ℝ≥0∞)
    (hn : n ≤ a * A + b * B) :
    n ^ (2 : ℕ) / d ≤
      2 * A ^ (2 : ℕ) * (a ^ (2 : ℕ) / d) +
        2 * B ^ (2 : ℕ) * (b ^ (2 : ℕ) / d) := by
  calc
    n ^ (2 : ℕ) / d ≤ (a * A + b * B) ^ (2 : ℕ) / d := by gcongr
    _ = (a * A + b * B) ^ (2 : ℝ) / d := by norm_num
    _ ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ((a * A) ^ (2 : ℝ) + (b * B) ^ (2 : ℝ)) / d := by
      gcongr
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
    _ = 2 * A ^ (2 : ℕ) * (a ^ (2 : ℕ) / d) +
        2 * B ^ (2 : ℕ) * (b ^ (2 : ℕ) / d) := by
      norm_num [ENNReal.mul_rpow_of_nonneg]
      simp only [div_eq_mul_inv]
      ring

private def schwartzDifferenceKernel (φ : SchwartzMap ℝ ℂ) (h : ℝ) : ℝ≥0∞ :=
  eLpNorm
      ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
        ℝ → ℂ) ⊤ volume ^ (2 : ℕ) /
    ENNReal.ofReal (|h| ^ (2 : ℕ))

private def schwartzDifferenceMajorant (φ : SchwartzMap ℝ ℂ) (h : ℝ) : ℝ :=
  (2 * (SchwartzMap.seminorm ℂ 0 1 φ) ^ 2 +
      8 * (SchwartzMap.seminorm ℂ 0 0 φ) ^ 2) * (1 + h ^ 2)⁻¹

private def smoothMultiplierKernelIntegral : ℝ≥0∞ :=
  ∫⁻ h : ℝ, ENNReal.ofReal ((1 + h ^ 2)⁻¹)

private lemma smoothMultiplierKernelIntegral_lt_top :
    smoothMultiplierKernelIntegral < ⊤ := by
  rw [smoothMultiplierKernelIntegral,
    ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq]
  · exact ENNReal.ofReal_lt_top
  · filter_upwards with h
    positivity

private lemma eLpNorm_schwartz_top_le_seminorm (φ : SchwartzMap ℝ ℂ) :
    eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ≤
      ENNReal.ofReal (SchwartzMap.seminorm ℂ 0 0 φ) := by
  rw [eLpNorm_congr_ae (φ.coeFn_toLp 2 volume), eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with x
  simpa using (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 0 x)

private lemma lintegral_schwartzDifferenceMajorant (φ : SchwartzMap ℝ ℂ) :
    (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) =
      ENNReal.ofReal
          (2 * (SchwartzMap.seminorm ℂ 0 1 φ) ^ 2 +
            8 * (SchwartzMap.seminorm ℂ 0 0 φ) ^ 2) *
        smoothMultiplierKernelIntegral := by
  let A : ℝ := 2 * (SchwartzMap.seminorm ℂ 0 1 φ) ^ 2 +
    8 * (SchwartzMap.seminorm ℂ 0 0 φ) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) =
        ∫⁻ h : ℝ, ENNReal.ofReal A * ENNReal.ofReal ((1 + h ^ 2)⁻¹) := by
      apply lintegral_congr
      intro h
      rw [← ENNReal.ofReal_mul hA]
      rfl
    _ = ENNReal.ofReal A * smoothMultiplierKernelIntegral := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ = _ := by rfl

private lemma schwartzDifferenceMajorant_nonneg (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    0 ≤ schwartzDifferenceMajorant φ h := by
  unfold schwartzDifferenceMajorant
  positivity

private lemma schwartzDifferenceKernel_le_majorant
    (φ : SchwartzMap ℝ ℂ) (h : ℝ) :
    schwartzDifferenceKernel φ h ≤
      ENNReal.ofReal (schwartzDifferenceMajorant φ h) := by
  by_cases hh : h = 0
  · subst h
    have hz : translateL2 0 (φ.toLp 2 volume) - φ.toLp 2 volume =
        (0 : FourierL2) := by simp [translateL2]
    rw [schwartzDifferenceKernel, hz,
      eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)), eLpNorm_zero]
    simp
  have hdenpos : 0 < |h| ^ (2 : ℕ) := sq_pos_of_ne_zero (abs_ne_zero.mpr hh)
  have hden0 : ENNReal.ofReal (|h| ^ (2 : ℕ)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hdenpos)
  have hdentop : ENNReal.ofReal (|h| ^ (2 : ℕ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [schwartzDifferenceKernel, ENNReal.div_le_iff' hden0 hdentop]
  by_cases hsmall : |h| ≤ 1
  · have hB := eLpNorm_schwartzDifference_top_le_deriv φ h
    calc
      eLpNorm
          ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
            ℝ → ℂ) ⊤ volume ^ (2 : ℕ) ≤
          (ENNReal.ofReal
            (SchwartzMap.seminorm ℂ 0 1 φ * |h|)) ^ (2 : ℕ) := by gcongr
      _ = ENNReal.ofReal
          ((SchwartzMap.seminorm ℂ 0 1 φ * |h|) ^ (2 : ℕ)) := by
        rw [ENNReal.ofReal_pow (mul_nonneg
          (apply_nonneg (SchwartzMap.seminorm ℂ 0 1) φ) (abs_nonneg h))]
      _ ≤ ENNReal.ofReal (|h| ^ (2 : ℕ)) *
          ENNReal.ofReal (schwartzDifferenceMajorant φ h) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ |h| ^ (2 : ℕ))]
        apply ENNReal.ofReal_le_ofReal
        unfold schwartzDifferenceMajorant
        have habs2 : |h| ^ 2 ≤ 1 := by
          simpa using (sq_le_sq₀ (abs_nonneg h) zero_le_one).2 hsmall
        have hone : 1 + h ^ 2 ≤ 2 := by
          rw [← sq_abs]
          linarith
        have hpos : 0 < 1 + h ^ 2 := by positivity
        rw [inv_eq_one_div]
        rw [show (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 +
              8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) *
              (1 / (1 + h ^ 2)) =
            (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 +
              8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) /
              (1 + h ^ 2) by ring]
        rw [mul_div_assoc']
        rw [le_div_iff₀ hpos]
        rw [sq_abs]
        calc
          ((SchwartzMap.seminorm ℂ 0 1) φ * |h|) ^ 2 * (1 + h ^ 2) =
              (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 * h ^ 2 *
                (1 + h ^ 2) := by rw [mul_pow, sq_abs]
          _ ≤ (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 * h ^ 2 * 2 := by
            gcongr
          _ ≤ h ^ 2 *
              (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 +
                8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) := by
            have hm : 0 ≤ h ^ 2 *
                (8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) := by positivity
            nlinarith
  · have hlarge : 1 ≤ |h| := le_of_not_ge hsmall
    have hB := eLpNorm_schwartzDifference_top_le_sup φ h
    calc
      eLpNorm
          ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
            ℝ → ℂ) ⊤ volume ^ (2 : ℕ) ≤
          (ENNReal.ofReal
            (2 * SchwartzMap.seminorm ℂ 0 0 φ)) ^ (2 : ℕ) := by gcongr
      _ = ENNReal.ofReal
          ((2 * SchwartzMap.seminorm ℂ 0 0 φ) ^ (2 : ℕ)) := by
        rw [ENNReal.ofReal_pow (mul_nonneg (by norm_num)
          (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) φ))]
      _ ≤ ENNReal.ofReal (|h| ^ (2 : ℕ)) *
          ENNReal.ofReal (schwartzDifferenceMajorant φ h) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ |h| ^ (2 : ℕ))]
        apply ENNReal.ofReal_le_ofReal
        unfold schwartzDifferenceMajorant
        have hsquare : 1 ≤ h ^ 2 := by
          rw [← sq_abs]
          nlinarith [abs_nonneg h]
        have hpos : 0 < 1 + h ^ 2 := by positivity
        rw [inv_eq_one_div]
        rw [show (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 +
              8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) *
              (1 / (1 + h ^ 2)) =
            (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 +
              8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) /
              (1 + h ^ 2) by ring]
        rw [mul_div_assoc']
        rw [le_div_iff₀ hpos]
        rw [sq_abs]
        have htwo : 1 + h ^ 2 ≤ 2 * h ^ 2 := by linarith
        calc
          (2 * (SchwartzMap.seminorm ℂ 0 0) φ) ^ 2 * (1 + h ^ 2) =
              4 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2 *
                (1 + h ^ 2) := by ring
          _ ≤ 4 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2 *
              (2 * h ^ 2) := by gcongr
          _ ≤ h ^ 2 *
              (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2 +
                8 * (SchwartzMap.seminorm ℂ 0 0) φ ^ 2) := by
            have hd : 0 ≤ h ^ 2 *
                (2 * (SchwartzMap.seminorm ℂ 0 1) φ ^ 2) := by positivity
            nlinarith

private lemma schwartzDifferenceKernel_integral_lt_top
    (φ : SchwartzMap ℝ ℂ) :
    (∫⁻ h : ℝ, schwartzDifferenceKernel φ h ∂volume) < ⊤ := by
  have hmajInt : Integrable (schwartzDifferenceMajorant φ) volume := by
    unfold schwartzDifferenceMajorant
    exact integrable_inv_one_add_sq.const_mul
      (2 * (SchwartzMap.seminorm ℂ 0 1 φ) ^ 2 +
        8 * (SchwartzMap.seminorm ℂ 0 0 φ) ^ 2)
  have hmajFin :
      (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h) ∂volume) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmajInt]
    · exact ENNReal.ofReal_lt_top
    · filter_upwards with h
      exact schwartzDifferenceMajorant_nonneg φ h
  exact lt_of_le_of_lt
    (lintegral_mono (schwartzDifferenceKernel_le_majorant φ)) hmajFin

set_option maxHeartbeats 1000000 in
theorem translationEnergy_schwartzProductL2_le
    (f : Hs (1 / 2 : ℝ)) (φ : SchwartzMap ℝ ℂ) :
    translationEnergy
      (schwartzProductL2 (Hs.toL2 (by norm_num) f) φ) ≤
        (2 * eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ^ (2 : ℕ)) *
          translationEnergy (Hs.toL2 (by norm_num) f) +
        (2 * ‖Hs.toL2 (by norm_num) f‖ₑ ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) := by
  let F : FourierL2 := Hs.toL2 (by norm_num) f
  let A : ℝ≥0∞ := eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume
  let B : ℝ≥0∞ := ‖F‖ₑ
  have hpoint (h : ℝ) :
      ‖translateL2 h (schwartzProductL2 F φ) -
          schwartzProductL2 F φ‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)) ≤
        2 * A ^ (2 : ℕ) *
          (‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) +
        2 * B ^ (2 : ℕ) *
          ENNReal.ofReal (schwartzDifferenceMajorant φ h) := by
    let K : ℝ≥0∞ := eLpNorm
      ((translateL2 h (φ.toLp 2 volume) - φ.toLp 2 volume : FourierL2) :
        ℝ → ℂ) ⊤ volume
    calc
      ‖translateL2 h (schwartzProductL2 F φ) -
          schwartzProductL2 F φ‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)) ≤
        2 * A ^ (2 : ℕ) *
            (‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) +
          2 * K ^ (2 : ℕ) *
            (B ^ (2 : ℕ) / ENNReal.ofReal (|h| ^ (2 : ℕ))) := by
        apply sq_div_le_two_mul_smooth
        simpa [A, B, K, F] using
          (enorm_translate_schwartzProduct_sub_le F φ h)
      _ = 2 * A ^ (2 : ℕ) *
            (‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) +
          2 * B ^ (2 : ℕ) * schwartzDifferenceKernel φ h := by
        unfold schwartzDifferenceKernel
        dsimp only [K]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ 2 * A ^ (2 : ℕ) *
            (‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) +
          2 * B ^ (2 : ℕ) *
            ENNReal.ofReal (schwartzDifferenceMajorant φ h) := by
        gcongr
        exact schwartzDifferenceKernel_le_majorant φ h
  unfold translationEnergy
  have hmeasF : AEMeasurable (fun h : ℝ =>
      ‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ))) volume :=
    (((continuous_translateL2 F).sub continuous_const).aestronglyMeasurable.enorm.pow_const 2).div
      (by fun_prop)
  have hmeasFirst : AEMeasurable (fun h : ℝ =>
      2 * A ^ (2 : ℕ) *
        (‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)))) volume :=
    measurable_const.aemeasurable.mul hmeasF
  calc
    (∫⁻ h : ℝ, ‖translateL2 h (schwartzProductL2 F φ) -
        schwartzProductL2 F φ‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ))) ≤
      ∫⁻ h : ℝ,
        2 * A ^ (2 : ℕ) *
            (‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) +
          2 * B ^ (2 : ℕ) *
            ENNReal.ofReal (schwartzDifferenceMajorant φ h) :=
      lintegral_mono hpoint
    _ = (2 * A ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ‖translateL2 h F - F‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) +
        (2 * B ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ENNReal.ofReal
            (schwartzDifferenceMajorant φ h)) := by
      rw [lintegral_add_left' hmeasFirst]
      rw [lintegral_const_mul'' _ hmeasF]
      rw [lintegral_const_mul']
      exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top enorm_ne_top)
    _ = _ := by rfl

theorem translationEnergy_schwartzProductL2_lt_top
    (f : Hs (1 / 2 : ℝ)) (φ : SchwartzMap ℝ ℂ) :
    translationEnergy
      (schwartzProductL2 (Hs.toL2 (by norm_num) f) φ) < ⊤ := by
  apply (translationEnergy_schwartzProductL2_le f φ).trans_lt
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.pow_lt_top (schwartz_toLp_eLpNorm_top_lt φ)))
      (translationEnergy_Hs_toL2_lt_top f)
  · apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top (by norm_num)
        (ENNReal.pow_lt_top enorm_lt_top)
    · have hmajInt : Integrable (schwartzDifferenceMajorant φ) volume := by
        unfold schwartzDifferenceMajorant
        exact integrable_inv_one_add_sq.const_mul
          (2 * (SchwartzMap.seminorm ℂ 0 1 φ) ^ 2 +
            8 * (SchwartzMap.seminorm ℂ 0 0 φ) ^ 2)
      rw [← ofReal_integral_eq_lintegral_ofReal hmajInt]
      · exact ENNReal.ofReal_lt_top
      · filter_upwards with h
        exact schwartzDifferenceMajorant_nonneg φ h

/-- Multiplication by a fixed Schwartz function preserves critical
`H^{1/2}` regularity, with no boundedness hypothesis on the Sobolev factor. -/
theorem schwartz_Hs_product_exists (f : Hs (1 / 2 : ℝ))
    (φ : SchwartzMap ℝ ℂ) :
    ∃ p : Hs (1 / 2 : ℝ),
      Hs.toL2 (by norm_num) p =
        schwartzProductL2 (Hs.toL2 (by norm_num) f) φ ∧
      (Hs.toL2 (by norm_num) p : ℝ → ℂ) =ᵐ[volume]
        fun x => (Hs.toL2 (by norm_num) f : ℝ → ℂ) x * φ x := by
  let w := schwartzProductL2 (Hs.toL2 (by norm_num) f) φ
  have hwEnergy : translationEnergy w < ⊤ :=
    translationEnergy_schwartzProductL2_lt_top f φ
  have hwHom : homogeneousFourierEnergy (1 / 2 : ℝ) w < ⊤ := by
    by_contra hn
    have htop : homogeneousFourierEnergy (1 / 2 : ℝ) w = ⊤ :=
      top_unique (le_of_not_gt hn)
    rw [translationEnergy_eq_fourier, htop,
      ENNReal.mul_top halfKernelConstant_pos.ne'] at hwEnergy
    exact (ne_of_lt hwEnergy) rfl
  obtain ⟨p, hp⟩ := exists_Hs_half_of_homogeneousFourierEnergy_lt_top w hwHom
  refine ⟨p, hp, ?_⟩
  rw [hp]
  exact coe_schwartzProductL2 _ φ

lemma schwartzProductL2_eq_cutoffL2CLM (f : FourierL2)
    (φ : SchwartzMap ℝ ℂ) :
    schwartzProductL2 f φ = cutoffL2CLM φ f := by
  apply Lp.ext
  filter_upwards [coe_schwartzProductL2 f φ,
    coe_cutoffL2CLM φ f] with x hl hr
  rw [hl, hr]
  exact mul_comm _ _

private lemma schwartzProductL2_add (f g : FourierL2)
    (φ : SchwartzMap ℝ ℂ) :
    schwartzProductL2 (f + g) φ =
      schwartzProductL2 f φ + schwartzProductL2 g φ := by
  simp only [schwartzProductL2_eq_cutoffL2CLM]
  exact map_add (cutoffL2CLM φ) f g

private lemma schwartzProductL2_smul (c : ℂ) (f : FourierL2)
    (φ : SchwartzMap ℝ ℂ) :
    schwartzProductL2 (c • f) φ = c • schwartzProductL2 f φ := by
  simp only [schwartzProductL2_eq_cutoffL2CLM]
  exact map_smul (cutoffL2CLM φ) c f

/-- The canonical `H^{1/2}` representative of multiplication by a Schwartz
function. -/
def schwartzHsProduct (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) : Hs (1 / 2 : ℝ) :=
  Classical.choose (schwartz_Hs_product_exists f φ)

lemma schwartzHsProduct_toL2 (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) :
    Hs.toL2 (by norm_num) (schwartzHsProduct φ f) =
      schwartzProductL2 (Hs.toL2 (by norm_num) f) φ :=
  (Classical.choose_spec (schwartz_Hs_product_exists f φ)).1

lemma schwartzHsProduct_toL2_ae (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) :
    (Hs.toL2 (by norm_num) (schwartzHsProduct φ f) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Hs.toL2 (by norm_num) f : ℝ → ℂ) x * φ x :=
  (Classical.choose_spec (schwartz_Hs_product_exists f φ)).2

private def schwartzHsProductLinear (φ : SchwartzMap ℝ ℂ) :
    Hs (1 / 2 : ℝ) →ₗ[ℂ] Hs (1 / 2 : ℝ) where
  toFun := schwartzHsProduct φ
  map_add' f g := by
    apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
    have hadd : Hs.toL2 (by norm_num) (f + g) =
        Hs.toL2 (by norm_num) f + Hs.toL2 (by norm_num) g := by
      rw [← hsHalfToL2CLM_apply, map_add, hsHalfToL2CLM_apply,
        hsHalfToL2CLM_apply]
    have hout : Hs.toL2 (by norm_num)
          (schwartzHsProduct φ f + schwartzHsProduct φ g) =
        Hs.toL2 (by norm_num) (schwartzHsProduct φ f) +
          Hs.toL2 (by norm_num) (schwartzHsProduct φ g) := by
      rw [← hsHalfToL2CLM_apply, map_add, hsHalfToL2CLM_apply,
        hsHalfToL2CLM_apply]
    rw [schwartzHsProduct_toL2, hadd, schwartzProductL2_add, hout,
      schwartzHsProduct_toL2, schwartzHsProduct_toL2]
  map_smul' c f := by
    apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
    have hsmul : Hs.toL2 (by norm_num) (c • f) =
        c • Hs.toL2 (by norm_num) f := by
      rw [← hsHalfToL2CLM_apply, map_smul, hsHalfToL2CLM_apply]
    have hout : Hs.toL2 (by norm_num) (c • schwartzHsProduct φ f) =
        c • Hs.toL2 (by norm_num) (schwartzHsProduct φ f) := by
      rw [← hsHalfToL2CLM_apply, map_smul, hsHalfToL2CLM_apply]
    rw [schwartzHsProduct_toL2, hsmul, schwartzProductL2_smul]
    change c • schwartzProductL2 (Hs.toL2 (by norm_num) f) φ =
      Hs.toL2 (by norm_num) (c • schwartzHsProduct φ f)
    rw [hout, schwartzHsProduct_toL2]

private theorem schwartzHsProduct_seq_closed_graph (φ : SchwartzMap ℝ ℂ) :
    ∀ (u : ℕ → Hs (1 / 2 : ℝ)) (x y : Hs (1 / 2 : ℝ)),
      Tendsto u atTop (𝓝 x) →
      Tendsto (schwartzHsProductLinear φ ∘ u) atTop (𝓝 y) →
      y = schwartzHsProductLinear φ x := by
  intro u x y hu huy
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  have hy : Tendsto
      (fun n => Hs.toL2 (by norm_num)
        (schwartzHsProductLinear φ (u n))) atTop
      (𝓝 (Hs.toL2 (by norm_num) y)) := by
    simpa [Function.comp_def, hsHalfToL2CLM_apply] using
      (hsHalfToL2CLM.continuous.tendsto y).comp huy
  have hxL2 : Tendsto (fun n => Hs.toL2 (by norm_num) (u n)) atTop
      (𝓝 (Hs.toL2 (by norm_num) x)) := by
    have hx := (hsHalfToL2CLM.continuous.tendsto x).comp hu
    convert hx using 1 <;> simp [Function.comp_def, hsHalfToL2CLM_apply]
  have hprod : Tendsto
      (fun n => Hs.toL2 (by norm_num)
        (schwartzHsProductLinear φ (u n))) atTop
      (𝓝 (Hs.toL2 (by norm_num) (schwartzHsProductLinear φ x))) := by
    have hc := (cutoffL2CLM φ).continuous.tendsto
      (Hs.toL2 (by norm_num) x) |>.comp hxL2
    convert hc using 1 <;>
      simp [Function.comp_def, schwartzHsProductLinear,
        schwartzHsProduct_toL2, schwartzProductL2_eq_cutoffL2CLM]
  exact tendsto_nhds_unique hy hprod

/-- Multiplication by a fixed Schwartz function as a continuous operator on
critical Sobolev space. -/
def schwartzHsMultiplier (φ : SchwartzMap ℝ ℂ) :
    Hs (1 / 2 : ℝ) →L[ℂ] Hs (1 / 2 : ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph
    (schwartzHsProduct_seq_closed_graph φ)

@[simp] lemma schwartzHsMultiplier_apply (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) :
    schwartzHsMultiplier φ f = schwartzHsProduct φ f := rfl

lemma schwartzHsMultiplier_toL2_ae (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) :
    (Hs.toL2 (by norm_num) (schwartzHsMultiplier φ f) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Hs.toL2 (by norm_num) f : ℝ → ℂ) x * φ x :=
  schwartzHsProduct_toL2_ae φ f

/-- A universal finite squared constant for multiplication on `H^{1/2}`.
The deliberately generous numerical coefficient keeps the estimate stable
under simultaneous control of a function and its first derivative. -/
def smoothHsMultiplierConstantSq : ℝ≥0∞ :=
  1 + halfKernelConstant⁻¹ *
    (2 * halfKernelConstant + 20 * smoothMultiplierKernelIntegral)

lemma smoothHsMultiplierConstantSq_lt_top :
    smoothHsMultiplierConstantSq < ⊤ := by
  unfold smoothHsMultiplierConstantSq
  apply ENNReal.add_lt_top.mpr
  refine ⟨by norm_num, ENNReal.mul_lt_top ?_ ?_⟩
  · exact ENNReal.inv_lt_top.mpr halfKernelConstant_pos
  · exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.mul_lt_top (by norm_num) halfKernelConstant_lt_top,
      ENNReal.mul_lt_top (by norm_num) smoothMultiplierKernelIntegral_lt_top⟩

/-- Quantitative critical smooth-multiplier estimate.  Only the zeroth and
first Schwartz seminorms enter, uniformly in the multiplier. -/
theorem schwartzHsMultiplier_enorm_sq_le (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) :
    ‖schwartzHsMultiplier φ f‖ₑ ^ (2 : ℕ) ≤
      smoothHsMultiplierConstantSq *
        ENNReal.ofReal
            (SchwartzMap.seminorm ℂ 0 0 φ +
              SchwartzMap.seminorm ℂ 0 1 φ) ^ (2 : ℕ) *
          ‖f‖ₑ ^ (2 : ℕ) := by
  let a : ℝ := SchwartzMap.seminorm ℂ 0 0 φ
  let d : ℝ := SchwartzMap.seminorm ℂ 0 1 φ
  let S : ℝ≥0∞ := ENNReal.ofReal (a + d)
  let E : ℝ≥0∞ := ‖f‖ₑ ^ (2 : ℕ)
  let F : FourierL2 := Hs.toL2 (by norm_num) f
  let P : Hs (1 / 2 : ℝ) := schwartzHsMultiplier φ f
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hS : ENNReal.ofReal a ≤ S := by
    dsimp [S]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hD : ENNReal.ofReal d ≤ S := by
    dsimp [S]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hF : ‖F‖ₑ ≤ ‖f‖ₑ := by
    simpa only [F, ofReal_norm] using
      ENNReal.ofReal_le_ofReal (norm_Hs_toL2_le f)
  have hhomF : homogeneousFourierEnergy (1 / 2 : ℝ) F ≤ E := by
    simpa [F, E] using homogeneousFourierEnergy_Hs_toL2_le_enorm_sq f
  have hmassP : ‖Hs.toL2 (by norm_num) P‖ₑ ^ (2 : ℕ) ≤ S ^ (2 : ℕ) * E := by
    have hprod : Hs.toL2 (by norm_num) P = schwartzProductL2 F φ := by
      simp [P, F, schwartzHsMultiplier_apply, schwartzHsProduct_toL2]
    rw [hprod]
    calc
      ‖schwartzProductL2 F φ‖ₑ ^ (2 : ℕ) ≤
          (‖F‖ₑ * eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume) ^
            (2 : ℕ) := by
        gcongr
        exact norm_boundedProductL2_le _ _ _
      _ ≤ (‖f‖ₑ *
          eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume) ^ (2 : ℕ) := by
        gcongr
      _ ≤ (‖f‖ₑ * S) ^ (2 : ℕ) := by
        gcongr
        exact (eLpNorm_schwartz_top_le_seminorm φ).trans hS
      _ = S ^ (2 : ℕ) * E := by dsimp [E]; ring
  have hcoeff : ENNReal.ofReal (2 * d ^ 2 + 8 * a ^ 2) ≤
      10 * S ^ (2 : ℕ) := by
    rw [show ENNReal.ofReal (2 * d ^ 2 + 8 * a ^ 2) =
        2 * ENNReal.ofReal d ^ (2 : ℕ) +
          8 * ENNReal.ofReal a ^ (2 : ℕ) by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
        ENNReal.ofReal_pow hd 2, ENNReal.ofReal_pow ha 2]
      norm_num]
    calc
      2 * ENNReal.ofReal d ^ (2 : ℕ) +
          8 * ENNReal.ofReal a ^ (2 : ℕ) ≤
          2 * S ^ (2 : ℕ) + 8 * S ^ (2 : ℕ) := by gcongr
      _ = 10 * S ^ (2 : ℕ) := by ring
  have henergyP : homogeneousFourierEnergy (1 / 2 : ℝ)
      (Hs.toL2 (by norm_num) P) ≤
        halfKernelConstant⁻¹ *
          (2 * S ^ (2 : ℕ) * (halfKernelConstant * E) +
            20 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral * E) := by
    have hprod : Hs.toL2 (by norm_num) P = schwartzProductL2 F φ := by
      simp [P, F, schwartzHsMultiplier_apply, schwartzHsProduct_toL2]
    have htranslate := translationEnergy_schwartzProductL2_le f φ
    have hA : eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ≤ S :=
      (eLpNorm_schwartz_top_le_seminorm φ).trans hS
    have hTEF : translationEnergy F ≤ halfKernelConstant * E := by
      rw [translationEnergy_eq_fourier]
      exact mul_le_mul_left' hhomF _
    have hJ : (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) ≤
        10 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral := by
      rw [lintegral_schwartzDifferenceMajorant]
      exact mul_le_mul_right' hcoeff _
    have hfirst :
        (2 * eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ^ (2 : ℕ)) *
            translationEnergy F ≤
          2 * S ^ (2 : ℕ) * (halfKernelConstant * E) := by
      calc
        (2 * eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ^ (2 : ℕ)) *
              translationEnergy F ≤
            (2 * S ^ (2 : ℕ)) * translationEnergy F := by gcongr
        _ ≤ (2 * S ^ (2 : ℕ)) * (halfKernelConstant * E) := by gcongr
    have hFpow : ‖F‖ₑ ^ (2 : ℕ) ≤ E := by
      dsimp [E]
      gcongr
    have hsecond :
        (2 * ‖F‖ₑ ^ (2 : ℕ)) *
            (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) ≤
          20 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral * E := by
      calc
        (2 * ‖F‖ₑ ^ (2 : ℕ)) *
              (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) ≤
            (2 * E) *
              (10 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral) := by
          gcongr
        _ = 20 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral * E := by ring
    rw [hprod]
    have htranslated :
        halfKernelConstant * homogeneousFourierEnergy (1 / 2 : ℝ)
            (schwartzProductL2 F φ) ≤
          (2 * eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ^ (2 : ℕ)) *
              translationEnergy F +
            (2 * ‖F‖ₑ ^ (2 : ℕ)) *
              (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h)) := by
      rw [← translationEnergy_eq_fourier]
      simpa [F] using htranslate
    calc
      homogeneousFourierEnergy (1 / 2 : ℝ) (schwartzProductL2 F φ) =
          halfKernelConstant⁻¹ *
            (halfKernelConstant * homogeneousFourierEnergy
              (1 / 2 : ℝ) (schwartzProductL2 F φ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel halfKernelConstant_pos.ne'
          halfKernelConstant_lt_top.ne, one_mul]
      _ ≤ halfKernelConstant⁻¹ *
          ((2 * eLpNorm (φ.toLp 2 volume : ℝ → ℂ) ⊤ volume ^ (2 : ℕ)) *
              translationEnergy F +
            (2 * ‖F‖ₑ ^ (2 : ℕ)) *
              (∫⁻ h : ℝ, ENNReal.ofReal (schwartzDifferenceMajorant φ h))) := by
        gcongr
      _ ≤ halfKernelConstant⁻¹ *
          (2 * S ^ (2 : ℕ) * (halfKernelConstant * E) +
            20 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral * E) := by
        gcongr
      _ = _ := rfl
  calc
    ‖P‖ₑ ^ (2 : ℕ) ≤ ‖Hs.toL2 (by norm_num) P‖ₑ ^ (2 : ℕ) +
        homogeneousFourierEnergy (1 / 2 : ℝ) (Hs.toL2 (by norm_num) P) :=
      enorm_Hs_half_sq_le_mass_add_homogeneous P
    _ ≤ S ^ (2 : ℕ) * E + halfKernelConstant⁻¹ *
        (2 * S ^ (2 : ℕ) * (halfKernelConstant * E) +
          20 * S ^ (2 : ℕ) * smoothMultiplierKernelIntegral * E) :=
      add_le_add hmassP henergyP
    _ = smoothHsMultiplierConstantSq * S ^ (2 : ℕ) * E := by
      unfold smoothHsMultiplierConstantSq
      ring
    _ = _ := by rfl

theorem schwartzHsMultiplier_norm_le (φ : SchwartzMap ℝ ℂ)
    (f : Hs (1 / 2 : ℝ)) :
    ‖schwartzHsMultiplier φ f‖ ≤
      Real.sqrt smoothHsMultiplierConstantSq.toReal *
        (SchwartzMap.seminorm ℂ 0 0 φ +
          SchwartzMap.seminorm ℂ 0 1 φ) * ‖f‖ := by
  let S : ℝ := SchwartzMap.seminorm ℂ 0 0 φ +
    SchwartzMap.seminorm ℂ 0 1 φ
  let K : ℝ := smoothHsMultiplierConstantSq.toReal
  let g : Hs (1 / 2 : ℝ) := schwartzHsMultiplier φ f
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hsq := schwartzHsMultiplier_enorm_sq_le φ f
  have hrightTop : smoothHsMultiplierConstantSq *
        ENNReal.ofReal S ^ (2 : ℕ) * ‖f‖ₑ ^ (2 : ℕ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top smoothHsMultiplierConstantSq_lt_top.ne
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    · exact ENNReal.pow_ne_top enorm_ne_top
  have hreal := (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top enorm_ne_top)
    hrightTop).mpr (by simpa [g, S] using hsq)
  have hsqReal : ‖g‖ ^ 2 ≤ K * S ^ 2 * ‖f‖ ^ 2 := by
    dsimp [g]
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ofReal_norm,
      ENNReal.toReal_ofReal hS, toReal_enorm, K, pow_two] using hreal
  have hsqrt : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  have hrhs0 : 0 ≤ Real.sqrt K * S * ‖f‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg K) hS) (norm_nonneg f)
  have hsquare : (Real.sqrt K * S * ‖f‖) ^ 2 = K * S ^ 2 * ‖f‖ ^ 2 := by
    calc
      (Real.sqrt K * S * ‖f‖) ^ 2 =
          (Real.sqrt K) ^ 2 * S ^ 2 * ‖f‖ ^ 2 := by ring
      _ = _ := by rw [hsqrt]
  rw [← hsquare] at hsqReal
  change ‖g‖ ≤ _
  nlinarith [sq_nonneg (‖g‖ - Real.sqrt K * S * ‖f‖), norm_nonneg g]

end CubicNLSPhaseRetrieval
