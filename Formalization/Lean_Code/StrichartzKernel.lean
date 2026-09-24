import Lean_Code.FreeKernelProofs
import Lean_Code.FractionalIntegration
import Lean_Code.ScalarMixedNorms

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap

noncomputable section

set_option maxHeartbeats 2000000

namespace CubicNLSPhaseRetrieval

private def spacetimeSlice (G : 𝓢(ℝ × ℝ, ℂ)) (s : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (K := 1) (g := fun x : ℝ => (s, x)) (by
      have h := (Function.HasTemperateGrowth.const (s, 0)).add
        (ContinuousLinearMap.inr ℝ ℝ ℝ).hasTemperateGrowth
      convert h using 1
      funext x
      simp) (by
      rw [antilipschitzWith_iff_le_mul_dist]
      intro x y
      simp)
    G

private lemma spacetimeSlice_apply (G : 𝓢(ℝ × ℝ, ℂ)) (s x : ℝ) :
    spacetimeSlice G s x = G (s, x) := rfl

def spatialL1 (G : ℝ × ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ‖G (t, x)‖ₑ

def spatialL1Complex (G : ℝ × ℝ → ℂ) (t : ℝ) : ℂ :=
  ((spatialL1 G t).toReal : ℝ)

def kernelTT (G : ℝ × ℝ → ℂ) (t x : ℝ) : ℂ :=
  ∫ s : ℝ, freeKernelOp (t - s) (fun y => G (s, y)) x

private lemma freeKernel_scale (t x y : ℝ) :
    ‖freeKernel t x y‖ₑ =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (|t| ^ (-(1 / 2 : ℝ))) := by
  rw [enorm_freeKernel]
  rw [show 4 * Real.pi * |t| = (4 * Real.pi) * |t| by ring]
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (abs_nonneg t)]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]

private lemma kernelTT_pointwise_bound (G : ℝ × ℝ → ℂ) (t x : ℝ) :
    ‖kernelTT G t x‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
        ∫⁻ s : ℝ, ENNReal.ofReal (|t - s| ^ (-(1 / 2 : ℝ))) * spatialL1 G s := by
  unfold kernelTT
  calc
    ‖∫ s : ℝ, freeKernelOp (t - s) (fun y => G (s, y)) x‖ₑ ≤
        ∫⁻ s : ℝ, ‖freeKernelOp (t - s) (fun y => G (s, y)) x‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s : ℝ, (ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (|t - s| ^ (-(1 / 2 : ℝ)))) * spatialL1 G s := by
      apply lintegral_mono
      intro s
      unfold freeKernelOp spatialL1
      calc
        ‖∫ y : ℝ, freeKernel (t - s) x y * G (s, y)‖ₑ ≤
            ∫⁻ y : ℝ, ‖freeKernel (t - s) x y * G (s, y)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ y : ℝ,
            (ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
              ENNReal.ofReal (|t - s| ^ (-(1 / 2 : ℝ)))) * ‖G (s, y)‖ₑ := by
          apply lintegral_congr
          intro y
          rw [enorm_mul, freeKernel_scale]
        _ = (ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
              ENNReal.ofReal (|t - s| ^ (-(1 / 2 : ℝ)))) *
              ∫⁻ y : ℝ, ‖G (s, y)‖ₑ := by
          rw [lintegral_const_mul']
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
        ∫⁻ s : ℝ, ENNReal.ofReal (|t - s| ^ (-(1 / 2 : ℝ))) * spatialL1 G s := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top

lemma spatialL1_measurable (G : ℝ × ℝ → ℂ) (hG : Measurable G) :
    Measurable (spatialL1 G) := by
  unfold spatialL1
  exact hG.enorm.lintegral_prod_right'

lemma spatialL1Complex_enorm (G : ℝ × ℝ → ℂ)
    (hfinite : ∀ t, spatialL1 G t ≠ ⊤) (t : ℝ) :
    ‖spatialL1Complex G t‖ₑ = spatialL1 G t := by
  unfold spatialL1Complex
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfinite t)]

lemma spatialL1Complex_eLpNorm (G : ℝ × ℝ → ℂ)
    (hfinite : ∀ t, spatialL1 G t ≠ ⊤) :
    eLpNorm (spatialL1Complex G) (4 / 3) volume =
      scalarMixedENorm volume volume (4 / 3) 1 G := by
  unfold scalarMixedENorm sectionENorm
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  apply eLpNorm_congr_enorm_ae
  filter_upwards with t
  rw [spatialL1Complex_enorm G hfinite]
  exact (enorm_eq_self _).symm

lemma spatialL1Complex_memLp (G : ℝ × ℝ → ℂ) (hG : Measurable G)
    (hfinite : ∀ t, spatialL1 G t ≠ ⊤)
    (hmix : scalarMixedENorm volume volume (4 / 3) 1 G < ⊤) :
    MemLp (spatialL1Complex G) (4 / 3) volume := by
  have hmeas : AEStronglyMeasurable (spatialL1Complex G) volume := by
    exact (Complex.ofRealCLM.continuous.measurable.comp
      (ENNReal.measurable_toReal.comp (spatialL1_measurable G hG))).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [spatialL1Complex_eLpNorm G hfinite]
  exact hmix

lemma fractionalIntegral_spatialL1 (G : ℝ × ℝ → ℂ)
    (hfinite : ∀ t, spatialL1 G t ≠ ⊤) (t : ℝ) :
    fractionalIntegral (1 / 2) (spatialL1Complex G) t =
      ∫⁻ s : ℝ, ENNReal.ofReal (|t - s| ^ (-(1 / 2 : ℝ))) * spatialL1 G s := by
  unfold fractionalIntegral
  apply lintegral_congr
  intro s
  congr 1
  rw [← enorm_eq_nnnorm, spatialL1Complex_enorm G hfinite]

lemma eLpNorm_ennreal_const_mul
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (g : T → ℝ≥0∞)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrtop : r ≠ ⊤) :
    eLpNorm (fun x => c * g x) r mu = c * eLpNorm g r mu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop]
  simp only [enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
  rw [lintegral_const_mul' _ _
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hc).ne,
    ENNReal.mul_rpow_of_nonneg]
  · rw [← ENNReal.rpow_mul]
    field_simp [ENNReal.toReal_ne_zero.mpr ⟨hr0, hrtop⟩]
    simp only [ENNReal.rpow_one]
  · positivity

/-- The scalar `TT*` kernel estimate obtained from the explicit free kernel
and one-dimensional Hardy--Littlewood--Sobolev. -/
theorem kernelTT_mixed_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ G : ℝ × ℝ → ℂ, Measurable G →
      (∀ t, spatialL1 G t ≠ ⊤) →
      scalarMixedENorm volume volume (4 / 3) 1 G < ⊤ →
      scalarMixedENorm volume volume 4 ⊤
          (fun p => kernelTT G p.1 p.2) ≤
        C * scalarMixedENorm volume volume (4 / 3) 1 G := by
  have hp : (1 : ℝ≥0∞) < 4 / 3 := by
    rw [← ENNReal.toReal_lt_toReal (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  have hpq : (4 / 3 : ℝ≥0∞) < 4 := by
    rw [← ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)]
    norm_num
  have hexp : (4 : ℝ≥0∞)⁻¹ =
      (4 / 3 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (1 / 2 : ℝ) := by
    have hl : (4 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
    have hdiv : (4 / 3 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvtop : (4 / 3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hdiv
    have hr : (4 / 3 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.sub_ne_top hinvtop
    have hle : ENNReal.ofReal (1 / 2 : ℝ) ≤ (4 / 3 : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.toReal_le_toReal (by norm_num) hinvtop]
      norm_num
    apply le_antisymm
    · rw [← ENNReal.toReal_le_toReal hl hr,
        ENNReal.toReal_sub_of_le hle hinvtop]
      norm_num
    · rw [← ENNReal.toReal_le_toReal hr hl,
        ENNReal.toReal_sub_of_le hle hinvtop]
      norm_num
  obtain ⟨Ch, hChtop, hHLS⟩ := HLS_time (1 / 2) (by norm_num) (by norm_num)
    (4 / 3) 4 hp hpq (by norm_num) (by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
      exact hexp)
  let c : ℝ≥0∞ := ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ)))
  refine ⟨c * Ch, ENNReal.mul_lt_top (by simp [c]) hChtop, ?_⟩
  intro G hG hfinite hmix
  have hgMem := spatialL1Complex_memLp G hG hfinite hmix
  have hfrac := hHLS (spatialL1Complex G) hgMem
  have hsection (t : ℝ) :
      sectionENorm volume ⊤ (fun p => kernelTT G p.1 p.2) t ≤
        c * fractionalIntegral (1 / 2) (spatialL1Complex G) t := by
    unfold sectionENorm
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards with x
    rw [fractionalIntegral_spatialL1 G hfinite]
    exact kernelTT_pointwise_bound G t x
  unfold scalarMixedENorm
  calc
    eLpNorm (fun t => sectionENorm volume ⊤
        (fun p => kernelTT G p.1 p.2) t) 4 volume ≤
        eLpNorm (fun t => c * fractionalIntegral (1 / 2)
          (spatialL1Complex G) t) 4 volume := by
      apply eLpNorm_mono_enorm
      intro t
      simpa only [enorm_eq_self] using hsection t
    _ = c * eLpNorm (fractionalIntegral (1 / 2)
          (spatialL1Complex G)) 4 volume := by
      exact eLpNorm_ennreal_const_mul volume c (by simp [c]) _ 4 (by norm_num) (by norm_num)
    _ ≤ c * (Ch * eLpNorm (spatialL1Complex G) (4 / 3) volume) :=
      mul_le_mul_left' hfrac c
    _ = (c * Ch) * scalarMixedENorm volume volume (4 / 3) 1 G := by
      rw [spatialL1Complex_eLpNorm G hfinite]
      ring

end CubicNLSPhaseRetrieval
