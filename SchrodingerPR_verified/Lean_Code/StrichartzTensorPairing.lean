import Lean_Code.StrichartzTensorL1

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 5000000

namespace CubicNLSPhaseRetrieval

lemma freeKernelOp_schwartz_bound (t x : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖freeKernelOp t f x‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E f := by
  unfold freeKernelOp schwartzL1E
  calc
    ‖∫ y : ℝ, freeKernel t x y * f y‖ₑ ≤
        ∫⁻ y : ℝ, ‖freeKernel t x y * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y : ℝ,
        ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * ‖f y‖ₑ := by
      apply lintegral_congr
      intro y
      rw [enorm_mul, enorm_freeKernel]
    _ = ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        ∫⁻ y : ℝ, ‖f y‖ₑ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top

lemma inner_freeProp_schwartz_bound (t : ℝ) (f g : SchwartzMap ℝ ℂ) (ht : t ≠ 0) :
    ‖@inner ℂ L2 _ (f.toLp 2 volume) (freeProp t (g.toLp 2 volume))‖ₑ ≤
      schwartzL1E f *
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E g) := by
  rw [MeasureTheory.L2.inner_def]
  have hfcoe : (⇑(f.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume] f :=
    (f.memLp 2 volume).coeFn_toLp
  have hgker := free_kernel_explicit t ht g
  calc
    ‖∫ x : ℝ, @inner ℂ ℂ _ ((f.toLp 2 volume) x)
        ((freeProp t (g.toLp 2 volume)) x)‖ₑ ≤
        ∫⁻ x : ℝ, ‖@inner ℂ ℂ _ ((f.toLp 2 volume) x)
          ((freeProp t (g.toLp 2 volume)) x)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ * ‖freeKernelOp t g x‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [hfcoe, hgker] with x hfx hgx
      rw [hfx, hgx]
      simpa only [RCLike.inner_apply, enorm_mul, RCLike.enorm_conj, mul_comm]
    _ ≤ ∫⁻ x : ℝ, ‖f x‖ₑ *
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E g) := by
      apply lintegral_mono
      intro x
      exact mul_le_mul_left' (freeKernelOp_schwartz_bound t x g) _
    _ = schwartzL1E f *
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E g) := by
      unfold schwartzL1E
      rw [lintegral_mul_const'']
      exact f.continuous.enorm.aemeasurable

lemma inner_integral_left {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] (f : X → E) (hf : Integrable f μ) (c : E) :
    @inner ℂ E _ (∫ x, f x ∂μ) c = ∫ x, @inner ℂ E _ (f x) c ∂μ := by
  symm
  exact ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul
    (innerSLFlip ℂ c) hf

lemma inner_tensorAdjoint_double {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    @inner ℂ L2 _ (tensorAdjoint a b) (tensorAdjoint a b) =
      ∫ s : ℝ, ∫ r : ℝ,
        @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r) := by
  have hcur := tensorAdjointCurve_integrable a b
  rw [tensorAdjoint, inner_integral_left _ hcur]
  apply integral_congr_ae
  filter_upwards with s
  exact (innerSL ℂ (tensorAdjointCurve a b s)).integral_comp_comm hcur |>.symm

lemma inner_tensorAdjointCurve_bound {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ)
    (s r : ℝ) (hsr : s ≠ r) :
    ‖@inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ ≤
      tensorSliceL1 a b s *
        (ENNReal.ofReal ((4 * Real.pi * |s - r|) ^ (-(1 / 2 : ℝ))) *
          tensorSliceL1 a b r) := by
  have htime : s - r ≠ 0 := sub_ne_zero.mpr hsr
  have hinner :
      @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r) =
        @inner ℂ L2 _ ((tensorConjSlice a b s).toLp 2 volume)
          (freeProp (s - r) ((tensorConjSlice a b r).toLp 2 volume)) := by
    unfold tensorAdjointCurve
    rw [← inner_freeProp s]
    congr 1
    · rw [propagator_unitary.2.1]
      convert propagator_unitary.2.2.1 _ using 1
      ring
    · rw [propagator_unitary.2.1]
      congr 2
  rw [hinner]
  exact inner_freeProp_schwartz_bound (s - r)
    (tensorConjSlice a b s) (tensorConjSlice a b r) htime

def tensorG {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (tensorRaw a b p)

lemma tensorG_measurable {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    Measurable (tensorG a b) := by
  unfold tensorG tensorRaw
  exact Complex.continuous_conj.measurable.comp (by fun_prop)

lemma spatialL1_tensorG {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) :
    spatialL1 (tensorG a b) t = tensorSliceL1 a b t := by
  unfold spatialL1 tensorSliceL1 schwartzL1E tensorG
  apply lintegral_congr
  intro x
  rw [tensorConjSlice_apply]

lemma lintegral_mul_le_eLpNorm_four_thirds_four
    (q F : ℝ → ℝ≥0∞) (hq : AEMeasurable q volume) (hF : AEMeasurable F volume) :
    ∫⁻ t : ℝ, q t * F t ≤ eLpNorm q (4 / 3) volume * eLpNorm F 4 volume := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (4 / 3 : ℝ).HolderConjugate 4 by
      rw [Real.holderConjugate_iff]
      constructor <;> norm_num)
    hq hF
  have hqnorm : eLpNorm q (4 / 3) volume =
      (∫⁻ t : ℝ, q t ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (4 / 3 : ℝ≥0∞) ≠ 0)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    congr 1
    · apply lintegral_congr
      intro t
      rw [enorm_eq_self]
      congr 1
      norm_num [ENNReal.toReal_div]
    · norm_num [ENNReal.toReal_div]
  have hFnorm : eLpNorm F 4 volume =
      (∫⁻ t : ℝ, F t ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    simp only [enorm_eq_self]
    norm_num
  rw [hqnorm, hFnorm]
  have hexp : (1 / (4 / 3 : ℝ)) = 3 / 4 := by norm_num
  simpa only [Pi.mul_apply, hexp] using hh

lemma freeKernel_time_factor (t : ℝ) :
    ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (|t| ^ (-(1 / 2 : ℝ))) := by
  rw [show 4 * Real.pi * |t| = (4 * Real.pi) * |t| by ring]
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (abs_nonneg t)]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]

end CubicNLSPhaseRetrieval
