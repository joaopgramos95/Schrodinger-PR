import Lean_Code.StrichartzSpatialDuality
import Lean_Code.StrichartzTensorPairing

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators FourierTransform

noncomputable section

set_option maxHeartbeats 5000000

namespace CubicNLSPhaseRetrieval

/-- Pair a continuous representative of the free flow with a Schwartz spatial
test function. -/
def freeFlowPairing (φ b : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, schwartzFreeFlow φ (t, x) * b x

lemma freeFlowPairing_continuous (φ b : SchwartzMap ℝ ℂ) :
    Continuous (freeFlowPairing φ b) := by
  unfold freeFlowPairing
  apply continuous_of_dominated
      (bound := fun x : ℝ => (∫ ξ : ℝ, ‖(𝓕 φ) ξ‖) * ‖b x‖)
  · intro t
    exact ((schwartzFreeFlow_continuous φ).comp
      (continuous_const.prodMk continuous_id) |>.mul b.continuous).aestronglyMeasurable
  · intro t
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (schwartzFreeFlow_uniform_bound φ t x)
      (norm_nonneg _)
  · exact b.integrable.norm.const_mul _
  · filter_upwards with x
    exact ((schwartzFreeFlow_continuous φ).comp
      (continuous_id.prodMk continuous_const) |>.mul continuous_const)

lemma freeFlowPairing_bound (φ b : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖freeFlowPairing φ b t‖ ≤
      (∫ ξ : ℝ, ‖(𝓕 φ) ξ‖) * ∫ x : ℝ, ‖b x‖ := by
  unfold freeFlowPairing
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (b.integrable.norm.const_mul _)
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (schwartzFreeFlow_uniform_bound φ t x)
    (norm_nonneg _)

lemma freeFlowPairing_tail_bound (φ b : SchwartzMap ℝ ℂ) (t : ℝ) (ht : t ≠ 0) :
    ‖freeFlowPairing φ b t‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        schwartzL1E φ * schwartzL1E b := by
  have hφker := free_kernel_explicit t ht φ
  have hflow := schwartzFreeFlow_slice_ae φ t
  unfold freeFlowPairing
  calc
    ‖∫ x : ℝ, schwartzFreeFlow φ (t, x) * b x‖ₑ =
        ‖∫ x : ℝ, freeKernelOp t φ x * b x‖ₑ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hflow, hφker] with x hx hkx
      rw [hx, hkx]
    _ ≤ ∫⁻ x : ℝ, ‖freeKernelOp t φ x * b x‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x : ℝ,
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
          schwartzL1E φ) * ‖b x‖ₑ := by
      apply lintegral_mono
      intro x
      change ‖freeKernelOp t φ x * b x‖ₑ ≤
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
          schwartzL1E φ) * ‖b x‖ₑ
      rw [enorm_mul]
      exact mul_le_mul_right' (freeKernelOp_schwartz_bound t x φ) _
    _ = (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
          schwartzL1E φ) * schwartzL1E b := by
      unfold schwartzL1E
      rw [lintegral_const_mul']
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (schwartzL1E_ne_top φ)
    _ = ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        schwartzL1E φ * schwartzL1E b := by ring

lemma freeFlowPairing_tail_bound_real (φ b : SchwartzMap ℝ ℂ) (t : ℝ) (ht : t ≠ 0) :
    ‖freeFlowPairing φ b t‖ ≤
      ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        (schwartzL1E φ).toReal * (schwartzL1E b).toReal := by
  have h := freeFlowPairing_tail_bound φ b t ht
  have htop : ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
      schwartzL1E φ * schwartzL1E b ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (schwartzL1E_ne_top φ))
      (schwartzL1E_ne_top b)
  have hr := ENNReal.toReal_mono htop h
  calc
    ‖freeFlowPairing φ b t‖ = (‖freeFlowPairing φ b t‖ₑ).toReal := by
      rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
    _ ≤ (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        schwartzL1E φ * schwartzL1E b).toReal := hr
    _ = ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        (schwartzL1E φ).toReal * (schwartzL1E b).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)]

/-- The model positive tail `t ↦ t⁻¹ᐟ²` on `(1,∞)`. -/
def positiveHalfTail (t : ℝ) : ℝ :=
  Set.indicator (Set.Ioi (1 : ℝ))
    (fun s => (max s 1) ^ (-(1 / 2 : ℝ))) t

lemma positiveHalfTail_memLp_four :
    MemLp positiveHalfTail 4 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable positiveHalfTail (volume : Measure ℝ) := by
    apply Measurable.aestronglyMeasurable
    unfold positiveHalfTail
    have hbase : Continuous (fun t : ℝ => max t 1) :=
      continuous_id.max continuous_const
    have hpow : Measurable (fun t : ℝ => (max t 1) ^ (-(1 / 2 : ℝ))) :=
      (hbase.rpow_const (fun t => Or.inl (ne_of_gt
        (lt_of_lt_of_le zero_lt_one (le_max_right t 1))))).measurable
    exact hpow.indicator measurableSet_Ioi
  apply (integrable_norm_rpow_iff hmeas (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).mp
  have hpoint : (fun t : ℝ => ‖positiveHalfTail t‖ ^ (4 : ℝ)) =
      Set.indicator (Set.Ioi (1 : ℝ)) (fun t => t ^ (-2 : ℝ)) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · have htmem : t ∈ Set.Ioi (1 : ℝ) := ht
      change 1 < t at ht
      rw [show positiveHalfTail t = t ^ (-(1 / 2 : ℝ)) by
        simp [positiveHalfTail, ht, max_eq_left (le_of_lt ht)],
        Set.indicator_of_mem htmem]
      have ht0 : 0 ≤ t := le_trans (by norm_num) (le_of_lt ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _),
        ← Real.rpow_mul ht0]
      norm_num
    · simp [positiveHalfTail, Set.indicator_of_notMem ht]
  simp only [ENNReal.toReal_ofNat]
  rw [hpoint, integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one

/-- The reflected model tail on `(-∞,-1)`. -/
def negativeHalfTail (t : ℝ) : ℝ := positiveHalfTail (-t)

lemma negativeHalfTail_memLp_four :
    MemLp negativeHalfTail 4 (volume : Measure ℝ) := by
  have hneg : MeasurePreserving (fun t : ℝ => -t) volume volume :=
    Measure.measurePreserving_neg volume
  exact positiveHalfTail_memLp_four.comp_measurePreserving hneg

lemma positiveHalfTail_of_one_lt {t : ℝ} (ht : 1 < t) :
    positiveHalfTail t = t ^ (-(1 / 2 : ℝ)) := by
  simp [positiveHalfTail, ht, max_eq_left (le_of_lt ht)]

lemma negativeHalfTail_of_lt_neg_one {t : ℝ} (ht : t < -1) :
    negativeHalfTail t = (-t) ^ (-(1 / 2 : ℝ)) := by
  unfold negativeHalfTail
  rw [positiveHalfTail_of_one_lt]
  linarith

/-- Each scalar spatial pairing of a Schwartz free flow belongs to `L⁴_t`.
This is the only decay input needed in the endpoint norming argument. -/
theorem freeFlowPairing_memLp_four (φ b : SchwartzMap ℝ ℂ) :
    MemLp (freeFlowPairing φ b) 4 (volume : Measure ℝ) := by
  let A : ℝ := (∫ ξ : ℝ, ‖(𝓕 φ) ξ‖) * ∫ x : ℝ, ‖b x‖
  let D : ℝ := (4 * Real.pi) ^ (-(1 / 2 : ℝ)) *
    (schwartzL1E φ).toReal * (schwartzL1E b).toReal
  let envelope : ℝ → ℝ := fun t =>
    A * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℝ)) t +
      D * positiveHalfTail t + D * negativeHalfTail t
  have hcompact : MemLp
      (Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℝ))) 4 volume :=
    memLp_indicator_const 4 measurableSet_Icc 1 (Or.inr (by simp))
  have henv : MemLp envelope 4 volume := by
    exact ((hcompact.const_mul A).add (positiveHalfTail_memLp_four.const_mul D)).add
      (negativeHalfTail_memLp_four.const_mul D)
  apply henv.of_le (freeFlowPairing_continuous φ b).aestronglyMeasurable
  filter_upwards with t
  change ‖freeFlowPairing φ b t‖ ≤ ‖envelope t‖
  by_cases hmid : t ∈ Set.Icc (-1 : ℝ) 1
  · have hposzero : positiveHalfTail t = 0 := by
      apply Set.indicator_of_notMem
      exact fun ht => (not_lt_of_ge hmid.2) ht
    have hnegzero : negativeHalfTail t = 0 := by
      unfold negativeHalfTail positiveHalfTail
      apply Set.indicator_of_notMem
      intro ht
      change 1 < -t at ht
      linarith [hmid.1]
    rw [show envelope t = A by
      simp only [envelope, Set.indicator_of_mem hmid, mul_one, hposzero, hnegzero,
        mul_zero, add_zero]]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact freeFlowPairing_bound φ b t
    · exact mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _)
  · have hout : t < -1 ∨ 1 < t := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hmid
    rcases hout with hleft | hright
    · have hcompzero : Set.indicator (Set.Icc (-1 : ℝ) 1)
          (fun _ => (1 : ℝ)) t = 0 :=
        Set.indicator_of_notMem hmid _
      have hposzero : positiveHalfTail t = 0 := by
        apply Set.indicator_of_notMem
        intro ht
        change 1 < t at ht
        linarith
      rw [show envelope t = D * negativeHalfTail t by
        simp only [envelope, hcompzero, hposzero, mul_zero, zero_add]]
      have ht0 : t ≠ 0 := by linarith
      have htail := freeFlowPairing_tail_bound_real φ b t ht0
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · calc
          ‖freeFlowPairing φ b t‖ ≤
              ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
                (schwartzL1E φ).toReal * (schwartzL1E b).toReal := htail
          _ = D * negativeHalfTail t := by
            rw [negativeHalfTail_of_lt_neg_one hleft,
              Real.mul_rpow (show 0 ≤ 4 * Real.pi by positivity) (abs_nonneg t),
              abs_of_neg (show t < 0 by linarith)]
            dsimp [D]
            ring
      · rw [negativeHalfTail_of_lt_neg_one hleft]
        dsimp [D]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
            ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
          (Real.rpow_nonneg (by linarith) _)
    · have hcompzero : Set.indicator (Set.Icc (-1 : ℝ) 1)
          (fun _ => (1 : ℝ)) t = 0 :=
        Set.indicator_of_notMem hmid _
      have hnegzero : negativeHalfTail t = 0 := by
        unfold negativeHalfTail positiveHalfTail
        apply Set.indicator_of_notMem
        intro ht
        change 1 < -t at ht
        linarith
      rw [show envelope t = D * positiveHalfTail t by
        simp only [envelope, hcompzero, hnegzero, mul_zero, zero_add, add_zero]]
      have ht0 : t ≠ 0 := by linarith
      have htail := freeFlowPairing_tail_bound_real φ b t ht0
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · calc
          ‖freeFlowPairing φ b t‖ ≤
              ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
                (schwartzL1E φ).toReal * (schwartzL1E b).toReal := htail
          _ = D * positiveHalfTail t := by
            rw [positiveHalfTail_of_one_lt hright,
              Real.mul_rpow (show 0 ≤ 4 * Real.pi by positivity) (abs_nonneg t),
              abs_of_pos (show 0 < t by linarith)]
            dsimp [D]
            ring
      · rw [positiveHalfTail_of_one_lt hright]
        dsimp [D]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
            ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
          (Real.rpow_nonneg (by linarith) _)

end CubicNLSPhaseRetrieval
