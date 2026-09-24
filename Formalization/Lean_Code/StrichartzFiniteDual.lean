import Lean_Code.StrichartzFiniteMax

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators FourierTransform

noncomputable section

set_option maxHeartbeats 5000000

namespace CubicNLSPhaseRetrieval

def conjugatePhase (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

lemma conjugatePhase_norm_le_one (z : ℂ) : ‖conjugatePhase z‖ ≤ 1 := by
  unfold conjugatePhase
  rw [Complex.norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · rw [div_self hz]

lemma conjugatePhase_mul (z : ℂ) : conjugatePhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [conjugatePhase, hz]
  · unfold conjugatePhase
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

lemma conjugatePhase_measurable : Measurable conjugatePhase := by
  unfold conjugatePhase
  exact Complex.continuous_conj.measurable.div
    (Complex.ofRealCLM.continuous.measurable.comp continuous_norm.measurable)

variable {n : ℕ}

/-- A positive normalization larger than the `L⁴` norm of the finite maximum. -/
def finiteDualScale (A : Fin (n + 1) → ℝ → ℂ) (ε : ℝ) : ℝ :=
  (eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)).toReal + ε

def finiteDualMagnitude (A : Fin (n + 1) → ℝ → ℂ) (ε : ℝ) (t : ℝ) : ℝ :=
  (finiteMaxProfile A t) ^ (3 : ℕ) / (finiteDualScale A ε) ^ (3 : ℕ)

/-- The one-sparse measurable dual coefficient attached to a finite maximum. -/
def finiteDualCoeff (A : Fin (n + 1) → ℝ → ℂ) (ε : ℝ)
    (i : Fin (n + 1)) (t : ℝ) : ℂ :=
  if finiteWinnerNat A t = i.val then
    (finiteDualMagnitude A ε t : ℂ) * conjugatePhase (A i t)
  else 0

lemma finiteDualScale_pos (A : Fin (n + 1) → ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    0 < finiteDualScale A ε := by
  unfold finiteDualScale
  positivity

lemma finiteDualMagnitude_nonneg (A : Fin (n + 1) → ℝ → ℂ) {ε : ℝ}
    (hscale : 0 < finiteDualScale A ε) (t : ℝ) : 0 ≤ finiteDualMagnitude A ε t := by
  unfold finiteDualMagnitude
  exact div_nonneg (pow_nonneg (finiteMaxProfile_nonneg A t) _)
    (pow_nonneg hscale.le _)

lemma finiteDualMagnitude_measurable (A : Fin (n + 1) → ℝ → ℂ)
    (hA : ∀ i, Measurable (A i)) (ε : ℝ) :
    Measurable (finiteDualMagnitude A ε) := by
  unfold finiteDualMagnitude
  exact ((finiteMaxProfile_measurable A hA).pow_const 3).div_const _

lemma finiteDualCoeff_measurable (A : Fin (n + 1) → ℝ → ℂ)
    (hA : ∀ i, Measurable (A i)) (ε : ℝ) (i : Fin (n + 1)) :
    Measurable (finiteDualCoeff A ε i) := by
  unfold finiteDualCoeff
  apply Measurable.ite
  · exact (finiteWinnerNat_measurable A hA) (measurableSet_singleton i.val)
  · exact (Complex.ofRealCLM.continuous.measurable.comp
      (finiteDualMagnitude_measurable A hA ε)).mul
        (conjugatePhase_measurable.comp (hA i))
  · exact measurable_const

lemma finiteDualCoeff_norm_le (A : Fin (n + 1) → ℝ → ℂ) {ε : ℝ}
    (hscale : 0 < finiteDualScale A ε) (i : Fin (n + 1)) (t : ℝ) :
    ‖finiteDualCoeff A ε i t‖ ≤ finiteDualMagnitude A ε t := by
  unfold finiteDualCoeff
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (finiteDualMagnitude_nonneg A hscale t)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (conjugatePhase_norm_le_one (A i t)) (finiteDualMagnitude_nonneg A hscale t)
  · simpa only [norm_zero] using finiteDualMagnitude_nonneg A hscale t

lemma finiteDualMagnitude_memLp (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ))
    {ε : ℝ} (hscale : 0 < finiteDualScale A ε) :
    MemLp (finiteDualMagnitude A ε) (4 / 3) (volume : Measure ℝ) := by
  have hM := finiteMaxProfile_memLp_four A hmeas hA
  have hpow := hM.norm_rpow_div (3 : ℝ≥0∞)
  have hp : MemLp (fun t : ℝ => (finiteMaxProfile A t) ^ (3 : ℕ))
      (4 / 3) volume := by
    convert hpow using 1
    · funext t
      rw [show finiteMaxProfile A t = ‖finiteMaxProfile A t‖ by
        rw [Real.norm_eq_abs, abs_of_nonneg (finiteMaxProfile_nonneg A t)]]
      norm_num
  have hscale0 : finiteDualScale A ε ≠ 0 := ne_of_gt hscale
  rw [show finiteDualMagnitude A ε = fun t =>
      ((finiteDualScale A ε) ^ (3 : ℕ))⁻¹ * (finiteMaxProfile A t) ^ (3 : ℕ) by
    funext t
    unfold finiteDualMagnitude
    field_simp]
  exact hp.const_mul _

lemma finiteDualCoeff_memLp (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ))
    {ε : ℝ} (hscale : 0 < finiteDualScale A ε) (i : Fin (n + 1)) :
    MemLp (finiteDualCoeff A ε i) (4 / 3) (volume : Measure ℝ) := by
  apply (finiteDualMagnitude_memLp A hmeas hA hscale).of_le
    (finiteDualCoeff_measurable A hmeas ε i).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteDualMagnitude_nonneg A hscale t)]
  exact finiteDualCoeff_norm_le A hscale i t

lemma finiteDualMagnitude_zero_eLpNorm (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ))
    (hpos : 0 < eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)) :
    eLpNorm (finiteDualMagnitude A 0) (4 / 3) (volume : Measure ℝ) = 1 := by
  let L : ℝ≥0∞ := eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)
  have hM := finiteMaxProfile_memLp_four A hmeas hA
  have hLtop : L ≠ ⊤ := ne_of_lt hM.2
  have hLreal : 0 < L.toReal := ENNReal.toReal_pos hpos.ne' hLtop
  have hscale : finiteDualScale A 0 = L.toReal := by
    simp [finiteDualScale, L]
  have hfun : finiteDualMagnitude A 0 =
      ((L.toReal ^ (3 : ℕ))⁻¹ : ℝ) •
        (fun t => ‖finiteMaxProfile A t‖ ^ (3 : ℝ)) := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ‖finiteMaxProfile A t‖ = finiteMaxProfile A t by
      rw [Real.norm_eq_abs, abs_of_nonneg (finiteMaxProfile_nonneg A t)]]
    norm_num
    unfold finiteDualMagnitude
    rw [hscale]
    field_simp
  rw [hfun, eLpNorm_const_smul,
    eLpNorm_norm_rpow (finiteMaxProfile A) (by norm_num : (0 : ℝ) < 3)]
  have hexp : (4 / 3 : ℝ≥0∞) * ENNReal.ofReal 3 = 4 := by
    norm_num [ENNReal.div_eq_inv_mul]
    calc
      (3 : ℝ≥0∞)⁻¹ * 4 * 3 = 4 * ((3 : ℝ≥0∞)⁻¹ * 3) := by ring
      _ = 4 := by rw [ENNReal.inv_mul_cancel] <;> norm_num
  rw [hexp]
  have hL : ENNReal.ofReal L.toReal = L := ENNReal.ofReal_toReal hLtop
  rw [show ‖((L.toReal ^ (3 : ℕ))⁻¹ : ℝ)‖ₑ = (L ^ (3 : ℕ))⁻¹ by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr (pow_pos hLreal 3)),
      ENNReal.ofReal_inv_of_pos (pow_pos hLreal 3), ENNReal.ofReal_pow,
      hL]
    exact ENNReal.toReal_nonneg]
  rw [show eLpNorm (finiteMaxProfile A) 4 volume ^ (3 : ℝ) =
      L ^ (3 : ℕ) by
    change L ^ (3 : ℝ) = L ^ (3 : ℕ)
    exact ENNReal.rpow_natCast L 3]
  exact ENNReal.inv_mul_cancel (pow_ne_zero 3 hpos.ne') (by finiteness)

lemma integral_finiteMaxProfile_pow_four (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ)) :
    ∫ t : ℝ, (finiteMaxProfile A t) ^ (4 : ℕ) =
      (eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)).toReal ^ (4 : ℕ) := by
  have hM := finiteMaxProfile_memLp_four A hmeas hA
  have he := hM.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
  have hnorm (t : ℝ) : ‖finiteMaxProfile A t‖ = finiteMaxProfile A t := by
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteMaxProfile_nonneg A t)]
  simp only [ENNReal.toReal_ofNat, hnorm] at he
  have he' : eLpNorm (finiteMaxProfile A) 4 volume =
      ENNReal.ofReal
        ((∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹)) := by
    rw [he]
    congr 2
    apply integral_congr_ae
    filter_upwards with t
    exact Real.rpow_natCast (finiteMaxProfile A t) 4
  have hI : 0 ≤ ∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ) :=
    integral_nonneg fun t => pow_nonneg (finiteMaxProfile_nonneg A t) 4
  have hroot : (eLpNorm (finiteMaxProfile A) 4 volume).toReal =
      (∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹) := by
    calc
      (eLpNorm (finiteMaxProfile A) 4 volume).toReal =
          (ENNReal.ofReal
            ((∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹))).toReal :=
        congrArg ENNReal.toReal he'
      _ = (∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹) :=
        ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)
  calc
    ∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ) =
        ((∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹)) ^ (4 : ℕ) := by
      symm
      exact Real.rpow_inv_natCast_pow hI (by norm_num)
    _ = (eLpNorm (finiteMaxProfile A) 4 volume).toReal ^ (4 : ℕ) := by rw [hroot]

lemma finiteDual_product_integrable (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ))
    {ε : ℝ} (hscale : 0 < finiteDualScale A ε) (i : Fin (n + 1)) :
    Integrable (fun t => finiteDualCoeff A ε i t * A i t) volume := by
  have hc := finiteDualCoeff_memLp A hmeas hA hscale i
  refine ⟨(finiteDualCoeff_measurable A hmeas ε i).aestronglyMeasurable.mul
    (hmeas i).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ t : ℝ, ‖finiteDualCoeff A ε i t * A i t‖ₑ) =
        ∫⁻ t : ℝ, ‖finiteDualCoeff A ε i t‖ₑ * ‖A i t‖ₑ := by
      apply lintegral_congr
      intro t
      rw [enorm_mul]
    _ ≤ eLpNorm (fun t => ‖finiteDualCoeff A ε i t‖ₑ) (4 / 3) volume *
        eLpNorm (fun t => ‖A i t‖ₑ) 4 volume :=
      lintegral_mul_le_eLpNorm_four_thirds_four _ _
        (finiteDualCoeff_measurable A hmeas ε i).enorm.aemeasurable
        (hmeas i).enorm.aemeasurable
    _ < ⊤ := by
      rw [eLpNorm_enorm, eLpNorm_enorm]
      exact ENNReal.mul_lt_top hc.2 (hA i).2

lemma sum_finiteDualCoeff_norm_le (A : Fin (n + 1) → ℝ → ℂ) {ε : ℝ}
    (hscale : 0 < finiteDualScale A ε) (t : ℝ) :
    (∑ i : Fin (n + 1), ‖finiteDualCoeff A ε i t‖) ≤
      finiteDualMagnitude A ε t := by
  let w : Fin (n + 1) := finiteWinner A t
  rw [Finset.sum_eq_single w]
  · exact finiteDualCoeff_norm_le A hscale w t
  · intro i hi hne
    have hn : finiteWinnerNat A t ≠ i.val := by
      intro heq
      apply hne
      apply Fin.ext
      exact heq.symm
    simp [finiteDualCoeff, hn]
  · simp

lemma sum_finiteDualCoeff_mul (A : Fin (n + 1) → ℝ → ℂ) {ε : ℝ}
    (t : ℝ) :
    (∑ i : Fin (n + 1), finiteDualCoeff A ε i t * A i t) =
      ((finiteMaxProfile A t) ^ (4 : ℕ) /
        (finiteDualScale A ε) ^ (3 : ℕ) : ℝ) := by
  let w : Fin (n + 1) := finiteWinner A t
  rw [Finset.sum_eq_single w]
  · have hw : finiteWinnerNat A t = w.val := rfl
    rw [finiteDualCoeff, if_pos hw, mul_assoc, conjugatePhase_mul]
    push_cast
    unfold finiteDualMagnitude
    rw [finiteMaxProfile_eq]
    dsimp [w]
    push_cast
    ring
  · intro i hi hne
    have hn : finiteWinnerNat A t ≠ i.val := by
      intro heq
      apply hne
      apply Fin.ext
      exact heq.symm
    simp [finiteDualCoeff, hn]
  · simp

lemma integral_sum_finiteDualCoeff_mul_zero (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ))
    (hpos : 0 < eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)) :
    ∫ t : ℝ, ∑ i : Fin (n + 1), finiteDualCoeff A 0 i t * A i t =
      ((eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)).toReal : ℂ) := by
  let L : ℝ≥0∞ := eLpNorm (finiteMaxProfile A) 4 (volume : Measure ℝ)
  have hM := finiteMaxProfile_memLp_four A hmeas hA
  have hLtop : L ≠ ⊤ := ne_of_lt hM.2
  have hLreal : 0 < L.toReal := ENNReal.toReal_pos hpos.ne' hLtop
  have hscale : 0 < finiteDualScale A 0 := by
    simpa [finiteDualScale, L] using hLreal
  rw [show (∫ t : ℝ, ∑ i : Fin (n + 1), finiteDualCoeff A 0 i t * A i t) =
      ∫ t : ℝ, (((finiteMaxProfile A t) ^ (4 : ℕ) /
        (finiteDualScale A 0) ^ (3 : ℕ) : ℝ) : ℂ) by
    apply integral_congr_ae
    filter_upwards with t
    exact sum_finiteDualCoeff_mul A (ε := 0) t]
  rw [show finiteDualScale A 0 = L.toReal by simp [finiteDualScale, L]]
  push_cast
  rw [integral_div]
  have hcast : (∫ t : ℝ, (finiteMaxProfile A t : ℂ) ^ (4 : ℕ)) =
      ((show ℝ from ∫ t : ℝ, finiteMaxProfile A t ^ (4 : ℕ)) : ℂ) := by
    have hi := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ))
      (f := fun t : ℝ => finiteMaxProfile A t ^ (4 : ℕ))
    have hp : (∫ t : ℝ, (finiteMaxProfile A t : ℂ) ^ (4 : ℕ)) =
        ∫ t : ℝ, ((finiteMaxProfile A t ^ (4 : ℕ) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      norm_cast
    exact hp.trans hi
  rw [hcast]
  rw [integral_finiteMaxProfile_pow_four A hmeas hA]
  rw [show eLpNorm (finiteMaxProfile A) 4 volume = L from rfl]
  calc
    ((show ℝ from L.toReal ^ (4 : ℕ)) : ℂ) / (L.toReal : ℂ) ^ (3 : ℕ) =
        ((L.toReal ^ (4 : ℕ) / L.toReal ^ (3 : ℕ) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = (L.toReal : ℂ) := by
      congr 1
      field_simp

end CubicNLSPhaseRetrieval
