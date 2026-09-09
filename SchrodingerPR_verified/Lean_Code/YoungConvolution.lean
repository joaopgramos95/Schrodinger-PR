import Lean_Code.L1L2FourierBridge
import Mathlib.Analysis.Convolution

open Filter MeasureTheory
open scoped ENNReal Convolution

noncomputable section

namespace CubicNLSPhaseRetrieval

def complexMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

lemma convolution_mul_aestronglyMeasurable
    (k f : ℝ → ℂ) (hk : Measurable k) (hf : Measurable f) :
    AEStronglyMeasurable (k ⋆[complexMulCLM] f) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => k p.2 * f (p.1 - p.2)) (volume.prod volume) :=
    ((hk.comp measurable_snd).aestronglyMeasurable.mul
      (hf.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable)
  exact hjoint.integral_prod_right'

lemma convolution_mul_enorm_sq_le
    (k f : ℝ → ℂ) (hk : Measurable k) (hf : Measurable f)
    (x : ℝ) :
    ‖(k ⋆[complexMulCLM] f) x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ y, ‖k y‖ₑ) * ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) := by
  let K : ℝ → ℝ≥0∞ := fun y => ‖k y‖ₑ
  let G : ℝ → ℝ≥0∞ := fun y => ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ)
  have hK : AEMeasurable K volume := hk.enorm.aemeasurable
  have hG : AEMeasurable G volume :=
    hk.enorm.aemeasurable.mul
      ((hf.comp (measurable_const.sub measurable_id)).enorm.aemeasurable.pow_const 2)
  have hcs := ENNReal.lintegral_mul_norm_pow_le hK hG
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hrewrite :
      (∫⁻ y, K y ^ (1 / 2 : ℝ) * G y ^ (1 / 2 : ℝ)) =
        ∫⁻ y, ‖k y * f (x - y)‖ₑ := by
    apply lintegral_congr
    intro y
    simp only [K, G, enorm_mul]
    have hkfin : ‖k y‖ₑ ≠ ⊤ := enorm_ne_top
    have hffin : ‖f (x - y)‖ₑ ≠ ⊤ := enorm_ne_top
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
    calc
      ‖k y‖ₑ ^ (1 / 2 : ℝ) *
          (‖k y‖ₑ ^ (1 / 2 : ℝ) * ‖f (x - y)‖ₑ) =
          (‖k y‖ₑ ^ (1 / 2 : ℝ) * ‖k y‖ₑ ^ (1 / 2 : ℝ)) *
            ‖f (x - y)‖ₑ := by ac_rfl
      _ = _ := by
        by_cases hk0 : ‖k y‖ₑ = 0
        · simp [hk0]
        · rw [← ENNReal.rpow_add (1 / 2 : ℝ) (1 / 2 : ℝ) hk0 hkfin]
          norm_num
  have hnorm : ‖(k ⋆[complexMulCLM] f) x‖ₑ ≤
      (∫⁻ y, ‖k y‖ₑ) ^ (1 / 2 : ℝ) *
        (∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    refine (enorm_integral_le_lintegral_enorm
      (fun y => k y * f (x - y))).trans ?_
    rw [← hrewrite]
    exact hcs
  have hsquare := ENNReal.rpow_le_rpow hnorm (show 0 ≤ (2 : ℝ) by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hsquare
  norm_num at hsquare
  simpa only [K, G, ENNReal.rpow_two] using hsquare

/-- Quantitative `L¹ * L² → L²` Young inequality for the scalar
convolution used by the smoothing argument. -/
theorem eLpNorm_convolution_mul_two_le
    (k f : ℝ → ℂ) (hkm : Measurable k) (hfm : Measurable f)
    (hk : Integrable k) (hf2 : MemLp f 2 volume) :
    eLpNorm (k ⋆[complexMulCLM] f) 2 volume ≤
      eLpNorm k 1 volume * eLpNorm f 2 volume := by
  let A : ℝ≥0∞ := ∫⁻ y, ‖k y‖ₑ
  let B : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)
  have hBlt : B < ⊤ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hf2.eLpNorm_lt_top
  have hBtop : B ≠ ⊤ := hBlt.ne
  have hbound :
      (∫⁻ x, ‖(k ⋆[complexMulCLM] f) x‖ₑ ^ (2 : ℝ)) ≤ A ^ 2 * B := by
    calc
      (∫⁻ x, ‖(k ⋆[complexMulCLM] f) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x, (∫⁻ y, ‖k y‖ₑ) *
            ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (convolution_mul_enorm_sq_le k f hkm hfm)
      _ = (∫⁻ y, ‖k y‖ₑ) *
          ∫⁻ x, ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul'' _ (by fun_prop)]
      _ = (∫⁻ y, ‖k y‖ₑ) *
          ∫⁻ y, ∫⁻ x, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) := by
        congr 1
        rw [lintegral_lintegral_swap]
        fun_prop
      _ = (∫⁻ y, ‖k y‖ₑ) *
          ∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro y
        rw [lintegral_const_mul'' _ (by fun_prop),
          lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ (2 : ℝ)) y]
      _ = A * (A * B) := by
        rw [show (∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) =
            A * B by
          change (∫⁻ y, ‖k y‖ₑ * B) = A * B
          rw [lintegral_mul_const' B (fun y => ‖k y‖ₑ) hBtop]]
      _ = A ^ 2 * B := by rw [pow_two]; ac_rfl
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by norm_num : (1 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_one]
  have hsqrt := ENNReal.rpow_le_rpow hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hsqrt
  norm_num at hsqrt
  simpa [A, B] using hsqrt

theorem convolution_mul_memLp_two
    (k f : ℝ → ℂ) (hkm : Measurable k) (hfm : Measurable f)
    (hk : Integrable k) (hf2 : MemLp f 2 volume) :
    MemLp (k ⋆[complexMulCLM] f) 2 volume := by
  have hm := convolution_mul_aestronglyMeasurable k f hkm hfm
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨hm.norm.pow 2, ?_⟩
  let A : ℝ≥0∞ := ∫⁻ y, ‖k y‖ₑ
  let B : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)
  have hAtop : A ≠ ⊤ := (hk.2).ne
  have hBlt : B < ⊤ := by
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hf2.eLpNorm_lt_top
  have hBtop : B ≠ ⊤ := hBlt.ne
  have hbound :
      (∫⁻ x, ‖‖(k ⋆[complexMulCLM] f) x‖ ^ 2‖ₑ) ≤
        A ^ 2 * B := by
    rw [show (fun x => ‖‖(k ⋆[complexMulCLM] f) x‖ ^ 2‖ₑ) =
        fun x => ‖(k ⋆[complexMulCLM] f) x‖ₑ ^ (2 : ℝ) by
      funext x
      rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
      norm_num [← ofReal_norm]]
    calc
      (∫⁻ x, ‖(k ⋆[complexMulCLM] f) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x, (∫⁻ y, ‖k y‖ₑ) *
            ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (convolution_mul_enorm_sq_le k f hkm hfm)
      _ = (∫⁻ y, ‖k y‖ₑ) *
          ∫⁻ x, ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul'' _ (by fun_prop)]
      _ = (∫⁻ y, ‖k y‖ₑ) *
          ∫⁻ y, ∫⁻ x, ‖k y‖ₑ * ‖f (x - y)‖ₑ ^ (2 : ℝ) := by
        congr 1
        rw [lintegral_lintegral_swap]
        fun_prop
      _ = (∫⁻ y, ‖k y‖ₑ) *
          ∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro y
        rw [lintegral_const_mul'' _ (by fun_prop),
          lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ (2 : ℝ)) y]
      _ = A * (A * B) := by
        rw [show (∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) =
            A * B by
          change (∫⁻ y, ‖k y‖ₑ * B) = A * B
          rw [lintegral_mul_const' B (fun y => ‖k y‖ₑ) hBtop]]
      _ = A ^ 2 * B := by rw [pow_two]; ac_rfl
  change (∫⁻ x, ‖‖(k ⋆[complexMulCLM] f) x‖ ^ 2‖ₑ) < ⊤
  exact hbound.trans_lt (ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top hAtop)) hBlt)

/-- Bundled real-norm form of the quantitative Young inequality. -/
theorem norm_convolution_mul_toLp_le
    (k f : ℝ → ℂ) (hkm : Measurable k) (hfm : Measurable f)
    (hk : Integrable k) (hf2 : MemLp f 2 volume) :
    ‖(convolution_mul_memLp_two k f hkm hfm hk hf2).toLp
        (k ⋆[complexMulCLM] f)‖ ≤
      ‖(memLp_one_iff_integrable.mpr hk).toLp k‖ * ‖hf2.toLp f‖ := by
  have h := eLpNorm_convolution_mul_two_le k f hkm hfm hk hf2
  have htop : eLpNorm k 1 volume * eLpNorm f 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hk).eLpNorm_ne_top
      hf2.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_mul,
    toReal_eLpNorm (convolution_mul_memLp_two k f hkm hfm hk hf2).1,
    toReal_eLpNorm (memLp_one_iff_integrable.mpr hk).1,
    toReal_eLpNorm hf2.1] at hr
  rw [Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm (convolution_mul_memLp_two k f hkm hfm hk hf2).1,
    toReal_eLpNorm (memLp_one_iff_integrable.mpr hk).1,
    toReal_eLpNorm hf2.1]
  exact hr

/-- The inverse Fourier transform turns an integrable convolution into a
pointwise product, with Mathlib's unitary `2π` normalization. -/
theorem inverseIntegral_convolution_mul (k f : ℝ → ℂ)
    (hk : Integrable k) (hf : Integrable f) (x : ℝ) :
    inverseIntegral (k ⋆[complexMulCLM] f) x =
      inverseIntegral k x * inverseIntegral f x := by
  unfold inverseIntegral
  simp only [complexMulCLM]
  rw [Real.fourierInv_eq_fourier_neg,
    Real.fourier_mul_convolution_eq hk hf,
    ← Real.fourierInv_eq_fourier_neg,
    ← Real.fourierInv_eq_fourier_neg]

end CubicNLSPhaseRetrieval
