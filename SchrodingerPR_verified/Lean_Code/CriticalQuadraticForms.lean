import Lean_Code.GagliardoHalf

/-!
# Critical H^{1/2} calculus and the current

Blueprint chapter: `chap:critical-calculus` (module 8).
Imports: modules 1 and 6.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology RealInnerProductSpace

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Division-free zero-set regularizer.  It is written in a complex-algebraic
form here and as a radial real map below for the differential estimates. -/
def Teps (ε : ℝ) (z : ℂ) : ℂ :=
  ((ε : ℂ) * z) / (((‖z‖ ^ 2 + ε : ℝ) : ℂ))

private def tepsR (ε : ℝ) (z : ℂ) : ℂ :=
  (ε / (‖z‖ ^ 2 + ε)) • z

private lemma teps_eq_tepsR (ε : ℝ) (_hε : 0 < ε) (z : ℂ) :
    Teps ε z = tepsR ε z := by
  rw [Teps, tepsR]
  change (ε : ℂ) * z / (((‖z‖ ^ 2 + ε : ℝ) : ℂ)) =
    (((ε / (‖z‖ ^ 2 + ε) : ℝ) : ℂ)) * z
  push_cast
  ring

private lemma tepsR_differentiable (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (tepsR ε) := by
  unfold tepsR
  have hc : Differentiable ℝ (fun z : ℂ => ε / (‖z‖ ^ 2 + ε)) := by
    intro z
    have hd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖ ^ 2 + ε) z :=
      ((hasStrictFDerivAt_norm_sq z).add_const ε).differentiableAt
    change DifferentiableAt ℝ
      ((fun _ : ℂ => ε) * (fun w : ℂ => (‖w‖ ^ 2 + ε)⁻¹)) z
    exact (differentiableAt_const (c := ε)).mul (hd.inv (by positivity))
  exact hc.smul (by fun_prop)

private lemma tepsR_fderiv_apply (ε : ℝ) (hε : 0 < ε) (z v : ℂ) :
    fderiv ℝ (tepsR ε) z v =
      (ε / (‖z‖ ^ 2 + ε)) • v -
        (2 * ε / (‖z‖ ^ 2 + ε) ^ 2 * inner ℝ z v) • z := by
  let d : ℝ := ‖z‖ ^ 2 + ε
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hden : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2 + ε)
      (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).add_const ε |>.hasFDerivAt
  have hinv : HasFDerivAt (fun w : ℂ => (‖w‖ ^ 2 + ε)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(d ^ 2)⁻¹)).comp
        (2 • innerSL ℝ z)) z := by
    exact (hasFDerivAt_inv hdpos.ne').comp z hden
  have hcoef : HasFDerivAt (fun w : ℂ => ε / (‖w‖ ^ 2 + ε))
      (ε • ((ContinuousLinearMap.toSpanSingleton ℝ (-(d ^ 2)⁻¹)).comp
        (2 • innerSL ℝ z))) z := by
    simpa only [div_eq_mul_inv] using hinv.const_mul ε
  change fderiv ℝ ((fun w : ℂ => ε / (‖w‖ ^ 2 + ε)) • id) z v = _
  rw [(hcoef.smul (hasFDerivAt_id z)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    innerSL_apply_apply]
  dsimp [d]
  push_cast
  field_simp
  ring

private lemma tepsR_fderiv_norm_le (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖fderiv ℝ (tepsR ε) z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [tepsR_fderiv_apply ε hε]
  let d : ℝ := ‖z‖ ^ 2 + ε
  let a : ℝ := ε / d
  let c : ℝ := 2 * ε / d ^ 2
  let q : ℝ := inner ℝ z v
  have hdpos : 0 < d := by dsimp [d]; positivity
  have ha0 : 0 ≤ a := div_nonneg hε.le hdpos.le
  have ha1 : a ≤ 1 := by
    rw [div_le_one₀ hdpos]
    dsimp [d]
    nlinarith [sq_nonneg ‖z‖]
  have hnorm : ‖a • v - (c * q) • z‖ ^ 2 =
      a ^ 2 * ‖v‖ ^ 2 - (4 * ε ^ 3 / d ^ 4) * q ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm z v]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    dsimp [a, c, q, d]
    field_simp
    ring
  have hmain : ‖a • v - (c * q) • z‖ ≤ ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hnorm]
    have hsub : 0 ≤ (4 * ε ^ 3 / d ^ 4) * q ^ 2 := by positivity
    calc
      a ^ 2 * ‖v‖ ^ 2 - (4 * ε ^ 3 / d ^ 4) * q ^ 2 ≤ a ^ 2 * ‖v‖ ^ 2 :=
        sub_le_self _ hsub
      _ ≤ 1 ^ 2 * ‖v‖ ^ 2 := by gcongr
      _ = ‖v‖ ^ 2 := by ring
  simpa only [a, c, q, d, one_mul] using hmain

/-- The radial zero-set regularizer is uniformly one-Lipschitz. -/
theorem Teps_lipschitz (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith 1 (Teps ε) := by
  have hradial : LipschitzWith 1 (tepsR ε) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (tepsR_differentiable ε hε)
    intro z
    exact_mod_cast tepsR_fderiv_norm_le ε hε z
  have hfun : Teps ε = tepsR ε := by
    funext z
    exact teps_eq_tepsR ε hε z
  rwa [hfun]

private lemma tepsR_norm (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖tepsR ε z‖ = (ε / (‖z‖ ^ 2 + ε)) * ‖z‖ := by
  rw [tepsR, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg hε.le (by positivity)

/-- The regularizer is dominated by its input. -/
theorem norm_Teps_le_norm (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖Teps ε z‖ ≤ ‖z‖ := by
  rw [teps_eq_tepsR ε hε, tepsR_norm ε hε]
  have hcoef0 : 0 ≤ ε / (‖z‖ ^ 2 + ε) := by positivity
  have hcoef1 : ε / (‖z‖ ^ 2 + ε) ≤ 1 := by
    rw [div_le_one₀ (by positivity)]
    nlinarith [sq_nonneg ‖z‖]
  nlinarith [norm_nonneg z]

/-- Uniform smallness of the regularizer, including at zeros. -/
theorem norm_Teps_le_sqrt (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖Teps ε z‖ ≤ Real.sqrt ε / 2 := by
  rw [teps_eq_tepsR ε hε, tepsR_norm ε hε]
  let r : ℝ := ‖z‖
  let s : ℝ := Real.sqrt ε
  let d : ℝ := r ^ 2 + ε
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hs0 : 0 ≤ s := by dsimp [s]; exact Real.sqrt_nonneg ε
  have hs2 : s ^ 2 = ε := by dsimp [s]; exact Real.sq_sqrt hε.le
  have hdpos : 0 < d := by dsimp [d, r]; positivity
  have hbasic : 2 * s * r ≤ d := by
    dsimp [d]
    nlinarith [sq_nonneg (r - s)]
  have hscaled := mul_le_mul_of_nonneg_left hbasic hs0
  change ε / d * r ≤ s / 2
  rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
  nlinarith

@[simp] theorem Teps_zero (ε : ℝ) : Teps ε 0 = 0 := by
  simp [Teps]

/-- Pointwise application of a Lipschitz map fixing zero preserves `L²`.
This is the low-order half of the critical Lipschitz-composition argument. -/
def lipschitzMapL2 (F : ℂ → ℂ) (L : NNReal) (hF : LipschitzWith L F)
    (hF0 : F 0 = 0) (f : FourierL2) : FourierL2 :=
  (show MemLp (fun x : ℝ => F ((f : ℝ → ℂ) x)) 2 volume from by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => F ((f : ℝ → ℂ) x)) volume :=
      hF.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
    exact ((Lp.memLp f).const_mul (L : ℝ)).mono hmeas (by
      filter_upwards with x
      have h := hF.norm_sub_le ((f : ℝ → ℂ) x) 0
      simpa [hF0] using h)).toLp
    (fun x : ℝ => F ((f : ℝ → ℂ) x))

lemma coe_lipschitzMapL2 (F : ℂ → ℂ) (L : NNReal)
    (hF : LipschitzWith L F) (hF0 : F 0 = 0) (f : FourierL2) :
    (lipschitzMapL2 F L hF hF0 f : ℝ → ℂ) =ᵐ[volume]
      fun x => F ((f : ℝ → ℂ) x) := by
  exact MemLp.coeFn_toLp _

/-- The Gagliardo energy obeys the elementary pointwise Lipschitz estimate.
No Fourier analysis is used in this step. -/
theorem gagliardoEnergy_lipschitzMapL2_le (F : ℂ → ℂ) (L : NNReal)
    (hF : LipschitzWith L F) (hF0 : F 0 = 0) (f : FourierL2) (s : ℝ) :
    gagliardoEnergy s (lipschitzMapL2 F L hF hF0 f) ≤
      (L : ℝ≥0∞) ^ (2 : ℕ) * gagliardoEnergy s f := by
  unfold gagliardoEnergy
  have hcoe := coe_lipschitzMapL2 F L hF hF0 f
  have hcoex : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      (lipschitzMapL2 F L hF hF0 f : ℝ → ℂ) p.1 =
        F ((f : ℝ → ℂ) p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hcoe
  have hcoey : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      (lipschitzMapL2 F L hF hF0 f : ℝ → ℂ) p.2 =
        F ((f : ℝ → ℂ) p.2) :=
    Measure.quasiMeasurePreserving_snd.ae hcoe
  calc
    (∫⁻ p : ℝ × ℝ,
        ‖(lipschitzMapL2 F L hF hF0 f : ℝ → ℂ) p.1 -
          (lipschitzMapL2 F L hF hF0 f : ℝ → ℂ) p.2‖₊ ^ (2 : ℕ) /
          ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s))) ≤
        ∫⁻ p : ℝ × ℝ,
          (L : ℝ≥0∞) ^ (2 : ℕ) *
            (‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖₊ ^ (2 : ℕ) /
              ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s))) := by
      apply lintegral_mono_ae
      filter_upwards [hcoex, hcoey] with p hx hy
      rw [hx, hy]
      have hlip := hF.norm_sub_le ((f : ℝ → ℂ) p.1) ((f : ℝ → ℂ) p.2)
      have hpow :
          (‖F ((f : ℝ → ℂ) p.1) - F ((f : ℝ → ℂ) p.2)‖₊ : ℝ≥0∞) ^
              (2 : ℕ) ≤
            (L : ℝ≥0∞) ^ (2 : ℕ) *
              (‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖₊ : ℝ≥0∞) ^
                (2 : ℕ) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast hlip) 2
      calc
        (↑‖F ((f : ℝ → ℂ) p.1) - F ((f : ℝ → ℂ) p.2)‖₊ : ℝ≥0∞) ^
              (2 : ℕ) /
            ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s)) ≤
            ((L : ℝ≥0∞) ^ (2 : ℕ) *
                (↑‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖₊ : ℝ≥0∞) ^
                  (2 : ℕ)) /
              ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s)) :=
          ENNReal.div_le_div hpow le_rfl
        _ = (L : ℝ≥0∞) ^ (2 : ℕ) *
              ((↑‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖₊ : ℝ≥0∞) ^
                  (2 : ℕ) /
                ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s))) := by
          rw [mul_div_assoc]
    _ = (L : ℝ≥0∞) ^ (2 : ℕ) *
        ∫⁻ p : ℝ × ℝ,
          ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖₊ ^ (2 : ℕ) /
            ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s)) := by
      rw [lintegral_const_mul' _ _ (by simp)]

private lemma coe_translateL2_critical (h : ℝ) (f : FourierL2) :
    (translateL2 h f : ℝ → ℂ) =ᵐ[volume]
      fun x => (f : ℝ → ℂ) (x + h) := by
  unfold translateL2
  exact MemLp.coeFn_toLp _

lemma enorm_translate_lipschitzMap_sub_le (F : ℂ → ℂ) (L : NNReal)
    (hF : LipschitzWith L F) (hF0 : F 0 = 0) (f : FourierL2) (h : ℝ) :
    ‖translateL2 h (lipschitzMapL2 F L hF hF0 f) -
        lipschitzMapL2 F L hF hF0 f‖ₑ ≤
      (L : ℝ≥0∞) * ‖translateL2 h f - f‖ₑ := by
  let Tf := lipschitzMapL2 F L hF hF0 f
  rw [Lp.enorm_def, Lp.enorm_def]
  have hTf := coe_lipschitzMapL2 F L hF hF0 f
  have hTfshift : ∀ᵐ x : ℝ ∂volume,
      (Tf : ℝ → ℂ) (x + h) = F ((f : ℝ → ℂ) (x + h)) := by
    change (fun x : ℝ => x + h) ⁻¹'
      {x | (Tf : ℝ → ℂ) x = F ((f : ℝ → ℂ) x)} ∈ ae volume
    exact (MeasureTheory.measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
      hTf
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      ‖((translateL2 h Tf - Tf : FourierL2) : ℝ → ℂ) x‖ ≤
        ‖(((L : ℂ) • (translateL2 h f - f) : FourierL2) : ℝ → ℂ) x‖ := by
    filter_upwards [coe_translateL2_critical h Tf, coe_translateL2_critical h f,
      Lp.coeFn_sub (translateL2 h Tf) Tf,
      Lp.coeFn_sub (translateL2 h f) f,
      Lp.coeFn_smul (L : ℂ) (translateL2 h f - f), hTf, hTfshift]
      with x htransTf htransf hsubTf hsubf hsmul hTfx hTfshiftx
    rw [hsubTf, hsmul]
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hsubf]
    simp only [Pi.sub_apply]
    rw [htransTf, htransf, hTfx, hTfshiftx]
    simpa [norm_smul, Complex.norm_real, NNReal.smul_def] using
      hF.norm_sub_le ((f : ℝ → ℂ) (x + h)) ((f : ℝ → ℂ) x)
  calc
    eLpNorm (((translateL2 h Tf - Tf : FourierL2) : ℝ → ℂ)) 2 volume ≤
        eLpNorm (((L : ℂ) • (translateL2 h f - f) : FourierL2) : ℝ → ℂ)
          2 volume := eLpNorm_mono_ae hpoint
    _ = ‖((L : ℂ) • (translateL2 h f - f) : FourierL2)‖ₑ := by
      rw [Lp.enorm_def]
    _ = (L : ℝ≥0∞) * ‖translateL2 h f - f‖ₑ := by
      rw [enorm_smul]
      congr 1
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      simp
    _ = (L : ℝ≥0∞) *
        eLpNorm (((translateL2 h f - f : FourierL2) : ℝ → ℂ)) 2 volume := by
      rw [Lp.enorm_def]

theorem translationEnergy_lipschitzMapL2_le (F : ℂ → ℂ) (L : NNReal)
    (hF : LipschitzWith L F) (hF0 : F 0 = 0) (f : FourierL2) :
    translationEnergy (lipschitzMapL2 F L hF hF0 f) ≤
      (L : ℝ≥0∞) ^ (2 : ℕ) * translationEnergy f := by
  unfold translationEnergy
  calc
    (∫⁻ h : ℝ, ‖translateL2 h (lipschitzMapL2 F L hF hF0 f) -
          lipschitzMapL2 F L hF hF0 f‖ₑ ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ))) ≤
      ∫⁻ h : ℝ, ((L : ℝ≥0∞) * ‖translateL2 h f - f‖ₑ) ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ)) := by
      apply lintegral_mono
      intro h
      exact ENNReal.div_le_div
        (pow_le_pow_left₀ (by positivity)
          (enorm_translate_lipschitzMap_sub_le F L hF hF0 f h) 2) le_rfl
    _ = (L : ℝ≥0∞) ^ (2 : ℕ) *
        ∫⁻ h : ℝ, ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)) := by
      rw [← lintegral_const_mul' _ _ (by simp)]
      apply lintegral_congr
      intro h
      rw [mul_pow, mul_div_assoc]

/-- Lipschitz maps fixing zero preserve the physical realization of
`H^{1/2}`.  This is the zero-safe critical composition theorem used below. -/
theorem lipschitz_composition_exists (F : ℂ → ℂ) (L : NNReal)
    (hF : LipschitzWith L F) (hF0 : F 0 = 0)
    (f : Hs (1 / 2 : ℝ)) :
    ∃ Ff : Hs (1 / 2 : ℝ),
      Hs.toL2 (by norm_num) Ff =
        lipschitzMapL2 F L hF hF0 (Hs.toL2 (by norm_num) f) := by
  let w : FourierL2 := Hs.toL2 (by norm_num) f
  let Fw : FourierL2 := lipschitzMapL2 F L hF hF0 w
  have hwE : homogeneousFourierEnergy (1 / 2 : ℝ) w < ⊤ :=
    homogeneousFourierEnergy_Hs_toL2_lt_top f
  have hwT : translationEnergy w < ⊤ := by
    rw [translationEnergy_eq_fourier]
    exact ENNReal.mul_lt_top halfKernelConstant_lt_top hwE
  have hFwT : translationEnergy Fw < ⊤ := by
    exact lt_of_le_of_lt
      (translationEnergy_lipschitzMapL2_le F L hF hF0 w)
      (ENNReal.mul_lt_top (by finiteness) hwT)
  have hprod : halfKernelConstant *
      homogeneousFourierEnergy (1 / 2 : ℝ) Fw < ⊤ := by
    rwa [← translationEnergy_eq_fourier]
  have hFwE : homogeneousFourierEnergy (1 / 2 : ℝ) Fw < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.mp hprod with h | h | h
    · exact h.2
    · exact (halfKernelConstant_pos.ne' h).elim
    · rw [h]
      exact ENNReal.zero_lt_top
  simpa [Fw, w] using
    exists_Hs_half_of_homogeneousFourierEnergy_lt_top Fw hFwE
end CubicNLSPhaseRetrieval
