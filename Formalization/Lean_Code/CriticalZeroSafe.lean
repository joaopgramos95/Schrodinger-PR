import Lean_Code.CriticalTepsLimit
import Lean_Code.SmoothCriticalCurrent

/-!
# The zero-safe critical Wronskian argument

This file contains the nonlinear algebra used at a good endpoint time slice.
The reciprocal is always paired with functions of the same modulus; no
division by the solution itself is used.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology ComplexConjugate

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- The reciprocal correction which vanishes at the origin. -/
def reciprocalCorrection (ε : ℝ) (z : ℂ) : ℂ :=
  ((1 / (‖z‖ ^ 2 + ε) - 1 / ε : ℝ) : ℂ)

@[simp] lemma reciprocalCorrection_zero (ε : ℝ) :
    reciprocalCorrection ε 0 = 0 := by
  simp [reciprocalCorrection]

private lemma reciprocalCorrection_differentiable (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (reciprocalCorrection ε) := by
  unfold reciprocalCorrection
  simp only [one_div]
  change Differentiable ℝ (fun z : ℂ =>
    Complex.ofReal ((‖z‖ ^ 2 + ε)⁻¹ - ε⁻¹))
  apply Complex.ofRealCLM.differentiable.comp
  intro z
  exact (((hasStrictFDerivAt_norm_sq z).differentiableAt.add_const ε).inv
      (by positivity)).sub_const ε⁻¹

private lemma reciprocalCorrection_fderiv_apply (ε : ℝ) (hε : 0 < ε)
    (z v : ℂ) :
    fderiv ℝ (reciprocalCorrection ε) z v =
      (((-2 / (‖z‖ ^ 2 + ε) ^ 2) * inner ℝ z v : ℝ) : ℂ) := by
  let d : ℝ := ‖z‖ ^ 2 + ε
  have hd : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2 + ε)
      (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).add_const ε |>.hasFDerivAt
  have hinv : HasFDerivAt (fun w : ℂ => (‖w‖ ^ 2 + ε)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(d ^ 2)⁻¹)).comp
        (2 • innerSL ℝ z)) z := by
    exact (hasFDerivAt_inv (by dsimp [d]; positivity : d ≠ 0)).comp z hd
  have hreal : HasFDerivAt
      (fun w : ℂ => 1 / (‖w‖ ^ 2 + ε) - 1 / ε)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(d ^ 2)⁻¹)).comp
        (2 • innerSL ℝ z)) z := by
    simpa only [one_div] using hinv.sub_const (1 / ε)
  have hout := Complex.ofRealCLM.hasFDerivAt.comp z hreal
  change fderiv ℝ
      (Complex.ofRealCLM ∘ fun w : ℂ =>
        1 / (‖w‖ ^ 2 + ε) - 1 / ε) z v = _
  rw [hout.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, Complex.ofRealCLM_apply]
  dsimp [d]
  push_cast
  field_simp
  ring

private lemma reciprocalCorrection_fderiv_norm_le (ε : ℝ) (hε : 0 < ε)
    (z : ℂ) :
    ‖fderiv ℝ (reciprocalCorrection ε) z‖ ≤
      1 / (ε * Real.sqrt ε) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [reciprocalCorrection_fderiv_apply ε hε]
  rw [Complex.norm_real, Real.norm_eq_abs]
  let r : ℝ := ‖z‖
  let s : ℝ := Real.sqrt ε
  let d : ℝ := r ^ 2 + ε
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = ε := by dsimp [s]; exact Real.sq_sqrt hε.le
  have hd : 0 < d := by dsimp [d, r]; positivity
  have hbasic : 2 * s * r ≤ d := by
    dsimp [d]
    nlinarith [sq_nonneg (r - s)]
  have hinner : |inner ℝ z v| ≤ r * ‖v‖ := by
    simpa [r] using abs_real_inner_le_norm z v
  have hcoef : 2 * r / d ^ 2 ≤ 1 / (ε * s) := by
    rw [div_le_iff₀ (sq_pos_of_pos hd), one_div, inv_mul_eq_div,
      le_div_iff₀ (mul_pos hε hs)]
    have hεd : ε ≤ d := by
      dsimp [d, r]
      nlinarith [sq_nonneg ‖z‖]
    have h₁ := mul_le_mul_of_nonneg_right hbasic hε.le
    have h₂ := mul_le_mul_of_nonneg_left hεd hd.le
    nlinarith
  calc
    |(-2 / (‖z‖ ^ 2 + ε) ^ 2) * inner ℝ z v| =
        (2 / d ^ 2) * |inner ℝ z v| := by
      rw [abs_mul, abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos (sq_pos_of_pos hd)]
    _ ≤ (2 / d ^ 2) * (r * ‖v‖) := by gcongr
    _ = (2 * r / d ^ 2) * ‖v‖ := by ring
    _ ≤ (1 / (ε * s)) * ‖v‖ := by gcongr
    _ = 1 / (ε * Real.sqrt ε) * ‖v‖ := by rfl

/-- The reciprocal correction is globally Lipschitz for positive ε. -/
theorem reciprocalCorrection_lipschitz (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨1 / (ε * Real.sqrt ε), by positivity⟩
      (reciprocalCorrection ε) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (reciprocalCorrection_differentiable ε hε)
  intro z
  exact_mod_cast reciprocalCorrection_fderiv_norm_le ε hε z

/-- Composition of the reciprocal correction with a critical function. -/
def reciprocalCorrectionHs (ε : ℝ) (hε : 0 < ε)
    (f : Hs (1 / 2 : ℝ)) : Hs (1 / 2 : ℝ) :=
  Classical.choose (lipschitz_composition_exists
    (reciprocalCorrection ε) ⟨1 / (ε * Real.sqrt ε), by positivity⟩
    (reciprocalCorrection_lipschitz ε hε) (reciprocalCorrection_zero ε) f)

lemma reciprocalCorrectionHs_toL2_ae (ε : ℝ) (hε : 0 < ε)
    (f : Hs (1 / 2 : ℝ)) :
    (Hs.toL2 (by norm_num) (reciprocalCorrectionHs ε hε f) : ℝ → ℂ) =ᵐ[volume]
      fun x => reciprocalCorrection ε
        ((Hs.toL2 (by norm_num) f : ℝ → ℂ) x) := by
  unfold reciprocalCorrectionHs
  rw [Classical.choose_spec (lipschitz_composition_exists
    (reciprocalCorrection ε) ⟨1 / (ε * Real.sqrt ε), by positivity⟩
    (reciprocalCorrection_lipschitz ε hε) (reciprocalCorrection_zero ε) f)]
  exact coe_lipschitzMapL2 _ _ _ _ _

/-- Addition in the bounded critical algebra. -/
def BoundedCritical.add (f g : BoundedCritical) : BoundedCritical := by
  refine ⟨f.val + g.val, ?_⟩
  have hcoe : (Hs.toL2 (by norm_num) (f.val + g.val) : ℝ → ℂ) =ᵐ[volume]
      fun x => (f.toL2 : ℝ → ℂ) x + (g.toL2 : ℝ → ℂ) x := by
    have hmap : Hs.toL2 (by norm_num) (f.val + g.val) = f.toL2 + g.toL2 := by
      simpa [BoundedCritical.toL2, hsHalfToL2CLM_apply] using
        map_add hsHalfToL2CLM f.val g.val
    rw [hmap]
    exact Lp.coeFn_add _ _
  rw [eLpNorm_congr_ae hcoe]
  exact (eLpNorm_add_le (Lp.aestronglyMeasurable f.toL2)
    (Lp.aestronglyMeasurable g.toL2) (by simp)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨f.bounded, g.bounded⟩)

lemma BoundedCritical.add_toL2_ae (f g : BoundedCritical) :
    (f.add g).toL2 =ᵐ[volume]
      fun x => (f.toL2 : ℝ → ℂ) x + (g.toL2 : ℝ → ℂ) x := by
  unfold BoundedCritical.add BoundedCritical.toL2
  dsimp only
  have hmap : Hs.toL2 (by norm_num) (f.val + g.val) =
      Hs.toL2 (by norm_num) f.val + Hs.toL2 (by norm_num) g.val := by
    simpa [hsHalfToL2CLM_apply] using map_add hsHalfToL2CLM f.val g.val
  rw [hmap]
  exact Lp.coeFn_add _ _

/-- Scalar multiplication in the bounded critical algebra. -/
def BoundedCritical.smul (c : ℂ) (f : BoundedCritical) : BoundedCritical := by
  refine ⟨c • f.val, ?_⟩
  have hmap : Hs.toL2 (by norm_num) (c • f.val) = c • f.toL2 := by
    unfold BoundedCritical.toL2
    rw [← hsHalfToL2CLM_apply, map_smul, hsHalfToL2CLM_apply]
  rw [hmap, eLpNorm_congr_ae (Lp.coeFn_smul c f.toL2),
    eLpNorm_const_smul]
  exact ENNReal.mul_lt_top (by finiteness) f.bounded

lemma BoundedCritical.smul_toL2_ae (c : ℂ) (f : BoundedCritical) :
    (f.smul c).toL2 =ᵐ[volume]
      fun x => c * (f.toL2 : ℝ → ℂ) x := by
  unfold BoundedCritical.smul BoundedCritical.toL2
  dsimp only
  have hmap : Hs.toL2 (by norm_num) (c • f.val) =
      c • Hs.toL2 (by norm_num) f.val := by
    rw [← hsHalfToL2CLM_apply, map_smul, hsHalfToL2CLM_apply]
  rw [hmap]
  exact (Lp.coeFn_smul c (Hs.toL2 (by norm_num) f.val)).mono fun x hx => by
    simpa [smul_eq_mul] using hx

/-- The reciprocal correction as a bounded critical element. -/
def BoundedCritical.reciprocalCorrection (ε : ℝ) (hε : 0 < ε)
    (f : BoundedCritical) : BoundedCritical := by
  refine ⟨reciprocalCorrectionHs ε hε f.val, ?_⟩
  have hcoe := reciprocalCorrectionHs_toL2_ae ε hε f.val
  rw [eLpNorm_congr_ae hcoe, eLpNorm_exponent_top]
  apply (eLpNormEssSup_le_of_ae_bound (C := 2 / ε) ?_).trans_lt
  · exact ENNReal.ofReal_lt_top
  · filter_upwards with x
    rw [CubicNLSPhaseRetrieval.reciprocalCorrection,
      Complex.norm_real, Real.norm_eq_abs]
    have hden : 0 < ‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + ε := by positivity
    have hdirect : 1 / (‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + ε) ≤ 1 / ε := by
      exact one_div_le_one_div_of_le hε (by nlinarith [sq_nonneg ‖(f.toL2 : ℝ → ℂ) x‖])
    have h₁ : |1 / (‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + ε)| ≤ 1 / ε := by
      rw [abs_of_pos (one_div_pos.mpr hden)]
      exact hdirect
    calc
      |1 / (‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + ε) - 1 / ε| ≤
          |1 / (‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + ε)| + |1 / ε| := abs_sub _ _
      _ ≤ 1 / ε + 1 / ε := by
        gcongr
        rw [abs_of_pos (one_div_pos.mpr hε)]
      _ = 2 / ε := by ring

lemma BoundedCritical.reciprocalCorrection_toL2_ae
    (ε : ℝ) (hε : 0 < ε) (f : BoundedCritical) :
    (f.reciprocalCorrection ε hε).toL2 =ᵐ[volume]
      fun x => CubicNLSPhaseRetrieval.reciprocalCorrection ε
        ((f.toL2 : ℝ → ℂ) x) :=
  reciprocalCorrectionHs_toL2_ae ε hε f.val

/-- The zero-safe radial remainder as a bounded critical element. -/
def BoundedCritical.teps (f : BoundedCritical) (n : ℕ) : BoundedCritical := by
  refine ⟨tepsHsSequence f.val n, ?_⟩
  have hcoe : (Hs.toL2 (by norm_num) (tepsHsSequence f.val n) : ℝ → ℂ) =ᵐ[volume]
      fun x => Teps (tepsSequence n) ((f.toL2 : ℝ → ℂ) x) := by
    rw [tepsHsSequence_toL2]
    exact coe_lipschitzMapL2 _ _ _ _ _
  rw [eLpNorm_congr_ae hcoe, eLpNorm_exponent_top]
  apply (eLpNormEssSup_le_of_ae_bound
    (C := Real.sqrt (tepsSequence n) / 2) ?_).trans_lt
  · exact ENNReal.ofReal_lt_top
  · filter_upwards with x
    exact norm_Teps_le_sqrt _ (tepsSequence_pos n) _

lemma BoundedCritical.teps_toL2_ae (f : BoundedCritical) (n : ℕ) :
    (f.teps n).toL2 =ᵐ[volume]
      fun x => Teps (tepsSequence n) ((f.toL2 : ℝ → ℂ) x) := by
  unfold BoundedCritical.teps BoundedCritical.toL2
  dsimp only
  rw [tepsHsSequence_toL2]
  exact coe_lipschitzMapL2 _ _ _ _ _

/-- The bounded multiplier `fg / (|f|² + ε)` used in the zero-safe test. -/
def BoundedCritical.zeroSafeMultiplier (f g : BoundedCritical) (n : ℕ) :
    BoundedCritical :=
  let ε := tepsSequence n
  let p := f.mul g
  (p.smul ((1 / ε : ℝ) : ℂ)).add
    (p.mul (f.reciprocalCorrection ε (tepsSequence_pos n)))

lemma BoundedCritical.zeroSafeMultiplier_toL2_ae
    (f g : BoundedCritical) (n : ℕ) :
    (f.zeroSafeMultiplier g n).toL2 =ᵐ[volume] fun x =>
      ((f.toL2 : ℝ → ℂ) x * (g.toL2 : ℝ → ℂ) x) /
        (((‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + tepsSequence n : ℝ) : ℂ)) := by
  let ε := tepsSequence n
  let p := f.mul g
  let r := f.reciprocalCorrection ε (tepsSequence_pos n)
  filter_upwards [BoundedCritical.add_toL2_ae
      (p.smul ((1 / ε : ℝ) : ℂ)) (p.mul r),
    BoundedCritical.smul_toL2_ae ((1 / ε : ℝ) : ℂ) p,
    BoundedCritical.mul_toL2_ae p r,
    BoundedCritical.mul_toL2_ae f g,
    BoundedCritical.reciprocalCorrection_toL2_ae ε
      (tepsSequence_pos n) f] with x hadd hsmul hpr hp hr
  rw [show (f.zeroSafeMultiplier g n).toL2 =
      ((p.smul ((1 / ε : ℝ) : ℂ)).add (p.mul r)).toL2 by rfl,
    hadd, hsmul, hpr, hp, hr]
  dsimp only [ε]
  rw [CubicNLSPhaseRetrieval.reciprocalCorrection]
  have hden : (‖(f.toL2 : ℝ → ℂ) x‖ ^ 2 + tepsSequence n : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (tepsSequence_pos n))
  push_cast
  field_simp
  ring

private lemma sub_Teps_eq_norm_sq_div (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    z - Teps ε z =
      (((‖z‖ ^ 2 / (‖z‖ ^ 2 + ε) : ℝ) : ℂ)) * z := by
  rw [Teps]
  have hden : (‖z‖ ^ 2 + ε : ℝ) ≠ 0 := by positivity
  have hcden : (((‖z‖ ^ 2 + ε : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hcoef : (1 : ℂ) - (ε : ℂ) /
        ((‖z‖ ^ 2 + ε : ℝ) : ℂ) =
      (‖z‖ ^ 2 : ℂ) / ((‖z‖ ^ 2 + ε : ℝ) : ℂ) := by
    field_simp [hcden]
    push_cast
    ring
  rw [show (ε : ℂ) * z / ((‖z‖ ^ 2 + ε : ℝ) : ℂ) =
      ((ε : ℂ) / ((‖z‖ ^ 2 + ε : ℝ) : ℂ)) * z by ring]
  rw [show (((‖z‖ ^ 2 / (‖z‖ ^ 2 + ε) : ℝ) : ℂ)) =
      (‖z‖ ^ 2 : ℂ) / ((‖z‖ ^ 2 + ε : ℝ) : ℂ) by push_cast; rfl]
  rw [← hcoef]
  ring

/-- Multiplying the zero-safe coefficient by `conj f` removes its
denominator, up to the small radial remainder. -/
lemma zeroSafeMultiplier_mul_conj_ae (f g : BoundedCritical) (n : ℕ)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖) :
    ∀ᵐ x : ℝ ∂volume,
      (f.zeroSafeMultiplier g n).toL2 x * f.conj.toL2 x =
        g.toL2 x - (g.teps n).toL2 x := by
  filter_upwards [hmod, BoundedCritical.zeroSafeMultiplier_toL2_ae f g n,
    BoundedCritical.conj_toL2_ae f,
    BoundedCritical.teps_toL2_ae g n] with x hm hh hc ht
  rw [hh, hc, ht, sub_Teps_eq_norm_sq_div _ (tepsSequence_pos n), ← hm]
  let a : ℂ := (f.toL2 : ℝ → ℂ) x
  let b : ℂ := (g.toL2 : ℝ → ℂ) x
  let d : ℂ := ((‖a‖ ^ 2 + tepsSequence n : ℝ) : ℂ)
  change a * b / d * (starRingEnd ℂ) a =
    (((‖a‖ ^ 2 / (‖a‖ ^ 2 + tepsSequence n) : ℝ) : ℂ)) * b
  rw [div_eq_mul_inv]
  calc
    a * b * d⁻¹ * (starRingEnd ℂ) a =
        ((starRingEnd ℂ) a * a) * b * d⁻¹ := by ring
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) * b * d⁻¹ := by
      rw [Complex.conj_mul', ← Complex.ofReal_pow]
    _ = (((‖a‖ ^ 2 / (‖a‖ ^ 2 + tepsSequence n) : ℝ) : ℂ)) * b := by
      dsimp [d]
      push_cast
      rw [div_eq_mul_inv]
      ring

lemma zeroSafeMultiplier_mul_conj_swap_ae (f g : BoundedCritical) (n : ℕ)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖) :
    ∀ᵐ x : ℝ ∂volume,
      (f.zeroSafeMultiplier g n).toL2 x * g.conj.toL2 x =
        f.toL2 x - (f.teps n).toL2 x := by
  filter_upwards [hmod, BoundedCritical.zeroSafeMultiplier_toL2_ae f g n,
    BoundedCritical.conj_toL2_ae g,
    BoundedCritical.teps_toL2_ae f n] with x hm hh hc ht
  rw [hh, hc, ht, sub_Teps_eq_norm_sq_div _ (tepsSequence_pos n)]
  let a : ℂ := (f.toL2 : ℝ → ℂ) x
  let b : ℂ := (g.toL2 : ℝ → ℂ) x
  let d : ℂ := ((‖a‖ ^ 2 + tepsSequence n : ℝ) : ℂ)
  change a * b / d * (starRingEnd ℂ) b =
    (((‖a‖ ^ 2 / (‖a‖ ^ 2 + tepsSequence n) : ℝ) : ℂ)) * a
  rw [div_eq_mul_inv]
  calc
    a * b * d⁻¹ * (starRingEnd ℂ) b =
        (b * (starRingEnd ℂ) b) * a * d⁻¹ := by ring
    _ = ((‖b‖ ^ 2 : ℝ) : ℂ) * a * d⁻¹ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) * a * d⁻¹ := by rw [hm]
    _ = (((‖a‖ ^ 2 / (‖a‖ ^ 2 + tepsSequence n) : ℝ) : ℂ)) * a := by
      dsimp [d]
      push_cast
      rw [div_eq_mul_inv]
      ring

/-- Current tested by a bounded critical coefficient. -/
def boundedQuadraticCurrentAgainst (f a : BoundedCritical) : ℂ :=
  criticalPairingCLM (criticalDerivative f.val) (a.mul f.conj).val

/-- Wronskian tested by a bounded critical coefficient. -/
def boundedWronskianAgainst (f g a : BoundedCritical) : ℂ :=
  criticalPairingCLM (criticalDerivative f.val) (a.mul g).val -
    criticalPairingCLM (criticalDerivative g.val) (a.mul f).val

private lemma boundedCritical_val_eq_of_toL2_ae (f g : BoundedCritical)
    (h : (f.toL2 : ℝ → ℂ) =ᵐ[volume] (g.toL2 : ℝ → ℂ)) :
    f.val = g.val := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  exact h

private lemma Hs_toL2_sub_ae (f g : Hs (1 / 2 : ℝ)) :
    (Hs.toL2 (by norm_num) (f - g) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Hs.toL2 (by norm_num) f : ℝ → ℂ) x -
        (Hs.toL2 (by norm_num) g : ℝ → ℂ) x := by
  have hmap : Hs.toL2 (by norm_num) (f - g) =
      Hs.toL2 (by norm_num) f - Hs.toL2 (by norm_num) g := by
    rw [← hsHalfToL2CLM_apply, map_sub, hsHalfToL2CLM_apply,
      hsHalfToL2CLM_apply]
  rw [hmap]
  exact (Lp.coeFn_sub _ _).mono fun x hx => by simpa using hx

private lemma zeroSafe_left_test_val (f g : BoundedCritical)
    (φ : SchwartzMap ℝ ℂ) (n : ℕ)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖) :
    (((schwartzBoundedCritical φ).mul
        (f.zeroSafeMultiplier g n)).mul f.conj).val =
      schwartzHsMultiplier φ (g.val - (g.teps n).val) := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  filter_upwards [BoundedCritical.mul_toL2_ae
      ((schwartzBoundedCritical φ).mul (f.zeroSafeMultiplier g n)) f.conj,
    BoundedCritical.mul_toL2_ae (schwartzBoundedCritical φ)
      (f.zeroSafeMultiplier g n),
    schwartzBoundedCritical_toL2_ae φ,
    zeroSafeMultiplier_mul_conj_ae f g n hmod,
    Hs_toL2_sub_ae g.val (g.teps n).val,
    schwartzHsMultiplier_toL2_ae φ (g.val - (g.teps n).val)]
      with x hout ha hφ hzero hsub htarget
  change (((((schwartzBoundedCritical φ).mul
      (f.zeroSafeMultiplier g n)).mul f.conj).toL2 : ℝ → ℂ) x) =
    (Hs.toL2 (by norm_num)
      (schwartzHsMultiplier φ (g.val - (g.teps n).val)) : ℝ → ℂ) x
  rw [hout, ha, hφ, htarget, hsub]
  change φ x * (f.zeroSafeMultiplier g n).toL2 x * f.conj.toL2 x =
    (g.toL2 x - (g.teps n).toL2 x) * φ x
  calc
    φ x * (f.zeroSafeMultiplier g n).toL2 x * f.conj.toL2 x =
        φ x * ((f.zeroSafeMultiplier g n).toL2 x * f.conj.toL2 x) := by ring
    _ = φ x * (g.toL2 x - (g.teps n).toL2 x) := by rw [hzero]
    _ = (g.toL2 x - (g.teps n).toL2 x) * φ x := by ring

private lemma zeroSafe_right_test_val (f g : BoundedCritical)
    (φ : SchwartzMap ℝ ℂ) (n : ℕ)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖) :
    (((schwartzBoundedCritical φ).mul
        (f.zeroSafeMultiplier g n)).mul g.conj).val =
      schwartzHsMultiplier φ (f.val - (f.teps n).val) := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  filter_upwards [BoundedCritical.mul_toL2_ae
      ((schwartzBoundedCritical φ).mul (f.zeroSafeMultiplier g n)) g.conj,
    BoundedCritical.mul_toL2_ae (schwartzBoundedCritical φ)
      (f.zeroSafeMultiplier g n),
    schwartzBoundedCritical_toL2_ae φ,
    zeroSafeMultiplier_mul_conj_swap_ae f g n hmod,
    Hs_toL2_sub_ae f.val (f.teps n).val,
    schwartzHsMultiplier_toL2_ae φ (f.val - (f.teps n).val)]
      with x hout ha hφ hzero hsub htarget
  change (((((schwartzBoundedCritical φ).mul
      (f.zeroSafeMultiplier g n)).mul g.conj).toL2 : ℝ → ℂ) x) =
    (Hs.toL2 (by norm_num)
      (schwartzHsMultiplier φ (f.val - (f.teps n).val)) : ℝ → ℂ) x
  rw [hout, ha, hφ, htarget, hsub]
  change φ x * (f.zeroSafeMultiplier g n).toL2 x * g.conj.toL2 x =
    (f.toL2 x - (f.teps n).toL2 x) * φ x
  calc
    φ x * (f.zeroSafeMultiplier g n).toL2 x * g.conj.toL2 x =
        φ x * ((f.zeroSafeMultiplier g n).toL2 x * g.conj.toL2 x) := by ring
    _ = φ x * (f.toL2 x - (f.teps n).toL2 x) := by rw [hzero]
    _ = (f.toL2 x - (f.teps n).toL2 x) * φ x := by ring

/-- Zero-safe Wronskian theorem using only the specific reciprocal tests
which occur in its proof. -/
theorem boundedWronskian_zero_of_zeroSafe_current_eq
    (f g : BoundedCritical)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖)
    (φ : SchwartzMap ℝ ℂ)
    (hcurrent : ∀ n : ℕ,
      boundedQuadraticCurrentAgainst f
          ((schwartzBoundedCritical φ).mul (f.zeroSafeMultiplier g n)) =
        boundedQuadraticCurrentAgainst g
          ((schwartzBoundedCritical φ).mul (f.zeroSafeMultiplier g n))) :
    criticalWronskianCurrent f.val g.val φ = 0 := by
  have hidentity (n : ℕ) :
      criticalWronskianCurrent f.val g.val φ =
        criticalPairingCLM (criticalDerivative f.val)
            (schwartzHsMultiplier φ (g.teps n).val) -
          criticalPairingCLM (criticalDerivative g.val)
            (schwartzHsMultiplier φ (f.teps n).val) := by
    have hc := hcurrent n
    unfold boundedQuadraticCurrentAgainst at hc
    rw [
      zeroSafe_left_test_val f g φ n hmod,
      zeroSafe_right_test_val f g φ n hmod] at hc
    have hmg : schwartzHsMultiplier φ (g.val - (g.teps n).val) =
        schwartzHsMultiplier φ g.val -
          schwartzHsMultiplier φ (g.teps n).val := map_sub _ _ _
    have hmf : schwartzHsMultiplier φ (f.val - (f.teps n).val) =
        schwartzHsMultiplier φ f.val -
          schwartzHsMultiplier φ (f.teps n).val := map_sub _ _ _
    rw [hmg, hmf, map_sub, map_sub] at hc
    unfold criticalWronskianCurrent
    linear_combination hc
  have htg : Tendsto (fun n =>
      criticalPairingCLM (criticalDerivative f.val)
        (schwartzHsMultiplier φ (g.teps n).val)) atTop (𝓝 0) := by
    have hteps : Tendsto (fun n => (g.teps n).val) atTop (𝓝 0) := by
      simpa [BoundedCritical.teps] using tepsHsSequence_tendsto_zero g.val
    have hm := (schwartzHsMultiplier φ).continuous.continuousAt.tendsto.comp hteps
    have hp := (criticalPairingCLM (criticalDerivative f.val)).continuous.continuousAt.tendsto.comp hm
    have hz : schwartzHsMultiplier φ (0 : Hs (1 / 2 : ℝ)) = 0 := map_zero _
    rw [hz, map_zero] at hp
    change Tendsto (fun n =>
      criticalPairingCLM (criticalDerivative f.val)
        (schwartzHsMultiplier φ (g.teps n).val)) atTop (𝓝 0) at hp
    exact hp
  have htf : Tendsto (fun n =>
      criticalPairingCLM (criticalDerivative g.val)
        (schwartzHsMultiplier φ (f.teps n).val)) atTop (𝓝 0) := by
    have hteps : Tendsto (fun n => (f.teps n).val) atTop (𝓝 0) := by
      simpa [BoundedCritical.teps] using tepsHsSequence_tendsto_zero f.val
    have hm := (schwartzHsMultiplier φ).continuous.continuousAt.tendsto.comp hteps
    have hp := (criticalPairingCLM (criticalDerivative g.val)).continuous.continuousAt.tendsto.comp hm
    have hz : schwartzHsMultiplier φ (0 : Hs (1 / 2 : ℝ)) = 0 := map_zero _
    rw [hz, map_zero] at hp
    change Tendsto (fun n =>
      criticalPairingCLM (criticalDerivative g.val)
        (schwartzHsMultiplier φ (f.teps n).val)) atTop (𝓝 0) at hp
    exact hp
  have hrhs := htg.sub htf
  have hlhs : Tendsto (fun _ : ℕ => criticalWronskianCurrent f.val g.val φ)
      atTop (𝓝 (criticalWronskianCurrent f.val g.val φ)) := tendsto_const_nhds
  have heq : (fun _ : ℕ => criticalWronskianCurrent f.val g.val φ) =
      fun n => criticalPairingCLM (criticalDerivative f.val)
            (schwartzHsMultiplier φ (g.teps n).val) -
          criticalPairingCLM (criticalDerivative g.val)
            (schwartzHsMultiplier φ (f.teps n).val) := by
    funext n
    exact hidentity n
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs (by simpa using hrhs)

/-- Zero-safe Wronskian theorem.  Equality of modulus and equality of the
quadratic current as a functional on the bounded critical algebra imply the
holomorphic Wronskian identity against every Schwartz test. -/
theorem boundedWronskian_zero_of_current_eq
    (f g : BoundedCritical)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖)
    (hcurrent : ∀ a : BoundedCritical,
      boundedQuadraticCurrentAgainst f a =
        boundedQuadraticCurrentAgainst g a)
    (φ : SchwartzMap ℝ ℂ) :
    criticalWronskianCurrent f.val g.val φ = 0 :=
  boundedWronskian_zero_of_zeroSafe_current_eq f g hmod φ
    (fun n => hcurrent ((schwartzBoundedCritical φ).mul
      (f.zeroSafeMultiplier g n)))



end CubicNLSPhaseRetrieval
