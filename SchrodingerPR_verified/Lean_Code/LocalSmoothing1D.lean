import Lean_Code.FourierSobolev
import Lean_Code.FreeSchrodinger
import Lean_Code.Strichartz1D
import Lean_Code.EndpointRegularity
import Lean_Code.JointL2Representative
import Lean_Code.L1L2FourierBridge

/-!
# Local smoothing by one half derivative

Blueprint chapter: `chap:smoothing` (module 7).
Imports: modules 1, 2, 4, and 6.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Frequency-side object whose inverse time Fourier transform is the pointwise smoothing trace. -/
def smoothingB (x : ℝ) (f : L2) (freq : ℝ) : ℂ :=
  if h : 0 < freq then
    ((freq ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
          (fourierL2 f : ℝ → ℂ) (Real.sqrt freq) +
        Complex.exp (-Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
          (fourierL2 f : ℝ → ℂ) (-Real.sqrt freq))
  else 0

private lemma sq_image_Ioi : (fun x : ℝ => x ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sq_pos_of_pos (show 0 < x from hx)
  · intro hy
    refine ⟨Real.sqrt y, Real.sqrt_pos.2 hy, ?_⟩
    exact Real.sq_sqrt hy.le

private lemma qmp_sqrt_Ioi :
    Measure.QuasiMeasurePreserving Real.sqrt (volume.restrict (Set.Ioi 0)) volume := by
  refine ⟨Real.continuous_sqrt.measurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hnull
  rw [Measure.map_apply_of_aemeasurable Real.continuous_sqrt.aemeasurable hs,
    Measure.restrict_apply (hs.preimage Real.continuous_sqrt.measurable)]
  let u : ℝ → ℝ≥0∞ := (Real.sqrt ⁻¹' s).indicator 1
  have hchange := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Set.Ioi (0 : ℝ)) (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x)
    measurableSet_Ioi
    (fun x _ => by simpa [pow_two] using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
        (add_nonneg (show 0 ≤ x from hx.le) (show 0 ≤ y from hy.le))]) u
  rw [sq_image_Ioi] at hchange
  have hs_ae : ∀ᵐ x : ℝ ∂volume, x ∉ s := by
    rw [ae_iff]
    simpa using hnull
  have hright :
      (∫⁻ x : ℝ in Set.Ioi 0, ENNReal.ofReal (2 * x) * u (x ^ 2)) = 0 := by
    rw [← lintegral_zero]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hs_ae]
      with x hx hxs
    simp [u, Real.sqrt_sq_eq_abs, abs_of_pos (show 0 < x from hx), hxs]
  have hleft : (∫⁻ y : ℝ in Set.Ioi 0, u y) = 0 := hchange.trans hright
  rw [show u = (Real.sqrt ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) by rfl,
    setLIntegral_indicator (hs.preimage Real.continuous_sqrt.measurable),
    setLIntegral_one] at hleft
  simpa [Set.inter_comm] using hleft

private def smoothingBRaw (x : ℝ) (f : L2) (freq : ℝ) : ℂ :=
  ((freq ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
    (Complex.exp (Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
        (fourierL2 f : ℝ → ℂ) (Real.sqrt freq) +
      Complex.exp (-Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
        (fourierL2 f : ℝ → ℂ) (-Real.sqrt freq))

private lemma smoothingB_eq_indicator (x : ℝ) (f : L2) :
    smoothingB x f = (Set.Ioi (0 : ℝ)).indicator (smoothingBRaw x f) := by
  funext freq
  simp only [smoothingB, smoothingBRaw, Set.indicator, Set.mem_Ioi]
  split_ifs <;> rfl

private lemma smoothingB_aestronglyMeasurable (x : ℝ) (f : L2) :
    AEStronglyMeasurable (smoothingB x f) volume := by
  rw [smoothingB_eq_indicator, aestronglyMeasurable_indicator_iff measurableSet_Ioi]
  let g : L2 := fourierL2 f
  have hgp : AEStronglyMeasurable (fun w : ℝ => (g : ℝ → ℂ) (Real.sqrt w))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [Function.comp_def] using
      (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving qmp_sqrt_Ioi
  have hqneg : Measure.QuasiMeasurePreserving (fun w : ℝ => -Real.sqrt w)
      (volume.restrict (Set.Ioi 0)) volume := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp qmp_sqrt_Ioi
  have hgn : AEStronglyMeasurable (fun w : ℝ => (g : ℝ → ℂ) (-Real.sqrt w))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [Function.comp_def] using
      (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving hqneg
  have hweight : AEStronglyMeasurable
      (fun w : ℝ => ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable
    exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const (fun w hw => Or.inl (ne_of_gt hw)))
    exact measurableSet_Ioi
  change AEStronglyMeasurable
    (fun freq => ((freq ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
          (g : ℝ → ℂ) (Real.sqrt freq) +
        Complex.exp (-Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
          (g : ℝ → ℂ) (-Real.sqrt freq)))
      (volume.restrict (Set.Ioi 0))
  exact hweight.mul
    (((by fun_prop : Continuous fun freq : ℝ =>
      Complex.exp (Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ))).aestronglyMeasurable.mul hgp).add
    ((by fun_prop : Continuous fun freq : ℝ =>
      Complex.exp (-Complex.I * ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ))).aestronglyMeasurable.mul hgn))

private lemma norm_smoothingBRaw_sq_le (x : ℝ) (f : L2) (w : ℝ) (hw : 0 < w) :
    ‖smoothingBRaw x f w‖ ^ 2 ≤
      2 * w ^ (-(1 / 2 : ℝ)) *
        (‖(fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖ ^ 2 +
          ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ ^ 2) := by
  let a : ℂ := Complex.exp
    (Complex.I * ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))
  let b : ℂ := Complex.exp
    (-Complex.I * ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))
  let A : ℝ := ‖(fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖
  let B : ℝ := ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖
  have ha : ‖a‖ = 1 := by
    dsimp [a]
    simp [Complex.norm_exp, Complex.mul_re]
  have hb : ‖b‖ = 1 := by
    dsimp [b]
    simp [Complex.norm_exp, Complex.mul_re]
  have hab : ‖a * (fourierL2 f : ℝ → ℂ) (Real.sqrt w) +
      b * (fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ ≤ A + B := by
    calc
      _ ≤ ‖a * (fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖ +
          ‖b * (fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ := norm_add_le _ _
      _ = A + B := by simp [ha, hb, A, B]
  have hsquare : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
    nlinarith [sq_nonneg (A - B)]
  have hweight : (w ^ (-(1 / 4 : ℝ))) ^ 2 = w ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num
  rw [smoothingBRaw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hw.le _), mul_pow, hweight]
  change w ^ (-(1 / 2 : ℝ)) *
      ‖a * (fourierL2 f : ℝ → ℂ) (Real.sqrt w) +
        b * (fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ ^ 2 ≤ _
  calc
    _ ≤ w ^ (-(1 / 2 : ℝ)) * (A + B) ^ 2 := by gcongr
    _ ≤ w ^ (-(1 / 2 : ℝ)) * (2 * (A ^ 2 + B ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hw.le _)
    _ = _ := by simp [A, B]; ring

private lemma enorm_smoothingB_sq_le (x : ℝ) (f : L2) (w : ℝ) (hw : 0 < w) :
    ‖smoothingB x f w‖ₑ ^ (2 : ℝ) ≤
      2 * ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
        (‖(fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ) +
          ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ₑ ^ (2 : ℝ)) := by
  have h := ENNReal.ofReal_le_ofReal (norm_smoothingBRaw_sq_le x f w hw)
  have hs : smoothingB x f w = smoothingBRaw x f w := by
    rw [smoothingB, dif_pos hw, smoothingBRaw]
  rw [hs]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)] at h
  norm_num at h ⊢
  simpa [← ofReal_norm] using h

private lemma weighted_sqrt_lintegral (g : ℝ → ℂ) :
    (∫⁻ w : ℝ in Ioi 0,
        ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) * ‖g (Real.sqrt w)‖ₑ ^ (2 : ℝ)) =
      2 * ∫⁻ y : ℝ in Ioi 0, ‖g y‖ₑ ^ (2 : ℝ) := by
  let u : ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) * ‖g (Real.sqrt w)‖ₑ ^ (2 : ℝ)
  have hchange := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Ioi (0 : ℝ)) (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x)
    measurableSet_Ioi
    (fun x _ => by simpa [pow_two] using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
        (add_nonneg (show 0 ≤ x from hx.le) (show 0 ≤ y from hy.le))]) u
  rw [sq_image_Ioi] at hchange
  rw [show (∫⁻ w : ℝ in Ioi 0,
      ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) * ‖g (Real.sqrt w)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ w : ℝ in Ioi 0, u w by rfl, hchange]
  rw [← lintegral_const_mul' 2 _ (by norm_num)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have hsqrt : Real.sqrt (x ^ 2) = x := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hx0]
  have hweight : (x ^ 2) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
    exact Real.rpow_neg_one x
  simp only [u, hsqrt, hweight]
  rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) by positivity)]
  rw [ENNReal.ofReal_ofNat]
  have hxne : ENNReal.ofReal x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hx0
  rw [ENNReal.ofReal_inv_of_pos hx0]
  calc
    2 * ENNReal.ofReal x * ((ENNReal.ofReal x)⁻¹ * ‖g x‖ₑ ^ (2 : ℝ)) =
        2 * (ENNReal.ofReal x * (ENNReal.ofReal x)⁻¹) * ‖g x‖ₑ ^ (2 : ℝ) := by
      ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hxne ENNReal.ofReal_ne_top]; simp

private lemma weighted_sqrt_aemeasurable (g : L2) :
    AEMeasurable (fun w : ℝ =>
      ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
        ‖(g : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioi 0)) := by
  have hgp : AEStronglyMeasurable (fun w : ℝ => (g : ℝ → ℂ) (Real.sqrt w))
      (volume.restrict (Ioi 0)) := by
    simpa [Function.comp_def] using
      (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving qmp_sqrt_Ioi
  have hweight : AEStronglyMeasurable
      (fun w : ℝ => ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))))
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const (fun w hw => Or.inl (ne_of_gt hw)))
    exact measurableSet_Ioi
  have hpow : AEMeasurable (fun w : ℝ =>
      ‖(g : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioi 0)) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hgp.enorm
  exact hweight.aemeasurable.mul hpow

private lemma lintegral_enorm_neg (g : ℝ → ℂ) :
    (∫⁻ y : ℝ, ‖g (-y)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ y : ℝ, ‖g y‖ₑ ^ (2 : ℝ) := by
  simpa using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun y : ℝ => ‖g y‖ₑ ^ (2 : ℝ))

private lemma lintegral_smoothingB_sq_le_energy (x : ℝ) (f : L2) :
    (∫⁻ w : ℝ, ‖smoothingB x f w‖ₑ ^ (2 : ℝ)) ≤
      8 * ∫⁻ y : ℝ, ‖(fourierL2 f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) := by
  let g : L2 := fourierL2 f
  let P : ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
      ‖(g : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ)
  let N : ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
      ‖(g : ℝ → ℂ) (-Real.sqrt w)‖ₑ ^ (2 : ℝ)
  have hpoint : ∀ w : ℝ,
      ‖smoothingB x f w‖ₑ ^ (2 : ℝ) ≤
        (Ioi (0 : ℝ)).indicator (fun w => 2 * P w + 2 * N w) w := by
    intro w
    by_cases hw : 0 < w
    · rw [show (Ioi (0 : ℝ)).indicator (fun w => 2 * P w + 2 * N w) w =
          2 * P w + 2 * N w by simp [Set.indicator, hw]]
      calc
        _ ≤ 2 * ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
            (‖(fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ) +
              ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ₑ ^ (2 : ℝ)) :=
          enorm_smoothingB_sq_le x f w hw
        _ = 2 * P w + 2 * N w := by simp only [P, N, g]; ring
    · simp [Set.indicator, smoothingB, hw]
  calc
    (∫⁻ w : ℝ, ‖smoothingB x f w‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ w : ℝ, (Ioi (0 : ℝ)).indicator (fun w => 2 * P w + 2 * N w) w :=
      lintegral_mono hpoint
    _ = ∫⁻ w : ℝ in Ioi 0, (2 * P w + 2 * N w) := by
      rw [lintegral_indicator measurableSet_Ioi]
    _ = (∫⁻ w : ℝ in Ioi 0, 2 * P w) +
        ∫⁻ w : ℝ in Ioi 0, 2 * N w := by
      rw [lintegral_add_left']
      exact measurable_const.aemeasurable.mul (weighted_sqrt_aemeasurable g)
    _ = 2 * (∫⁻ w : ℝ in Ioi 0, P w) +
        2 * ∫⁻ w : ℝ in Ioi 0, N w := by
      rw [lintegral_const_mul' 2 _ (by norm_num),
        lintegral_const_mul' 2 _ (by norm_num)]
    _ = 2 * (2 * ∫⁻ y : ℝ in Ioi 0, ‖(g : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)) +
        2 * (2 * ∫⁻ y : ℝ in Ioi 0, ‖(g : ℝ → ℂ) (-y)‖ₑ ^ (2 : ℝ)) := by
      rw [show (∫⁻ w : ℝ in Ioi 0, P w) =
          2 * ∫⁻ y : ℝ in Ioi 0, ‖(g : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) by
        simpa [P] using weighted_sqrt_lintegral (g : ℝ → ℂ)]
      rw [show (∫⁻ w : ℝ in Ioi 0, N w) =
          2 * ∫⁻ y : ℝ in Ioi 0, ‖(g : ℝ → ℂ) (-y)‖ₑ ^ (2 : ℝ) by
        simpa [N] using weighted_sqrt_lintegral (fun y => (g : ℝ → ℂ) (-y))]
    _ ≤ 2 * (2 * ∫⁻ y : ℝ, ‖(g : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)) +
        2 * (2 * ∫⁻ y : ℝ, ‖(g : ℝ → ℂ) (-y)‖ₑ ^ (2 : ℝ)) := by
      exact add_le_add
        (mul_le_mul_left' (mul_le_mul_left'
          (setLIntegral_le_lintegral (Ioi 0)
            (fun y : ℝ => ‖(g : ℝ → ℂ) y‖ₑ ^ (2 : ℝ))) 2) 2)
        (mul_le_mul_left' (mul_le_mul_left'
          (setLIntegral_le_lintegral (Ioi 0)
            (fun y : ℝ => ‖(g : ℝ → ℂ) (-y)‖ₑ ^ (2 : ℝ))) 2) 2)
    _ = 8 * ∫⁻ y : ℝ, ‖(fourierL2 f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) := by
      rw [lintegral_enorm_neg]
      simp [g]
      ring

private lemma fourierL2_energy (f : L2) :
    (∫⁻ y : ℝ, ‖(fourierL2 f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  let g : L2 := fourierL2 f
  calc
    (∫⁻ y : ℝ, ‖(fourierL2 f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)) =
        eLpNorm (g : ℝ → ℂ) 2 volume ^ (2 : ℝ) := by
      symm
      simpa [g] using (eLpNorm_nnreal_pow_eq_lintegral (f := (g : ℝ → ℂ))
        (p := (2 : NNReal)) (show (2 : NNReal) ≠ 0 by norm_num))
    _ = ‖g‖ₑ ^ (2 : ℕ) := by rw [← Lp.enorm_def]; norm_num
    _ = ENNReal.ofReal (‖g‖ ^ 2) := by
      rw [← ofReal_norm]
      norm_num
    _ = ENNReal.ofReal (‖f‖ ^ 2) := by rw [LinearIsometryEquiv.norm_map]

private lemma eLpNorm_smoothingB_le (x : ℝ) (f : L2) :
    eLpNorm (smoothingB x f) 2 volume ≤
      (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal ‖f‖ := by
  have hsquare :
      (∫⁻ w : ℝ, ‖smoothingB x f w‖ₑ ^ (2 : ℝ)) ≤
        8 * ENNReal.ofReal (‖f‖ ^ 2) := by
    calc
      _ ≤ 8 * ∫⁻ y : ℝ, ‖(fourierL2 f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) :=
        lintegral_smoothingB_sq_le_energy x f
      _ = _ := by rw [fourierL2_energy]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num only [ENNReal.toReal_ofNat]
  calc
    (∫⁻ w : ℝ, ‖smoothingB x f w‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (8 * ENNReal.ofReal (‖f‖ ^ 2)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hsquare (by positivity)
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (‖f‖ ^ 2)) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal ‖f‖ := by
      congr 1
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
      rw [← ENNReal.rpow_natCast]
      rw [← ENNReal.rpow_mul]
      norm_num

private lemma smoothingB_memLp (x : ℝ) (f : L2) :
    MemLp (smoothingB x f) 2 volume := by
  refine ⟨smoothingB_aestronglyMeasurable x f, ?_⟩
  exact lt_of_le_of_lt (eLpNorm_smoothingB_le x f) (by finiteness)

/-- `lem:homogeneous-smoothing-identity`: frequency representation and uniform L² bound. -/
theorem homogeneous_smoothing_identity (f : L2) (x : ℝ) :
  MemLp (smoothingB x f) 2 volume ∧
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      eLpNorm (smoothingB x f) 2 volume ≤ C * ENNReal.ofReal ‖f‖ := by
  exact ⟨smoothingB_memLp x f,
    ⟨(8 : ℝ≥0∞) ^ (1 / 2 : ℝ), by finiteness, eLpNorm_smoothingB_le x f⟩⟩

/-- `def:Ax-representative`: canonical inverse time Fourier representative. -/
def AxRepresentative (x : ℝ) (f : L2) : Lp ℂ 2 (volume : Measure ℝ) :=
  (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
    ((homogeneous_smoothing_identity f x).1.toLp (smoothingB x f))

/-- `lem:point-smoothing`: uniform pointwise-in-space half-derivative bound. -/
theorem point_smoothing :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : L2, ∀ x : ℝ,
    ENNReal.ofReal ‖AxRepresentative x f‖ ≤ C * ENNReal.ofReal ‖f‖ := by
  refine ⟨(8 : ℝ≥0∞) ^ (1 / 2 : ℝ), by finiteness, fun f x => ?_⟩
  rw [ofReal_norm, AxRepresentative, LinearIsometryEquiv.enorm_map,
    Lp.enorm_toLp (homogeneous_smoothing_identity f x).1]
  exact eLpNorm_smoothingB_le x f

/-! The frequency formula also varies continuously with the observation
point.  Keeping the two square-root branches separate avoids any appeal to
pointwise representatives of the inverse Fourier transform. -/

private def smoothingBPlus (x : ℝ) (f : L2) (freq : ℝ) : ℂ :=
  if 0 < freq then
    ((freq ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I *
        ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
          (fourierL2 f : ℝ → ℂ) (Real.sqrt freq))
  else 0

private def smoothingBMinus (x : ℝ) (f : L2) (freq : ℝ) : ℂ :=
  if 0 < freq then
    ((freq ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      (Complex.exp (-Complex.I *
        ((2 * Real.pi * x * Real.sqrt freq : ℝ) : ℂ)) *
          (fourierL2 f : ℝ → ℂ) (-Real.sqrt freq))
  else 0

private lemma smoothingB_eq_plus_add_minus (x : ℝ) (f : L2) :
    smoothingB x f = fun w => smoothingBPlus x f w + smoothingBMinus x f w := by
  funext w
  unfold smoothingB smoothingBPlus smoothingBMinus
  split_ifs <;> ring

private lemma smoothingBPlus_aestronglyMeasurable (x : ℝ) (f : L2) :
    AEStronglyMeasurable (smoothingBPlus x f) volume := by
  let g : L2 := fourierL2 f
  have hcomp : AEStronglyMeasurable
      (fun w : ℝ => (g : ℝ → ℂ) (Real.sqrt w))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [Function.comp_def] using
      (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving qmp_sqrt_Ioi
  have hraw : AEStronglyMeasurable (fun w : ℝ =>
      ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (Complex.I *
          ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ)) *
            (g : ℝ → ℂ) (Real.sqrt w)))
      (volume.restrict (Set.Ioi 0)) := by
    have hw : AEStronglyMeasurable
        (fun w : ℝ => ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))
        (volume.restrict (Set.Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_id.rpow_const (fun w hw => Or.inl (ne_of_gt hw)))
      exact measurableSet_Ioi
    exact hw.mul ((by fun_prop : Continuous fun w : ℝ =>
      Complex.exp (Complex.I *
        ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))).aestronglyMeasurable.mul hcomp)
  rw [show smoothingBPlus x f = (Set.Ioi (0 : ℝ)).indicator (fun w =>
      ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (Complex.I *
          ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ)) *
            (g : ℝ → ℂ) (Real.sqrt w))) by
    funext w
    simp only [smoothingBPlus, Set.indicator, Set.mem_Ioi, g]]
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
  exact hraw

private lemma smoothingBMinus_aestronglyMeasurable (x : ℝ) (f : L2) :
    AEStronglyMeasurable (smoothingBMinus x f) volume := by
  let g : L2 := fourierL2 f
  have hq : Measure.QuasiMeasurePreserving (fun w : ℝ => -Real.sqrt w)
      (volume.restrict (Set.Ioi 0)) volume := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp
        qmp_sqrt_Ioi
  have hcomp : AEStronglyMeasurable
      (fun w : ℝ => (g : ℝ → ℂ) (-Real.sqrt w))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [Function.comp_def] using
      (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving hq
  have hraw : AEStronglyMeasurable (fun w : ℝ =>
      ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I *
          ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ)) *
            (g : ℝ → ℂ) (-Real.sqrt w)))
      (volume.restrict (Set.Ioi 0)) := by
    have hw : AEStronglyMeasurable
        (fun w : ℝ => ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))
        (volume.restrict (Set.Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_id.rpow_const (fun w hw => Or.inl (ne_of_gt hw)))
      exact measurableSet_Ioi
    exact hw.mul ((by fun_prop : Continuous fun w : ℝ =>
      Complex.exp (-Complex.I *
        ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))).aestronglyMeasurable.mul hcomp)
  rw [show smoothingBMinus x f = (Set.Ioi (0 : ℝ)).indicator (fun w =>
      ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I *
          ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ)) *
            (g : ℝ → ℂ) (-Real.sqrt w))) by
    funext w
    simp only [smoothingBMinus, Set.indicator, Set.mem_Ioi, g]]
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
  exact hraw

private lemma enorm_smoothingBPlus_sq (x : ℝ) (f : L2) (w : ℝ) :
    ‖smoothingBPlus x f w‖ₑ ^ (2 : ℝ) =
      (Set.Ioi (0 : ℝ)).indicator (fun w =>
        ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
          ‖(fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ)) w := by
  by_cases hw : 0 < w
  · simp only [Set.indicator, Set.mem_Ioi, if_pos hw]
    rw [smoothingBPlus, if_pos hw, enorm_mul, enorm_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hexp : ‖Complex.exp (Complex.I *
        ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp, Complex.mul_re]
      norm_num
    rw [hexp]
    simp only [ENNReal.one_rpow, one_mul]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hw.le _)]
    congr 1
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (Real.rpow_nonneg hw.le _) 2]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num
  · simp [smoothingBPlus, Set.indicator, hw]

private lemma enorm_smoothingBMinus_sq (x : ℝ) (f : L2) (w : ℝ) :
    ‖smoothingBMinus x f w‖ₑ ^ (2 : ℝ) =
      (Set.Ioi (0 : ℝ)).indicator (fun w =>
        ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
          ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ₑ ^ (2 : ℝ)) w := by
  by_cases hw : 0 < w
  · simp only [Set.indicator, Set.mem_Ioi, if_pos hw]
    rw [smoothingBMinus, if_pos hw, enorm_mul, enorm_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hexp : ‖Complex.exp (-Complex.I *
        ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp]
      norm_num [Complex.mul_re]
    rw [hexp]
    simp only [ENNReal.one_rpow, one_mul]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hw.le _)]
    congr 1
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (Real.rpow_nonneg hw.le _) 2]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num
  · simp [smoothingBMinus, Set.indicator, hw]

private lemma smoothingBPlus_memLp (x : ℝ) (f : L2) :
    MemLp (smoothingBPlus x f) 2 volume := by
  refine ⟨smoothingBPlus_aestronglyMeasurable x f, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  norm_num only [ENNReal.toReal_ofNat]
  rw [show (fun w => ‖smoothingBPlus x f w‖ₑ ^ (2 : ℝ)) = fun w =>
      (Set.Ioi (0 : ℝ)).indicator (fun w =>
        ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
          ‖(fourierL2 f : ℝ → ℂ) (Real.sqrt w)‖ₑ ^ (2 : ℝ)) w by
    funext w; exact enorm_smoothingBPlus_sq x f w]
  rw [lintegral_indicator measurableSet_Ioi, weighted_sqrt_lintegral]
  exact ENNReal.mul_ne_top (by norm_num)
    ((setLIntegral_le_lintegral (Set.Ioi 0)
      (fun y : ℝ => ‖(fourierL2 f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ))).trans_lt
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (Lp.memLp (fourierL2 f)).2)).ne

private lemma smoothingBMinus_memLp (x : ℝ) (f : L2) :
    MemLp (smoothingBMinus x f) 2 volume := by
  refine ⟨smoothingBMinus_aestronglyMeasurable x f, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  norm_num only [ENNReal.toReal_ofNat]
  rw [show (fun w => ‖smoothingBMinus x f w‖ₑ ^ (2 : ℝ)) = fun w =>
      (Set.Ioi (0 : ℝ)).indicator (fun w =>
        ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
          ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ₑ ^ (2 : ℝ)) w by
    funext w; exact enorm_smoothingBMinus_sq x f w]
  rw [lintegral_indicator measurableSet_Ioi]
  rw [show (∫⁻ w : ℝ in Set.Ioi 0,
      ENNReal.ofReal (w ^ (-(1 / 2 : ℝ))) *
        ‖(fourierL2 f : ℝ → ℂ) (-Real.sqrt w)‖ₑ ^ (2 : ℝ)) =
      2 * ∫⁻ y : ℝ in Set.Ioi 0,
        ‖(fourierL2 f : ℝ → ℂ) (-y)‖ₑ ^ (2 : ℝ) by
    simpa using weighted_sqrt_lintegral
      (fun y : ℝ => (fourierL2 f : ℝ → ℂ) (-y))]
  exact ENNReal.mul_ne_top (by norm_num)
    ((setLIntegral_le_lintegral (Set.Ioi 0)
      (fun y : ℝ => ‖(fourierL2 f : ℝ → ℂ) (-y)‖ₑ ^ (2 : ℝ))).trans_lt (by
        rw [lintegral_enorm_neg]
        exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (Lp.memLp (fourierL2 f)).2)).ne

private def smoothingBPlusLp (x : ℝ) (f : L2) : Lp ℂ 2 (volume : Measure ℝ) :=
  (smoothingBPlus_memLp x f).toLp (smoothingBPlus x f)

private def smoothingBMinusLp (x : ℝ) (f : L2) : Lp ℂ 2 (volume : Measure ℝ) :=
  (smoothingBMinus_memLp x f).toLp (smoothingBMinus x f)

private lemma enorm_smoothingBPlus_independent (x y : ℝ) (f : L2) (w : ℝ) :
    ‖smoothingBPlus x f w‖ₑ = ‖smoothingBPlus y f w‖ₑ := by
  by_cases hw : 0 < w
  · simp only [smoothingBPlus, if_pos hw, enorm_mul]
    congr 1
    have hx : ‖Complex.exp (Complex.I *
        ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp, Complex.mul_re]
      norm_num
    have hy : ‖Complex.exp (Complex.I *
        ((2 * Real.pi * y * Real.sqrt w : ℝ) : ℂ))‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp, Complex.mul_re]
      norm_num
    rw [hx, hy]
  · simp [smoothingBPlus, hw]

private lemma enorm_smoothingBMinus_independent (x y : ℝ) (f : L2) (w : ℝ) :
    ‖smoothingBMinus x f w‖ₑ = ‖smoothingBMinus y f w‖ₑ := by
  by_cases hw : 0 < w
  · simp only [smoothingBMinus, if_pos hw, enorm_mul]
    congr 1
    have hx : ‖Complex.exp (-Complex.I *
        ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ))‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp]
      norm_num [Complex.mul_re]
    have hy : ‖Complex.exp (-Complex.I *
        ((2 * Real.pi * y * Real.sqrt w : ℝ) : ℂ))‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp]
      norm_num [Complex.mul_re]
    rw [hx, hy]
  · simp [smoothingBMinus, hw]

private lemma continuous_smoothingBPlusLp (f : L2) :
    Continuous (fun x => smoothingBPlusLp x f) := by
  rw [continuous_iff_seqContinuous]
  intro xn x hxn
  have hpoint (w : ℝ) : Tendsto (fun n => smoothingBPlus (xn n) f w)
      atTop (𝓝 (smoothingBPlus x f w)) := by
    by_cases hw : 0 < w
    · have hc : Continuous (fun z : ℝ =>
          ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            (Complex.exp (Complex.I *
              ((2 * Real.pi * z * Real.sqrt w : ℝ) : ℂ)) *
                (fourierL2 f : ℝ → ℂ) (Real.sqrt w))) := by
        fun_prop
      simpa [smoothingBPlus, hw, Function.comp_def] using hc.continuousAt.tendsto.comp hxn
    · simp [smoothingBPlus, hw]
  have hmeas (n : ℕ) : AEMeasurable (fun w =>
      ‖smoothingBPlus (xn n) f w - smoothingBPlus x f w‖ₑ ^ (2 : ℝ)) volume :=
    ((smoothingBPlus_aestronglyMeasurable (xn n) f).sub
      (smoothingBPlus_aestronglyMeasurable x f)).enorm.pow_const 2
  have hbound (n : ℕ) : ∀ᵐ w : ℝ ∂volume,
      ‖smoothingBPlus (xn n) f w - smoothingBPlus x f w‖ₑ ^ (2 : ℝ) ≤
        4 * ‖smoothingBPlus x f w‖ₑ ^ (2 : ℝ) := by
    filter_upwards with w
    have hi : ‖smoothingBPlus (xn n) f w - smoothingBPlus x f w‖ₑ ≤
        ‖smoothingBPlus (xn n) f w‖ₑ + ‖smoothingBPlus x f w‖ₑ :=
      enorm_sub_le
    have heq := enorm_smoothingBPlus_independent (xn n) x f w
    calc
      ‖smoothingBPlus (xn n) f w - smoothingBPlus x f w‖ₑ ^ (2 : ℝ) ≤
          (‖smoothingBPlus (xn n) f w‖ₑ +
            ‖smoothingBPlus x f w‖ₑ) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hi (by norm_num)
      _ = 4 * ‖smoothingBPlus x f w‖ₑ ^ (2 : ℝ) := by
        rw [heq, ← two_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  have hfin : (∫⁻ w : ℝ, 4 * ‖smoothingBPlus x f w‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (smoothingBPlus_memLp x f).2).ne
  have hint : Tendsto (fun n => ∫⁻ w : ℝ,
      ‖smoothingBPlus (xn n) f w - smoothingBPlus x f w‖ₑ ^ (2 : ℝ))
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence'
      (f := fun _ => 0) (fun w => 4 * ‖smoothingBPlus x f w‖ₑ ^ (2 : ℝ))
      hmeas hbound hfin (Filter.Eventually.of_forall fun w => by
        have he : Tendsto (fun n =>
            smoothingBPlus (xn n) f w - smoothingBPlus x f w)
            atTop (𝓝 0) := by
          simpa using (hpoint w).sub
            (tendsto_const_nhds : Tendsto
              (fun _ : ℕ => smoothingBPlus x f w) atTop
              (𝓝 (smoothingBPlus x f w)))
        have hn : Tendsto (fun n =>
            ‖smoothingBPlus (xn n) f w - smoothingBPlus x f w‖ₑ)
            atTop (𝓝 0) := by
          simpa using he.enorm
        simpa [Function.comp_def] using
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hn)
  have help : Tendsto (fun n => eLpNorm (fun w =>
      smoothingBPlus (xn n) f w - smoothingBPlus x f w) 2 volume)
      atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    convert
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hint
      using 1 <;> norm_num [Function.comp_def]
  change Tendsto (fun n => (smoothingBPlus_memLp (xn n) f).toLp
    (smoothingBPlus (xn n) f)) atTop
      (𝓝 ((smoothingBPlus_memLp x f).toLp (smoothingBPlus x f)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => smoothingBPlus (xn n) f)
    (fun n => smoothingBPlus_memLp (xn n) f)
    (smoothingBPlus x f) (smoothingBPlus_memLp x f)]
  exact help

private lemma continuous_smoothingBMinusLp (f : L2) :
    Continuous (fun x => smoothingBMinusLp x f) := by
  rw [continuous_iff_seqContinuous]
  intro xn x hxn
  have hpoint (w : ℝ) : Tendsto (fun n => smoothingBMinus (xn n) f w)
      atTop (𝓝 (smoothingBMinus x f w)) := by
    by_cases hw : 0 < w
    · have hc : Continuous (fun z : ℝ =>
          ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            (Complex.exp (-Complex.I *
              ((2 * Real.pi * z * Real.sqrt w : ℝ) : ℂ)) *
                (fourierL2 f : ℝ → ℂ) (-Real.sqrt w))) := by
        fun_prop
      simpa [smoothingBMinus, hw, Function.comp_def] using hc.continuousAt.tendsto.comp hxn
    · simp [smoothingBMinus, hw]
  have hmeas (n : ℕ) : AEMeasurable (fun w =>
      ‖smoothingBMinus (xn n) f w - smoothingBMinus x f w‖ₑ ^ (2 : ℝ)) volume :=
    ((smoothingBMinus_aestronglyMeasurable (xn n) f).sub
      (smoothingBMinus_aestronglyMeasurable x f)).enorm.pow_const 2
  have hbound (n : ℕ) : ∀ᵐ w : ℝ ∂volume,
      ‖smoothingBMinus (xn n) f w - smoothingBMinus x f w‖ₑ ^ (2 : ℝ) ≤
        4 * ‖smoothingBMinus x f w‖ₑ ^ (2 : ℝ) := by
    filter_upwards with w
    have hi : ‖smoothingBMinus (xn n) f w - smoothingBMinus x f w‖ₑ ≤
        ‖smoothingBMinus (xn n) f w‖ₑ + ‖smoothingBMinus x f w‖ₑ :=
      enorm_sub_le
    have heq := enorm_smoothingBMinus_independent (xn n) x f w
    calc
      ‖smoothingBMinus (xn n) f w - smoothingBMinus x f w‖ₑ ^ (2 : ℝ) ≤
          (‖smoothingBMinus (xn n) f w‖ₑ +
            ‖smoothingBMinus x f w‖ₑ) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hi (by norm_num)
      _ = 4 * ‖smoothingBMinus x f w‖ₑ ^ (2 : ℝ) := by
        rw [heq, ← two_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  have hfin : (∫⁻ w : ℝ, 4 * ‖smoothingBMinus x f w‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (smoothingBMinus_memLp x f).2).ne
  have hint : Tendsto (fun n => ∫⁻ w : ℝ,
      ‖smoothingBMinus (xn n) f w - smoothingBMinus x f w‖ₑ ^ (2 : ℝ))
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence'
      (f := fun _ => 0) (fun w => 4 * ‖smoothingBMinus x f w‖ₑ ^ (2 : ℝ))
      hmeas hbound hfin (Filter.Eventually.of_forall fun w => by
        have he : Tendsto (fun n =>
            smoothingBMinus (xn n) f w - smoothingBMinus x f w)
            atTop (𝓝 0) := by
          simpa using (hpoint w).sub
            (tendsto_const_nhds : Tendsto
              (fun _ : ℕ => smoothingBMinus x f w) atTop
              (𝓝 (smoothingBMinus x f w)))
        have hn : Tendsto (fun n =>
            ‖smoothingBMinus (xn n) f w - smoothingBMinus x f w‖ₑ)
            atTop (𝓝 0) := by
          simpa using he.enorm
        simpa [Function.comp_def] using
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hn)
  have help : Tendsto (fun n => eLpNorm (fun w =>
      smoothingBMinus (xn n) f w - smoothingBMinus x f w) 2 volume)
      atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    convert
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hint
      using 1 <;> norm_num [Function.comp_def]
  change Tendsto (fun n => (smoothingBMinus_memLp (xn n) f).toLp
    (smoothingBMinus (xn n) f)) atTop
      (𝓝 ((smoothingBMinus_memLp x f).toLp (smoothingBMinus x f)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => smoothingBMinus (xn n) f)
    (fun n => smoothingBMinus_memLp (xn n) f)
    (smoothingBMinus x f) (smoothingBMinus_memLp x f)]
  exact help

theorem continuous_AxRepresentative (f : L2) :
    Continuous (fun x => AxRepresentative x f) := by
  have hsum (x : ℝ) :
      (homogeneous_smoothing_identity f x).1.toLp (smoothingB x f) =
        smoothingBPlusLp x f + smoothingBMinusLp x f := by
    apply Lp.ext
    filter_upwards [(homogeneous_smoothing_identity f x).1.coeFn_toLp,
      (smoothingBPlus_memLp x f).coeFn_toLp,
      (smoothingBMinus_memLp x f).coeFn_toLp,
      Lp.coeFn_add (smoothingBPlusLp x f) (smoothingBMinusLp x f)]
      with w hs hp hm ha
    change (smoothingBPlusLp x f : ℝ → ℂ) w = smoothingBPlus x f w at hp
    change (smoothingBMinusLp x f : ℝ → ℂ) w = smoothingBMinus x f w at hm
    rw [hs, ha]
    change smoothingB x f w =
      (smoothingBPlusLp x f : ℝ → ℂ) w + (smoothingBMinusLp x f : ℝ → ℂ) w
    rw [hp, hm]
    exact congrFun (smoothingB_eq_plus_add_minus x f) w
  change Continuous (fun x =>
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
      ((homogeneous_smoothing_identity f x).1.toLp (smoothingB x f)))
  simp_rw [hsum]
  exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous.comp
    ((continuous_smoothingBPlusLp f).add (continuous_smoothingBMinusLp f))

/-- A jointly measurable choice of the canonical point-smoothing sections. -/
noncomputable def jointAxRepresentative (f : L2) : ℝ × ℝ → ℂ :=
  Classical.choose (joint_representative_L2_measurable_strong_generic
    volume volume (fun x => AxRepresentative x f)
      (continuous_AxRepresentative f).stronglyMeasurable)

lemma jointAxRepresentative_measurable (f : L2) :
    Measurable (jointAxRepresentative f) :=
  (Classical.choose_spec (joint_representative_L2_measurable_strong_generic
    volume volume (fun x => AxRepresentative x f)
      (continuous_AxRepresentative f).stronglyMeasurable)).1

lemma jointAxRepresentative_slice (f : L2) (x : ℝ) :
    (fun t => jointAxRepresentative f (x, t)) =ᵐ[volume]
      (AxRepresentative x f : ℝ → ℂ) :=
  (Classical.choose_spec (joint_representative_L2_measurable_strong_generic
    volume volume (fun x => AxRepresentative x f)
      (continuous_AxRepresentative f).stronglyMeasurable)).2 x

/-- The canonical smoothing representative is locally square-integrable in
space and globally square-integrable in time. -/
theorem jointAxRepresentative_memLp_Icc (f : L2) (a b : ℝ) :
    MemLp (jointAxRepresentative f) 2
      ((volume.restrict (Set.Icc a b)).prod volume) := by
  refine ⟨(jointAxRepresentative_measurable f).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  norm_num only [ENNReal.toReal_ofNat]
  rw [MeasureTheory.lintegral_prod _
    ((jointAxRepresentative_measurable f).enorm.pow_const 2).aemeasurable]
  let C : ℝ≥0∞ := (8 : ℝ≥0∞) * ENNReal.ofReal ‖f‖ ^ (2 : ℝ)
  have hsection (x : ℝ) :
      (∫⁻ t : ℝ, ‖jointAxRepresentative f (x, t)‖ₑ ^ (2 : ℝ)) ≤ C := by
    have hslice := jointAxRepresentative_slice f x
    have hnorm : ENNReal.ofReal ‖AxRepresentative x f‖ ≤
        (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal ‖f‖ :=
      by
        rw [ofReal_norm, AxRepresentative, LinearIsometryEquiv.enorm_map,
          Lp.enorm_toLp (homogeneous_smoothing_identity f x).1]
        exact eLpNorm_smoothingB_le x f
    rw [show (∫⁻ t : ℝ, ‖jointAxRepresentative f (x, t)‖ₑ ^ (2 : ℝ)) =
        ∫⁻ t : ℝ, ‖(AxRepresentative x f : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) by
      apply lintegral_congr_ae
      filter_upwards [hslice] with t ht
      rw [ht]]
    have hsquare := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at hsquare
    simp_rw [← ENNReal.rpow_mul] at hsquare
    norm_num at hsquare
    have hAx : (∫⁻ t : ℝ,
        ‖(AxRepresentative x f : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)) =
        ENNReal.ofReal ‖AxRepresentative x f‖ ^ (2 : ℝ) := by
      rw [ofReal_norm, Lp.enorm_def,
        eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      norm_num only [ENNReal.toReal_ofNat]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hAx]
    simpa only [C, ← ofReal_norm, ENNReal.rpow_two] using hsquare
  have hle : (∫⁻ x : ℝ in Set.Icc a b,
      ∫⁻ t : ℝ, ‖jointAxRepresentative f (x, t)‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ _x : ℝ in Set.Icc a b, C :=
    lintegral_mono hsection
  refine (hle.trans_lt ?_).ne
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top (by finiteness) measure_Icc_lt_top

/-- A bundled `H^{1/2}` curve represents the spatial cutoff of an `L²` curve. -/
def IsLocalizedHsRepresentative (χ : 𝓢(ℝ, ℂ)) (I : Set ℝ)
    (w : ℝ → L2) (localized : ℝ → Hs (1 / 2 : ℝ)) : Prop :=
  ∀ᵐ t : ℝ ∂volume.restrict I,
    Hs.toTempered (1 / 2 : ℝ) (localized t) =
      TemperedDistribution.smulLeftCLM ℂ (χ : ℝ → ℂ)
        (MeasureTheory.Lp.toTemperedDistribution (w t))

end CubicNLSPhaseRetrieval
