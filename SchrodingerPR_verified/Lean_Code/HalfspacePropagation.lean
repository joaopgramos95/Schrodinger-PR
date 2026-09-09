import Lean_Code.CarlemanClosure

/-!
# Half-space propagation

Blueprint chapter: `chap:halfspace` (module 14).
Imports: module 13.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Quantitative scale used for `N` moving-interface steps. -/
structure MovingInterfaceScale where
  delta : ℝ
  height : ℝ
  steps : ℕ

/-- `def:moving-interface-scale`: `δ=L/(32N)` and `h=(c₀/2)√δ`. -/
def movingInterfaceScale (c0 a b : ℝ) (N : ℕ) : MovingInterfaceScale where
  delta := (b - a) / (32 * N)
  height := (c0 / 2) * Real.sqrt ((b - a) / (32 * N))
  steps := N

/-! ## Explicit moving-interface cutoffs -/

/-- The increasing transition used on the left side of a moving-interface step. -/
def oneStepLeftTransition (a δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a - 2 * δ) / δ)

/-- The decreasing transition used on the right side of a moving-interface step. -/
def oneStepRightTransition (b δ t : ℝ) : ℝ :=
  Real.smoothTransition ((b - 2 * δ - t) / δ)

theorem smoothTransition_iteratedDeriv_two_sub_div (c δ t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => Real.smoothTransition ((s - c) / δ)) t =
      δ⁻¹ ^ 2 * iteratedDeriv 2 Real.smoothTransition ((t - c) / δ) := by
  let g : ℝ → ℝ := fun x => Real.smoothTransition (δ⁻¹ * x)
  have hfun : (fun s : ℝ => Real.smoothTransition ((s - c) / δ)) =
      fun s => g (s - c) := by
    funext s
    simp only [g, div_eq_mul_inv]
    congr 1
    ring
  rw [hfun]
  rw [show iteratedDeriv 2 (fun s => g (s - c)) t = iteratedDeriv 2 g (t - c) by
    simpa only [congrFun (iteratedDeriv_comp_sub_const 2 g c) t]]
  have hscale := iteratedDeriv_comp_const_mul
    (n := 2) (@Real.smoothTransition.contDiff 2) δ⁻¹
  change iteratedDeriv 2 g (t - c) = _
  rw [show iteratedDeriv 2 g (t - c) =
      δ⁻¹ ^ 2 * iteratedDeriv 2 Real.smoothTransition (δ⁻¹ * (t - c)) by
    exact congrFun hscale (t - c)]
  congr 2
  simp only [div_eq_mul_inv]
  ring

theorem smoothTransition_iteratedDeriv_two_const_sub_div (c δ t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => Real.smoothTransition ((c - s) / δ)) t =
      δ⁻¹ ^ 2 * iteratedDeriv 2 Real.smoothTransition ((c - t) / δ) := by
  let g : ℝ → ℝ := fun x => Real.smoothTransition (δ⁻¹ * x)
  have hfun : (fun s : ℝ => Real.smoothTransition ((c - s) / δ)) =
      fun s => g (c - s) := by
    funext s
    simp only [g, div_eq_mul_inv]
    congr 1
    ring
  rw [hfun]
  rw [show iteratedDeriv 2 (fun s => g (c - s)) t = iteratedDeriv 2 g (c - t) by
    rw [congrFun (iteratedDeriv_comp_const_sub 2 g c) t]
    norm_num]
  have hscale := iteratedDeriv_comp_const_mul
    (n := 2) (@Real.smoothTransition.contDiff 2) δ⁻¹
  change iteratedDeriv 2 g (c - t) = _
  rw [show iteratedDeriv 2 g (c - t) =
      δ⁻¹ ^ 2 * iteratedDeriv 2 Real.smoothTransition (δ⁻¹ * (c - t)) by
    exact congrFun hscale (c - t)]
  congr 2
  simp only [div_eq_mul_inv]
  ring

/-- Fixed `L¹` mass of the second derivative of Mathlib's smooth transition. -/
def oneStepTransitionSecondMass : ℝ :=
  ∫ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x|

theorem smoothTransition_sub_div_second_mass (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ t : ℝ, |iteratedDeriv 2
      (fun s : ℝ => Real.smoothTransition ((s - c) / δ)) t|) =
      δ⁻¹ * oneStepTransitionSecondMass := by
  simp_rw [smoothTransition_iteratedDeriv_two_sub_div]
  simp_rw [abs_mul, abs_pow, abs_inv, abs_of_pos hδ]
  rw [integral_const_mul]
  have hshift :
      (∫ t : ℝ, |iteratedDeriv 2 Real.smoothTransition ((t - c) / δ)|) =
        ∫ t : ℝ, |iteratedDeriv 2 Real.smoothTransition (t / δ)| := by
    let F : ℝ → ℝ := fun x => |iteratedDeriv 2 Real.smoothTransition (x / δ)|
    calc
      _ = ∫ t : ℝ, F (t + (-c)) := by rfl
      _ = ∫ t : ℝ, F t := integral_add_right_eq_self F (-c)
      _ = _ := rfl
  rw [hshift, Measure.integral_comp_div
    (fun x : ℝ => |iteratedDeriv 2 Real.smoothTransition x|) δ]
  simp only [abs_of_pos hδ, smul_eq_mul, oneStepTransitionSecondMass]
  field_simp

theorem smoothTransition_const_sub_div_second_mass (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ t : ℝ, |iteratedDeriv 2
      (fun s : ℝ => Real.smoothTransition ((c - s) / δ)) t|) =
      δ⁻¹ * oneStepTransitionSecondMass := by
  simp_rw [smoothTransition_iteratedDeriv_two_const_sub_div]
  simp_rw [abs_mul, abs_pow, abs_inv, abs_of_pos hδ]
  rw [integral_const_mul]
  have hreflect :
      (∫ t : ℝ, |iteratedDeriv 2 Real.smoothTransition ((c - t) / δ)|) =
        ∫ t : ℝ, |iteratedDeriv 2 Real.smoothTransition ((t + c) / δ)| := by
    let F : ℝ → ℝ := fun t => |iteratedDeriv 2 Real.smoothTransition ((c - t) / δ)|
    rw [← integral_neg_eq_self F]
    simp only [F, sub_neg_eq_add, add_comm]
  rw [hreflect]
  have hshift :
      (∫ t : ℝ, |iteratedDeriv 2 Real.smoothTransition ((t + c) / δ)|) =
        ∫ t : ℝ, |iteratedDeriv 2 Real.smoothTransition (t / δ)| := by
    let F : ℝ → ℝ := fun x => |iteratedDeriv 2 Real.smoothTransition (x / δ)|
    exact integral_add_right_eq_self F c
  rw [hshift, Measure.integral_comp_div
    (fun x : ℝ => |iteratedDeriv 2 Real.smoothTransition x|) δ]
  simp only [abs_of_pos hδ, smul_eq_mul, oneStepTransitionSecondMass]
  field_simp

/-- Interface profile: it is `2` near the temporal boundary and `-1` on the
inner slab.  The moving translation used below is `B + h * oneStepProfile`. -/
def oneStepProfile (a b δ t : ℝ) : ℝ :=
  2 - 3 * oneStepLeftTransition a δ t * oneStepRightTransition b δ t

/-- Compactly supported time cutoff, equal to one on the region on which the
moving interface is already constant. -/
def oneStepTimeCutoff (a b δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a - δ) / δ) *
    Real.smoothTransition ((b - δ - t) / δ)

theorem oneStepLeftTransition_eq_zero {a δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ a + 2 * δ) : oneStepLeftTransition a δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply (div_le_iff₀ hδ).2
  linarith

theorem oneStepLeftTransition_eq_one {a δ t : ℝ} (hδ : 0 < δ)
    (ht : a + 3 * δ ≤ t) : oneStepLeftTransition a δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div hδ).2
  linarith

theorem oneStepRightTransition_eq_zero {b δ t : ℝ} (hδ : 0 < δ)
    (ht : b - 2 * δ ≤ t) : oneStepRightTransition b δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply (div_le_iff₀ hδ).2
  linarith

theorem oneStepRightTransition_eq_one {b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ b - 3 * δ) : oneStepRightTransition b δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div hδ).2
  linarith

theorem oneStep_transition_product_eq_add_sub_one
    {a b δ t : ℝ} (hδ : 0 < δ) (hsep : a + 3 * δ ≤ b - 3 * δ) :
    oneStepLeftTransition a δ t * oneStepRightTransition b δ t =
      oneStepLeftTransition a δ t + oneStepRightTransition b δ t - 1 := by
  by_cases ht : t ≤ a + 3 * δ
  · rw [oneStepRightTransition_eq_one hδ (ht.trans hsep)]
    ring
  · rw [oneStepLeftTransition_eq_one hδ (le_of_not_ge ht)]
    ring

theorem oneStepProfile_eq_transition_sum
    {a b δ : ℝ} (hδ : 0 < δ) (hsep : a + 3 * δ ≤ b - 3 * δ) :
    oneStepProfile a b δ = fun t =>
      5 - 3 * oneStepLeftTransition a δ t - 3 * oneStepRightTransition b δ t := by
  funext t
  rw [oneStepProfile]
  rw [show 3 * oneStepLeftTransition a δ t * oneStepRightTransition b δ t =
    3 * (oneStepLeftTransition a δ t * oneStepRightTransition b δ t) by ring]
  rw [oneStep_transition_product_eq_add_sub_one hδ hsep]
  ring

theorem oneStepProfile_iteratedDeriv_two_eq
    {a b δ t : ℝ} (hδ : 0 < δ) (hsep : a + 3 * δ ≤ b - 3 * δ) :
    iteratedDeriv 2 (oneStepProfile a b δ) t =
      -3 * iteratedDeriv 2 (oneStepLeftTransition a δ) t -
        3 * iteratedDeriv 2 (oneStepRightTransition b δ) t := by
  rw [oneStepProfile_eq_transition_sum hδ hsep]
  have hc : ContDiffAt ℝ 2 (fun _ : ℝ => (5 : ℝ)) t := by fun_prop
  have hl : ContDiffAt ℝ 2 (oneStepLeftTransition a δ) t := by
    unfold oneStepLeftTransition
    fun_prop
  have hr : ContDiffAt ℝ 2 (oneStepRightTransition b δ) t := by
    unfold oneStepRightTransition
    fun_prop
  have h3l : ContDiffAt ℝ 2 (fun s => 3 * oneStepLeftTransition a δ s) t :=
    (contDiffAt_const (c := (3 : ℝ))).mul hl
  have h3r : ContDiffAt ℝ 2 (fun s => 3 * oneStepRightTransition b δ s) t :=
    (contDiffAt_const (c := (3 : ℝ))).mul hr
  rw [show (fun s : ℝ => 5 - 3 * oneStepLeftTransition a δ s -
      3 * oneStepRightTransition b δ s) =
      (fun s => 5 - 3 * oneStepLeftTransition a δ s) -
        (fun s => 3 * oneStepRightTransition b δ s) by rfl]
  rw [iteratedDeriv_sub (hc.sub h3l) h3r]
  rw [show (fun s : ℝ => 5 - 3 * oneStepLeftTransition a δ s) =
      (fun _ : ℝ => 5) - (fun s => 3 * oneStepLeftTransition a δ s) by rfl]
  rw [iteratedDeriv_sub hc h3l]
  rw [iteratedDeriv_const, if_neg (by norm_num : (2 : ℕ) ≠ 0), zero_sub]
  rw [iteratedDeriv_const_mul 3 hl, iteratedDeriv_const_mul 3 hr]
  ring

theorem oneStepLeftTransition_contDiff (a δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (oneStepLeftTransition a δ) := by
  unfold oneStepLeftTransition
  fun_prop

theorem oneStepRightTransition_contDiff (b δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (oneStepRightTransition b δ) := by
  unfold oneStepRightTransition
  fun_prop

theorem oneStepLeftTransition_iteratedDeriv_two_hasCompactSupport
    {a δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (iteratedDeriv 2 (oneStepLeftTransition a δ)) := by
  refine HasCompactSupport.intro (K := Set.Icc (a + 2 * δ) (a + 3 * δ))
    isCompact_Icc ?_
  intro t ht
  by_cases hleft : t < a + 2 * δ
  · have heq : oneStepLeftTransition a δ =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hleft] with s hs
      change s < a + 2 * δ at hs
      exact oneStepLeftTransition_eq_zero hδ hs.le
    rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
    norm_num
  · have hright : a + 3 * δ < t := by
      by_contra hnright
      exact ht ⟨le_of_not_gt hleft, le_of_not_gt hnright⟩
    have heq : oneStepLeftTransition a δ =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hright] with s hs
      change a + 3 * δ < s at hs
      exact oneStepLeftTransition_eq_one hδ hs.le
    rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
    norm_num

theorem oneStepRightTransition_iteratedDeriv_two_hasCompactSupport
    {b δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (iteratedDeriv 2 (oneStepRightTransition b δ)) := by
  refine HasCompactSupport.intro (K := Set.Icc (b - 3 * δ) (b - 2 * δ))
    isCompact_Icc ?_
  intro t ht
  by_cases hleft : t < b - 3 * δ
  · have heq : oneStepRightTransition b δ =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
      filter_upwards [isOpen_Iio.mem_nhds hleft] with s hs
      change s < b - 3 * δ at hs
      exact oneStepRightTransition_eq_one hδ hs.le
    rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
    norm_num
  · have hright : b - 2 * δ < t := by
      by_contra hnright
      exact ht ⟨le_of_not_gt hleft, le_of_not_gt hnright⟩
    have heq : oneStepRightTransition b δ =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds hright] with s hs
      change b - 2 * δ < s at hs
      exact oneStepRightTransition_eq_zero hδ hs.le
    rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
    norm_num

theorem oneStepLeftTransition_second_mass {a δ : ℝ} (hδ : 0 < δ) :
    (∫ t : ℝ, |iteratedDeriv 2 (oneStepLeftTransition a δ) t|) =
      δ⁻¹ * oneStepTransitionSecondMass := by
  have hfun : oneStepLeftTransition a δ =
      fun t => Real.smoothTransition ((t - (a + 2 * δ)) / δ) := by
    funext t
    unfold oneStepLeftTransition
    congr 1
    ring
  rw [hfun]
  exact smoothTransition_sub_div_second_mass (a + 2 * δ) hδ

theorem oneStepRightTransition_second_mass {b δ : ℝ} (hδ : 0 < δ) :
    (∫ t : ℝ, |iteratedDeriv 2 (oneStepRightTransition b δ) t|) =
      δ⁻¹ * oneStepTransitionSecondMass := by
  have hfun : oneStepRightTransition b δ =
      fun t => Real.smoothTransition (((b - 2 * δ) - t) / δ) := by
    funext t
    unfold oneStepRightTransition
    congr 1
  rw [hfun]
  exact smoothTransition_const_sub_div_second_mass (b - 2 * δ) hδ

theorem oneStepTransitionSecondMass_nonneg : 0 ≤ oneStepTransitionSecondMass := by
  exact integral_nonneg fun _ => abs_nonneg _

/-- Uniform scale bound `‖ω''‖₁ ≤ K/δ` for the explicit profile. -/
theorem oneStepProfile_second_mass_le
    {a b δ : ℝ} (hδ : 0 < δ) (hsep : a + 3 * δ ≤ b - 3 * δ) :
    (∫ t : ℝ, |iteratedDeriv 2 (oneStepProfile a b δ) t|) ≤
      (6 * oneStepTransitionSecondMass) / δ := by
  have hleftCont : Continuous (iteratedDeriv 2 (oneStepLeftTransition a δ)) :=
    (oneStepLeftTransition_contDiff a δ).continuous_iteratedDeriv 2 (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hrightCont : Continuous (iteratedDeriv 2 (oneStepRightTransition b δ)) :=
    (oneStepRightTransition_contDiff b δ).continuous_iteratedDeriv 2 (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hleftRaw : Integrable (iteratedDeriv 2 (oneStepLeftTransition a δ)) :=
    hleftCont.integrable_of_hasCompactSupport
      (oneStepLeftTransition_iteratedDeriv_two_hasCompactSupport hδ)
  have hrightRaw : Integrable (iteratedDeriv 2 (oneStepRightTransition b δ)) :=
    hrightCont.integrable_of_hasCompactSupport
      (oneStepRightTransition_iteratedDeriv_two_hasCompactSupport hδ)
  have hleftInt : Integrable (fun t =>
      |iteratedDeriv 2 (oneStepLeftTransition a δ) t|) := hleftRaw.norm
  have hrightInt : Integrable (fun t =>
      |iteratedDeriv 2 (oneStepRightTransition b δ) t|) := hrightRaw.norm
  have hprofileRaw : Integrable (iteratedDeriv 2 (oneStepProfile a b δ)) := by
    have hcomb : Integrable (fun t =>
        -3 * iteratedDeriv 2 (oneStepLeftTransition a δ) t -
          3 * iteratedDeriv 2 (oneStepRightTransition b δ) t) :=
      (hleftRaw.const_mul (-3)).sub (hrightRaw.const_mul 3)
    exact hcomb.congr (Filter.Eventually.of_forall fun t => by
      rw [oneStepProfile_iteratedDeriv_two_eq hδ hsep])
  have hprofileInt : Integrable (fun t =>
      |iteratedDeriv 2 (oneStepProfile a b δ) t|) := hprofileRaw.norm
  have hmajorInt : Integrable (fun t =>
      3 * |iteratedDeriv 2 (oneStepLeftTransition a δ) t| +
        3 * |iteratedDeriv 2 (oneStepRightTransition b δ) t|) :=
    (hleftInt.const_mul 3).add (hrightInt.const_mul 3)
  calc
    (∫ t : ℝ, |iteratedDeriv 2 (oneStepProfile a b δ) t|) ≤
        ∫ t : ℝ, (3 * |iteratedDeriv 2 (oneStepLeftTransition a δ) t| +
          3 * |iteratedDeriv 2 (oneStepRightTransition b δ) t|) := by
      apply integral_mono hprofileInt hmajorInt
      intro t
      change |iteratedDeriv 2 (oneStepProfile a b δ) t| ≤
        3 * |iteratedDeriv 2 (oneStepLeftTransition a δ) t| +
          3 * |iteratedDeriv 2 (oneStepRightTransition b δ) t|
      rw [oneStepProfile_iteratedDeriv_two_eq hδ hsep]
      calc
        |-3 * iteratedDeriv 2 (oneStepLeftTransition a δ) t -
            3 * iteratedDeriv 2 (oneStepRightTransition b δ) t| ≤
            |-3 * iteratedDeriv 2 (oneStepLeftTransition a δ) t| +
              |3 * iteratedDeriv 2 (oneStepRightTransition b δ) t| := abs_sub _ _
        _ = 3 * |iteratedDeriv 2 (oneStepLeftTransition a δ) t| +
            3 * |iteratedDeriv 2 (oneStepRightTransition b δ) t| := by
          simp only [abs_mul, abs_neg]
          norm_num
    _ = 3 * (δ⁻¹ * oneStepTransitionSecondMass) +
        3 * (δ⁻¹ * oneStepTransitionSecondMass) := by
      rw [integral_add (hleftInt.const_mul 3) (hrightInt.const_mul 3),
        integral_const_mul, integral_const_mul,
        oneStepLeftTransition_second_mass hδ,
        oneStepRightTransition_second_mass hδ]
    _ = (6 * oneStepTransitionSecondMass) / δ := by
      field_simp
      ring

theorem oneStepProfile_eq_two_of_left {a b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ a + 2 * δ) : oneStepProfile a b δ t = 2 := by
  simp [oneStepProfile, oneStepLeftTransition_eq_zero hδ ht]

theorem oneStepProfile_eq_two_of_right {a b δ t : ℝ} (hδ : 0 < δ)
    (ht : b - 2 * δ ≤ t) : oneStepProfile a b δ t = 2 := by
  simp [oneStepProfile, oneStepRightTransition_eq_zero hδ ht]

theorem oneStepProfile_eq_neg_one {a b δ t : ℝ} (hδ : 0 < δ)
    (htl : a + 3 * δ ≤ t) (htr : t ≤ b - 3 * δ) :
    oneStepProfile a b δ t = -1 := by
  rw [oneStepProfile, oneStepLeftTransition_eq_one hδ htl,
    oneStepRightTransition_eq_one hδ htr]
  norm_num

theorem oneStepTimeCutoff_eq_zero_of_left {a b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ a + δ) : oneStepTimeCutoff a b δ t = 0 := by
  rw [oneStepTimeCutoff, Real.smoothTransition.zero_of_nonpos]
  · simp
  · apply (div_le_iff₀ hδ).2
    linarith

theorem oneStepTimeCutoff_eq_zero_of_right {a b δ t : ℝ} (hδ : 0 < δ)
    (ht : b - δ ≤ t) : oneStepTimeCutoff a b δ t = 0 := by
  have hzero : Real.smoothTransition ((b - δ - t) / δ) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    apply (div_le_iff₀ hδ).2
    linarith
  simp [oneStepTimeCutoff, hzero]

theorem oneStepTimeCutoff_eq_one {a b δ t : ℝ} (hδ : 0 < δ)
    (htl : a + 2 * δ ≤ t) (htr : t ≤ b - 2 * δ) :
    oneStepTimeCutoff a b δ t = 1 := by
  rw [oneStepTimeCutoff, Real.smoothTransition.one_of_one_le,
    Real.smoothTransition.one_of_one_le, one_mul]
  · apply (one_le_div hδ).2
    linarith
  · apply (one_le_div hδ).2
    linarith

theorem oneStepProfile_contDiff (a b δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (oneStepProfile a b δ) := by
  unfold oneStepProfile oneStepLeftTransition oneStepRightTransition
  fun_prop

theorem oneStepProfile_iteratedDeriv_two_hasCompactSupport
    {a b δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (iteratedDeriv 2 (oneStepProfile a b δ)) := by
  refine HasCompactSupport.intro (K := Set.Icc (a + 2 * δ) (b - 2 * δ))
    isCompact_Icc ?_
  intro t ht
  by_cases hleft : t < a + 2 * δ
  · have heq : oneStepProfile a b δ =ᶠ[𝓝 t] (fun _ : ℝ => 2) := by
      filter_upwards [isOpen_Iio.mem_nhds hleft] with s hs
      exact oneStepProfile_eq_two_of_left hδ hs.le
    rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
    norm_num
  · have hright : b - 2 * δ < t := by
      by_contra hnright
      exact ht ⟨le_of_not_gt hleft, le_of_not_gt hnright⟩
    have heq : oneStepProfile a b δ =ᶠ[𝓝 t] (fun _ : ℝ => 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds hright] with s hs
      exact oneStepProfile_eq_two_of_right hδ hs.le
    rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
    norm_num

theorem oneStepTimeCutoff_contDiff (a b δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (oneStepTimeCutoff a b δ) := by
  unfold oneStepTimeCutoff
  fun_prop

theorem oneStepTimeCutoff_complex_deriv (a b δ t : ℝ) :
    deriv (fun s => (oneStepTimeCutoff a b δ s : ℂ)) t =
      ((deriv (oneStepTimeCutoff a b δ) t : ℝ) : ℂ) := by
  have hη : HasDerivAt (oneStepTimeCutoff a b δ)
      (deriv (oneStepTimeCutoff a b δ) t) t :=
    ((oneStepTimeCutoff_contDiff a b δ).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hcomp := Complex.ofRealCLM.hasFDerivAt.comp t hη.hasFDerivAt
  have hderiv := hcomp.hasDerivAt.deriv
  change deriv (Complex.ofRealCLM ∘ oneStepTimeCutoff a b δ) t =
    Complex.ofRealCLM (deriv (oneStepTimeCutoff a b δ) t)
  simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hderiv

theorem oneStepTimeCutoff_hasCompactSupport {a b δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (oneStepTimeCutoff a b δ) := by
  refine HasCompactSupport.intro (K := Set.Icc (a + δ) (b - δ)) isCompact_Icc ?_
  intro t ht
  by_cases hleft : t ≤ a + δ
  · exact oneStepTimeCutoff_eq_zero_of_left hδ hleft
  · have hright : b - δ ≤ t := by
      by_contra hnright
      exact ht ⟨le_of_lt (lt_of_not_ge hleft), le_of_not_ge hnright⟩
    exact oneStepTimeCutoff_eq_zero_of_right hδ hright

theorem oneStepTimeCutoff_complex_hasCompactSupport {a b δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun t => (oneStepTimeCutoff a b δ t : ℂ)) := by
  have h := (oneStepTimeCutoff_hasCompactSupport (a := a) (b := b) (δ := δ) hδ).comp_left
    (g := fun x : ℝ => (x : ℂ)) (by norm_num)
  change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ oneStepTimeCutoff a b δ)
  exact h

/-- The time cutoff can change only where the moving interface has its safe
value `2`.  This is the exact support separation needed for the cutoff error. -/
theorem oneStepTimeCutoff_deriv_eq_zero_of_profile_ne_two
    {a b δ t : ℝ} (hδ : 0 < δ) (hprofile : oneStepProfile a b δ t ≠ 2) :
    deriv (oneStepTimeCutoff a b δ) t = 0 := by
  have hleft : oneStepLeftTransition a δ t ≠ 0 := by
    intro hzero
    apply hprofile
    simp [oneStepProfile, hzero]
  have hright : oneStepRightTransition b δ t ≠ 0 := by
    intro hzero
    apply hprofile
    simp [oneStepProfile, hzero]
  have hleftArg : 0 < (t - a - 2 * δ) / δ :=
    lt_of_not_ge (fun h => hleft (Real.smoothTransition.zero_of_nonpos h))
  have hrightArg : 0 < (b - 2 * δ - t) / δ :=
    lt_of_not_ge (fun h => hright (Real.smoothTransition.zero_of_nonpos h))
  have htleft : a + 2 * δ < t := by
    rcases (div_pos_iff.mp hleftArg) with h | h
    · linarith [h.1]
    · linarith [hδ, h.2]
  have htright : t < b - 2 * δ := by
    rcases (div_pos_iff.mp hrightArg) with h | h
    · linarith [h.1]
    · linarith [hδ, h.2]
  have heq : oneStepTimeCutoff a b δ =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨htleft, htright⟩] with s hs
    exact oneStepTimeCutoff_eq_one hδ hs.1.le hs.2.le
  rw [heq.deriv_eq, deriv_const]

theorem oneStepTimeCutoff_deriv_eq_zero_of_notMem_Ioo
    {a b δ t : ℝ} (hδ : 0 < δ) (ht : t ∉ Set.Ioo a b) :
    deriv (oneStepTimeCutoff a b δ) t = 0 := by
  have hor : t ≤ a ∨ b ≤ t := by
    simpa only [Set.mem_Ioo, not_and_or, not_lt] using ht
  rcases hor with hleft | hright
  · have ht' : t < a + δ := by linarith
    have heq : oneStepTimeCutoff a b δ =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ht'] with s hs
      change s < a + δ at hs
      exact oneStepTimeCutoff_eq_zero_of_left hδ hs.le
    rw [heq.deriv_eq, deriv_const]
  · have ht' : b - δ < t := by linarith
    have heq : oneStepTimeCutoff a b δ =ᶠ[nhds t] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht'] with s hs
      change b - δ < s at hs
      exact oneStepTimeCutoff_eq_zero_of_right hδ hs.le
    rw [heq.deriv_eq, deriv_const]

theorem oneStepTimeCutoff_eq_zero_of_notMem_Ioo
    {a b δ t : ℝ} (hδ : 0 < δ) (ht : t ∉ Set.Ioo a b) :
    oneStepTimeCutoff a b δ t = 0 := by
  have hor : t ≤ a ∨ b ≤ t := by
    simpa only [Set.mem_Ioo, not_and_or, not_lt] using ht
  rcases hor with hleft | hright
  · exact oneStepTimeCutoff_eq_zero_of_left hδ (by linarith)
  · exact oneStepTimeCutoff_eq_zero_of_right hδ (by linarith)
  /-
  · have ht' : b - δ < t := by linarith
    have heq : oneStepTimeCutoff a b δ =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht'] with s hs
      change b - δ < s at hs
      exact oneStepTimeCutoff_eq_zero_of_right hδ hs.le
    rw [heq.deriv_eq, deriv_const]
  -/

theorem oneStepProfile_mem_Icc (a b δ t : ℝ) :
    oneStepProfile a b δ t ∈ Set.Icc (-1) 2 := by
  have hl0 := Real.smoothTransition.nonneg ((t - a - 2 * δ) / δ)
  have hl1 := Real.smoothTransition.le_one ((t - a - 2 * δ) / δ)
  have hr0 := Real.smoothTransition.nonneg ((b - 2 * δ - t) / δ)
  have hr1 := Real.smoothTransition.le_one ((b - 2 * δ - t) / δ)
  have hprod0 : 0 ≤ oneStepLeftTransition a δ t * oneStepRightTransition b δ t :=
    mul_nonneg hl0 hr0
  have hprod1 : oneStepLeftTransition a δ t * oneStepRightTransition b δ t ≤ 1 :=
    mul_le_one₀ hl1 hr0 hr1
  change -1 ≤ 2 - 3 * oneStepLeftTransition a δ t * oneStepRightTransition b δ t ∧
    2 - 3 * oneStepLeftTransition a δ t * oneStepRightTransition b δ t ≤ 2
  constructor <;> nlinarith

theorem oneStepTimeCutoff_mem_Icc (a b δ t : ℝ) :
    oneStepTimeCutoff a b δ t ∈ Set.Icc 0 1 := by
  have hl0 := Real.smoothTransition.nonneg ((t - a - δ) / δ)
  have hl1 := Real.smoothTransition.le_one ((t - a - δ) / δ)
  have hr0 := Real.smoothTransition.nonneg ((b - δ - t) / δ)
  have hr1 := Real.smoothTransition.le_one ((b - δ - t) / δ)
  exact ⟨mul_nonneg hl0 hr0, mul_le_one₀ hl1 hr0 hr1⟩

/-- The actual moving boundary used in one quantitative step. -/
def oneStepMovingBoundary (B h a b δ t : ℝ) : ℝ :=
  B + h * oneStepProfile a b δ t

theorem oneStepMovingBoundary_contDiff (B h a b δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (oneStepMovingBoundary B h a b δ) := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun t : ℝ => B + h * oneStepProfile a b δ t)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => B) := contDiff_const
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => h) := contDiff_const
  exact hB.add (hh.mul (oneStepProfile_contDiff a b δ))

theorem oneStepMovingBoundary_eq_safe_left {B h a b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ a + 2 * δ) : oneStepMovingBoundary B h a b δ t = B + 2 * h := by
  rw [oneStepMovingBoundary, oneStepProfile_eq_two_of_left hδ ht]
  ring

theorem oneStepMovingBoundary_eq_safe_right {B h a b δ t : ℝ} (hδ : 0 < δ)
    (ht : b - 2 * δ ≤ t) : oneStepMovingBoundary B h a b δ t = B + 2 * h := by
  rw [oneStepMovingBoundary, oneStepProfile_eq_two_of_right hδ ht]
  ring

theorem oneStepMovingBoundary_eq_inner {B h a b δ t : ℝ} (hδ : 0 < δ)
    (htl : a + 3 * δ ≤ t) (htr : t ≤ b - 3 * δ) :
    oneStepMovingBoundary B h a b δ t = B - h := by
  rw [oneStepMovingBoundary, oneStepProfile_eq_neg_one hδ htl htr]
  ring

theorem oneStepMovingBoundary_iteratedDeriv_two (B h a b δ t : ℝ) :
    iteratedDeriv 2 (oneStepMovingBoundary B h a b δ) t =
      h * iteratedDeriv 2 (oneStepProfile a b δ) t := by
  let n : WithTop ℕ∞ := (2 : ℕ)
  have hconst : ContDiffAt ℝ n (fun _ : ℝ => B) t := by fun_prop
  have hprofile : ContDiffAt ℝ n (oneStepProfile a b δ) t :=
    (oneStepProfile_contDiff a b δ).contDiffAt.of_le (by
      dsimp [n]
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hmul : ContDiffAt ℝ n (fun s : ℝ => h * oneStepProfile a b δ s) t :=
    (contDiffAt_const (c := h)).mul hprofile
  change iteratedDeriv 2 (fun s : ℝ => B + h * oneStepProfile a b δ s) t = _
  calc
    _ = iteratedDeriv 2 (fun _ : ℝ => B) t +
        iteratedDeriv 2 (fun s : ℝ => h * oneStepProfile a b δ s) t := by
      rw [show (fun s : ℝ => B + h * oneStepProfile a b δ s) =
        (fun _ : ℝ => B) + (fun s : ℝ => h * oneStepProfile a b δ s) by
          funext s
          rfl]
      exact iteratedDeriv_add hconst hmul
    _ = h * iteratedDeriv 2 (oneStepProfile a b δ) t := by
      rw [iteratedDeriv_const, if_neg (by norm_num : (2 : ℕ) ≠ 0), zero_add]
      exact iteratedDeriv_const_mul h hprofile

theorem oneStepProfile_eq_two_of_timeCutoff_deriv_ne_zero
    {a b δ t : ℝ} (hδ : 0 < δ)
    (hderiv : deriv (oneStepTimeCutoff a b δ) t ≠ 0) :
    oneStepProfile a b δ t = 2 := by
  by_contra hprofile
  exact hderiv (oneStepTimeCutoff_deriv_eq_zero_of_profile_ne_two hδ hprofile)

theorem oneStepMovingBoundary_eq_safe_of_timeCutoff_deriv_ne_zero
    {B h a b δ t : ℝ} (hδ : 0 < δ)
    (hderiv : deriv (oneStepTimeCutoff a b δ) t ≠ 0) :
    oneStepMovingBoundary B h a b δ t = B + 2 * h := by
  rw [oneStepMovingBoundary,
    oneStepProfile_eq_two_of_timeCutoff_deriv_ne_zero hδ hderiv]
  ring

theorem oneStep_inner_identities {a b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Set.Ioo (a + 4 * δ) (b - 4 * δ)) :
    oneStepProfile a b δ t = -1 ∧ oneStepTimeCutoff a b δ t = 1 := by
  constructor
  · exact oneStepProfile_eq_neg_one hδ (by linarith [ht.1]) (by linarith [ht.2])
  · exact oneStepTimeCutoff_eq_one hδ (by linarith [ht.1]) (by linarith [ht.2])

/-- Multiplication of a spacetime field by the explicit real time cutoff. -/
def oneStepLocalizedField (a b δ : ℝ) (U : Spacetime2) : Spacetime2 :=
  fun p => (oneStepTimeCutoff a b δ p.1 : ℂ) * U p

theorem oneStepLocalizedField_hasBoundedTimeSupport {a b δ : ℝ} (hδ : 0 < δ)
    (hab : a + δ < b - δ) (U : Spacetime2) :
    HasBoundedTimeSupport (oneStepLocalizedField a b δ U) := by
  refine ⟨a + δ, b - δ, hab, Filter.Eventually.of_forall ?_⟩
  intro p hp
  by_cases hleft : p.1 ≤ a + δ
  · simp [oneStepLocalizedField, oneStepTimeCutoff_eq_zero_of_left hδ hleft]
  · have hright : b - δ ≤ p.1 := by
      by_contra hnright
      exact hp ⟨le_of_lt (lt_of_not_ge hleft), le_of_not_ge hnright⟩
    simp [oneStepLocalizedField, oneStepTimeCutoff_eq_zero_of_right hδ hright]

/-- Acceleration coefficient produced by the Galilean gauge. -/
def oneStepAcceleration (B h a b δ t : ℝ) : ℂ :=
  ((iteratedDeriv 2 (oneStepMovingBoundary B h a b δ) t / 2 : ℝ) : ℂ)

/-- Bounded part of the acceleration potential, supported on `-h < y₁ ≤ h`. -/
def oneStepNearAcceleration (B h a b δ : ℝ) : Spacetime2 :=
  fun p => if -h < p.2.1 ∧ p.2.1 ≤ h then
    oneStepAcceleration B h a b δ p.1 * (p.2.1 : ℂ) else 0

/-- Far part of the acceleration potential, supported on `y₁ ≤ -h`. -/
def oneStepFarAcceleration (B h a b δ : ℝ) : Spacetime2 :=
  fun p => if p.2.1 ≤ -h then
    oneStepAcceleration B h a b δ p.1 * (p.2.1 : ℂ) else 0

theorem oneStep_acceleration_split {B h a b δ : ℝ} {U : Spacetime2}
    (hsupport : ∀ p, h < p.2.1 → U p = 0) (p : ℝ × (ℝ × ℝ)) :
    oneStepAcceleration B h a b δ p.1 * (p.2.1 : ℂ) * U p =
      oneStepNearAcceleration B h a b δ p * U p +
        oneStepFarAcceleration B h a b δ p * U p := by
  by_cases hfar : p.2.1 ≤ -h
  · simp [oneStepNearAcceleration, oneStepFarAcceleration, hfar]
  · by_cases hnear : p.2.1 ≤ h
    · have hlower : -h < p.2.1 := lt_of_not_ge hfar
      simp [oneStepNearAcceleration, oneStepFarAcceleration, hfar, hnear, hlower]
    · have hzero : U p = 0 := hsupport p (lt_of_not_ge hnear)
      simp [hzero]

theorem oneStepAcceleration_eq_profile (B h a b δ t : ℝ) :
    oneStepAcceleration B h a b δ t =
      (((h / 2) * iteratedDeriv 2 (oneStepProfile a b δ) t : ℝ) : ℂ) := by
  rw [oneStepAcceleration, oneStepMovingBoundary_iteratedDeriv_two]
  push_cast
  ring

theorem oneStepAcceleration_integrable {B h a b δ : ℝ} (hδ : 0 < δ) :
    Integrable (oneStepAcceleration B h a b δ) := by
  have hcontinuous : Continuous (iteratedDeriv 2 (oneStepProfile a b δ)) :=
    (oneStepProfile_contDiff a b δ).continuous_iteratedDeriv 2 (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hreal : Integrable (iteratedDeriv 2 (oneStepProfile a b δ)) :=
    hcontinuous.integrable_of_hasCompactSupport
      (oneStepProfile_iteratedDeriv_two_hasCompactSupport hδ)
  have hcomplex : Integrable (fun t =>
      ((iteratedDeriv 2 (oneStepProfile a b δ) t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hreal
  have hmul := hcomplex.const_mul (((h / 2 : ℝ) : ℂ))
  apply hmul.congr
  filter_upwards [] with t
  rw [oneStepAcceleration_eq_profile]
  push_cast
  rfl

theorem oneStepAcceleration_norm {B h a b δ t : ℝ} (hh : 0 ≤ h) :
    ‖oneStepAcceleration B h a b δ t‖ =
      (h / 2) * |iteratedDeriv 2 (oneStepProfile a b δ) t| := by
  rw [oneStepAcceleration_eq_profile, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (div_nonneg hh (by norm_num))]

theorem oneStepAcceleration_norm_integral {B h a b δ : ℝ} (hh : 0 ≤ h) :
    (∫ t : ℝ, ‖oneStepAcceleration B h a b δ t‖) =
      (h / 2) * ∫ t : ℝ, |iteratedDeriv 2 (oneStepProfile a b δ) t| := by
  simp_rw [oneStepAcceleration_norm hh]
  exact integral_const_mul _ _

theorem oneStepNearAcceleration_norm_le {B h a b δ : ℝ} (hh : 0 ≤ h)
    (p : ℝ × (ℝ × ℝ)) :
    ‖oneStepNearAcceleration B h a b δ p‖ ≤
      ‖oneStepAcceleration B h a b δ p.1‖ * h := by
  rw [oneStepNearAcceleration]
  split_ifs with hp
  · rw [norm_mul, Complex.norm_real]
    gcongr
    exact abs_le.mpr ⟨hp.1.le, hp.2⟩
  · simpa only [norm_zero] using
      mul_nonneg (norm_nonneg (oneStepAcceleration B h a b δ p.1)) hh

theorem oneStepAcceleration_continuous (B h a b δ : ℝ) :
    Continuous (oneStepAcceleration B h a b δ) := by
  rw [show oneStepAcceleration B h a b δ = fun t =>
      (((h / 2) * iteratedDeriv 2 (oneStepProfile a b δ) t : ℝ) : ℂ) by
    funext t
    exact oneStepAcceleration_eq_profile B h a b δ t]
  have hp : Continuous (iteratedDeriv 2 (oneStepProfile a b δ)) :=
    (oneStepProfile_contDiff a b δ).continuous_iteratedDeriv 2 (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  exact Complex.ofRealCLM.continuous.comp (continuous_const.mul hp)

theorem oneStepNearAcceleration_measurable (B h a b δ : ℝ) :
    Measurable (oneStepNearAcceleration B h a b δ) := by
  unfold oneStepNearAcceleration
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst measurable_const)
  · exact (oneStepAcceleration_continuous B h a b δ).measurable.comp measurable_fst |>.mul
      (Complex.continuous_ofReal.measurable.comp measurable_snd.fst)
  · exact measurable_const

theorem oneStepNearAcceleration_sectionENorm_le {B h a b δ t : ℝ}
    (hh : 0 ≤ h) :
    sectionENorm (volume.prod volume) ⊤ (oneStepNearAcceleration B h a b δ) t ≤
      ENNReal.ofReal (‖oneStepAcceleration B h a b δ t‖ * h) := by
  rw [sectionENorm, eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [] with x
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (oneStepNearAcceleration_norm_le hh (t, x))

/-- The near acceleration is controlled in `L¹_tL∞_x` by the time integral
of the scalar acceleration coefficient. -/
theorem oneStepNearAcceleration_mixed_le {B h a b δ : ℝ} (hδ : 0 < δ)
    (hh : 0 ≤ h) :
    scalarMixedENorm volume (volume.prod volume) 1 ⊤
        (oneStepNearAcceleration B h a b δ) ≤
      ENNReal.ofReal (h * ∫ t : ℝ, ‖oneStepAcceleration B h a b δ t‖) := by
  unfold scalarMixedENorm
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    (∫⁻ t, ‖sectionENorm (volume.prod volume) ⊤
        (oneStepNearAcceleration B h a b δ) t‖ₑ) ≤
        ∫⁻ t, ENNReal.ofReal (‖oneStepAcceleration B h a b δ t‖ * h) := by
      apply lintegral_mono
      intro t
      simpa only [enorm_eq_self] using
        (oneStepNearAcceleration_sectionENorm_le (B := B) (a := a) (b := b)
          (δ := δ) (t := t) hh)
    _ = ENNReal.ofReal (∫ t : ℝ, ‖oneStepAcceleration B h a b δ t‖ * h) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
      · exact (oneStepAcceleration_integrable (B := B) (h := h) (a := a)
          (b := b) hδ).norm.mul_const h
      · filter_upwards [] with t
        positivity
    _ = ENNReal.ofReal (h * ∫ t : ℝ, ‖oneStepAcceleration B h a b δ t‖) := by
      congr 1
      rw [integral_mul_const]
      ring

/-- Quantitative bound for the bounded acceleration potential.  Its size is
quadratic in the interface displacement and inverse-linear in the transition
scale. -/
theorem oneStepNearAcceleration_mixed_le_scaled
    {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h)
    (hsep : a + 3 * δ ≤ b - 3 * δ) :
    scalarMixedENorm volume (volume.prod volume) 1 ⊤
        (oneStepNearAcceleration B h a b δ) ≤
      ENNReal.ofReal (3 * oneStepTransitionSecondMass * h ^ 2 / δ) := by
  refine (oneStepNearAcceleration_mixed_le hδ hh).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [oneStepAcceleration_norm_integral hh]
  have hmass := oneStepProfile_second_mass_le hδ hsep
  calc
    h * ((h / 2) * ∫ t : ℝ,
        |iteratedDeriv 2 (oneStepProfile a b δ) t|) ≤
        h * ((h / 2) * ((6 * oneStepTransitionSecondMass) / δ)) := by
      gcongr
    _ = 3 * oneStepTransitionSecondMass * h ^ 2 / δ := by ring

/-- Moving translation of a spacetime field in the first spatial coordinate. -/
def movingTranslate (w : ℝ → ℝ) (Z : Spacetime2)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  Z (p.1, (p.2.1 + w p.1, p.2.2))

/-- Galilean phase correcting the velocity of a moving interface. -/
def movingGalilean (a : ℝ) (w : ℝ → ℝ) (Z : Spacetime2)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  Complex.exp (-Complex.I *
    ((((deriv w p.1) / 2) * p.2.1 +
      ∫ s in a..p.1, ((deriv w s) / 2) ^ 2 : ℝ) : ℂ)) * movingTranslate w Z p

/-- The time-dependent spatial shear underlying `movingTranslate`. -/
def movingSpatialMap (w : ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (p.1, (p.2.1 + w p.1, p.2.2))

theorem movingSpatialMap_measurePreserving {w : ℝ → ℝ} (hw : Measurable w) :
    MeasurePreserving (movingSpatialMap w)
      (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume)) := by
  change MeasurePreserving
    (fun p : ℝ × (ℝ × ℝ) => (id p.1, (p.2.1 + w p.1, p.2.2)))
    (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume))
  refine MeasurePreserving.skew_product
    (μc := volume.prod volume) (μd := volume.prod volume)
    (g := fun t : ℝ => fun z : ℝ × ℝ => (z.1 + w t, z.2))
    (MeasurePreserving.id volume) ?_ ?_
  · change Measurable (fun p : ℝ × (ℝ × ℝ) => (p.2.1 + w p.1, p.2.2))
    fun_prop
  · filter_upwards [] with t
    have hx := (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) (w t)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
    change Measure.map (Prod.map (fun x : ℝ => x + w t) id)
      (volume.prod volume) = volume.prod volume
    exact hx.map_eq

/-- The moving shear as a measurable equivalence; its inverse subtracts the
same time-dependent displacement. -/
def movingSpatialEquiv (w : ℝ → ℝ) (hw : Measurable w) :
    (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) where
  toFun := movingSpatialMap w
  invFun := movingSpatialMap (fun t => -w t)
  left_inv := by
    intro p
    simp [movingSpatialMap]
  right_inv := by
    intro p
    simp [movingSpatialMap]
  measurable_toFun := by
    unfold movingSpatialMap
    exact measurable_fst.prodMk
      ((measurable_snd.fst.add (hw.comp measurable_fst)).prodMk measurable_snd.snd)
  measurable_invFun := by
    unfold movingSpatialMap
    exact measurable_fst.prodMk
      ((measurable_snd.fst.add (hw.neg.comp measurable_fst)).prodMk measurable_snd.snd)

theorem movingTranslate_sectionENorm (q : ℝ≥0∞) (w : ℝ → ℝ)
    (Z : Spacetime2) (t : ℝ) :
    sectionENorm (volume.prod volume) q (movingTranslate w Z) t =
      sectionENorm (volume.prod volume) q Z t := by
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.addRight (w t)).prodCongr (MeasurableEquiv.refl ℝ)
  have hmap : Measure.map e (volume.prod volume) = volume.prod volume := by
    have hp := (MeasureTheory.measurePreserving_add_right
      (volume : Measure ℝ) (w t)).prod (MeasurePreserving.id (volume : Measure ℝ))
    exact hp.map_eq
  have heq := e.measurableEmbedding.eLpNorm_map_measure
    (p := q) (μ := volume.prod volume) (g := fun x : ℝ × ℝ => Z (t, x))
  rw [hmap] at heq
  have hefun : ((fun x : ℝ × ℝ => Z (t, x)) ∘ e) =
      fun x : ℝ × ℝ => Z (t, (x.1 + w t, x.2)) := by
    funext x
    rcases x with ⟨x₁, x₂⟩
    simp [e, MeasurableEquiv.prodCongr, Equiv.prodCongr]
  rw [hefun] at heq
  simpa only [sectionENorm, movingTranslate] using heq.symm

theorem scalarMixedENorm_movingTranslate (μt : Measure ℝ) (p q : ℝ≥0∞)
    (w : ℝ → ℝ) (Z : Spacetime2) :
    scalarMixedENorm μt (volume.prod volume) p q (movingTranslate w Z) =
      scalarMixedENorm μt (volume.prod volume) p q Z := by
  unfold scalarMixedENorm
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  exact movingTranslate_sectionENorm q w Z t

theorem movingGalilean_sectionENorm (q : ℝ≥0∞) (a : ℝ) (w : ℝ → ℝ)
    (Z : Spacetime2) (t : ℝ) :
    sectionENorm (volume.prod volume) q (movingGalilean a w Z) t =
      sectionENorm (volume.prod volume) q Z t := by
  calc
    sectionENorm (volume.prod volume) q (movingGalilean a w Z) t =
        sectionENorm (volume.prod volume) q (movingTranslate w Z) t := by
      unfold sectionENorm
      apply eLpNorm_congr_norm_ae
      filter_upwards [] with x
      rw [movingGalilean, norm_mul, Complex.norm_exp]
      have him : (-Complex.I *
          ((((deriv w t) / 2) * x.1 +
            ∫ s in a..t, ((deriv w s) / 2) ^ 2 : ℝ) : ℂ)).re = 0 := by
        simp
      rw [him, Real.exp_zero, one_mul]
    _ = sectionENorm (volume.prod volume) q Z t :=
      movingTranslate_sectionENorm q w Z t

theorem scalarMixedENorm_movingGalilean (J : Set ℝ) (p q : ℝ≥0∞)
    (a : ℝ) (w : ℝ → ℝ) (Z : Spacetime2) :
    scalarMixedENorm (volume.restrict J) (volume.prod volume) p q
        (movingGalilean a w Z) =
      scalarMixedENorm (volume.restrict J) (volume.prod volume) p q Z := by
  unfold scalarMixedENorm
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  exact movingGalilean_sectionENorm q a w Z t

theorem eLpNorm_movingGalilean (J : Set ℝ) (q : ℝ≥0∞) (a : ℝ)
    (w : ℝ → ℝ) (hw : Measurable w) (Z : Spacetime2) :
    eLpNorm (movingGalilean a w Z) q
        ((volume.restrict J).prod (volume.prod volume)) =
      eLpNorm Z q ((volume.restrict J).prod (volume.prod volume)) := by
  let μ : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict J).prod (volume.prod volume)
  let e : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) := movingSpatialEquiv w hw
  have hmap : Measure.map e μ = μ := by
    have hp : MeasurePreserving e μ μ := by
      change MeasurePreserving (movingSpatialMap w)
        ((volume.restrict J).prod (volume.prod volume))
        ((volume.restrict J).prod (volume.prod volume))
      refine MeasurePreserving.skew_product
        (μc := volume.prod volume) (μd := volume.prod volume)
        (g := fun t : ℝ => fun z : ℝ × ℝ => (z.1 + w t, z.2))
        (MeasurePreserving.id (volume.restrict J)) ?_ ?_
      · change Measurable (fun p : ℝ × (ℝ × ℝ) => (p.2.1 + w p.1, p.2.2))
        fun_prop
      · filter_upwards [] with t
        exact ((MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) (w t)).prod
          (MeasurePreserving.id (volume : Measure ℝ))).map_eq
    exact hp.map_eq
  have hshear := e.measurableEmbedding.eLpNorm_map_measure
    (p := q) (μ := μ) (g := Z)
  rw [hmap] at hshear
  have hefun : Z ∘ e = movingTranslate w Z := by
    funext p
    rfl
  rw [hefun] at hshear
  calc
    eLpNorm (movingGalilean a w Z) q μ = eLpNorm (movingTranslate w Z) q μ := by
      apply eLpNorm_congr_norm_ae
      filter_upwards [] with p
      rw [movingGalilean, norm_mul, Complex.norm_exp]
      have him : (-Complex.I *
          ((((deriv w p.1) / 2) * p.2.1 +
            ∫ s in a..p.1, ((deriv w s) / 2) ^ 2 : ℝ) : ℂ)).re = 0 := by
        simp
      rw [him, Real.exp_zero, one_mul]
    _ = eLpNorm Z q μ := by
      exact hshear.symm

private theorem movingTranslate_aestronglyMeasurable_iff
    (J : Set ℝ) (w : ℝ → ℝ) (hw : Measurable w) (Z : Spacetime2) :
    AEStronglyMeasurable (movingTranslate w Z)
        ((volume.restrict J).prod (volume.prod volume)) ↔
      AEStronglyMeasurable Z
        ((volume.restrict J).prod (volume.prod volume)) := by
  let μ : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict J).prod (volume.prod volume)
  let e : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) := movingSpatialEquiv w hw
  have hp : MeasurePreserving e μ μ := by
    change MeasurePreserving (movingSpatialMap w)
      ((volume.restrict J).prod (volume.prod volume))
      ((volume.restrict J).prod (volume.prod volume))
    refine MeasurePreserving.skew_product
      (μc := volume.prod volume) (μd := volume.prod volume)
      (g := fun t : ℝ => fun z : ℝ × ℝ => (z.1 + w t, z.2))
      (MeasurePreserving.id (volume.restrict J)) ?_ ?_
    · change Measurable (fun p : ℝ × (ℝ × ℝ) => (p.2.1 + w p.1, p.2.2))
      fun_prop
    · filter_upwards [] with t
      exact ((MeasureTheory.measurePreserving_add_right
        (volume : Measure ℝ) (w t)).prod
          (MeasurePreserving.id (volume : Measure ℝ))).map_eq
  have hiff := hp.aestronglyMeasurable_comp_iff e.measurableEmbedding (g := Z)
  have hefun : Z ∘ e = movingTranslate w Z := by
    funext p
    rfl
  rw [hefun] at hiff
  exact hiff

private theorem movingGalilean_aestronglyMeasurable_iff
    (J : Set ℝ) (a : ℝ) (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (Z : Spacetime2) :
    AEStronglyMeasurable (movingGalilean a w Z)
        ((volume.restrict J).prod (volume.prod volume)) ↔
      AEStronglyMeasurable Z
        ((volume.restrict J).prod (volume.prod volume)) := by
  let phase : Spacetime2 := fun p => Complex.exp (-Complex.I *
    ((((deriv w p.1) / 2) * p.2.1 +
      ∫ s in a..p.1, ((deriv w s) / 2) ^ 2 : ℝ) : ℂ))
  have hdw : Continuous (deriv w) := hw.continuous_deriv le_rfl
  have hg : Continuous (fun s => ((deriv w s) / 2) ^ 2 : ℝ → ℝ) := by
    fun_prop
  have hprim : Continuous
      (fun t => ∫ s in a..t, ((deriv w s) / 2) ^ 2 : ℝ → ℝ) :=
    intervalIntegral.continuous_primitive
      (fun x y => hg.intervalIntegrable x y) a
  have hphase : Measurable phase := by
    apply Continuous.measurable
    dsimp only [phase]
    fun_prop
  have htranslate := movingTranslate_aestronglyMeasurable_iff
    J w hw.continuous.measurable Z
  constructor
  · intro hgal
    have hinv : AEStronglyMeasurable
        (fun p => (phase p)⁻¹ * movingGalilean a w Z p)
        ((volume.restrict J).prod (volume.prod volume)) :=
      hphase.inv.aestronglyMeasurable.mul hgal
    have hmove : AEStronglyMeasurable (movingTranslate w Z)
        ((volume.restrict J).prod (volume.prod volume)) := hinv.congr <| by
      filter_upwards [] with p
      change (phase p)⁻¹ * (phase p * movingTranslate w Z p) =
        movingTranslate w Z p
      rw [← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
    exact htranslate.mp hmove
  · intro hZ
    have hmove := htranslate.mpr hZ
    exact (hphase.aestronglyMeasurable.mul hmove).congr <| by
      filter_upwards [] with p
      rfl

theorem carlemanXprimeNorm_movingGalilean (J : Set ℝ) (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ 1 w) (Z : Spacetime2) :
    carlemanXprimeNorm J (movingGalilean a w Z) = carlemanXprimeNorm J Z := by
  have hiff := movingGalilean_aestronglyMeasurable_iff J a w hw Z
  by_cases hZ : AEStronglyMeasurable Z
      ((volume.restrict J).prod (volume.prod volume))
  · have hgal := hiff.mpr hZ
    simp only [carlemanXprimeNorm, hZ, hgal, if_true]
    exact scalarMixedENorm_movingGalilean J ⊤ 2 a w Z
  · have hgal : ¬ AEStronglyMeasurable (movingGalilean a w Z)
        ((volume.restrict J).prod (volume.prod volume)) := fun h => hZ (hiff.mp h)
    simp [carlemanXprimeNorm, hZ, hgal]

theorem movingSpatialMap_ae {w : ℝ → ℝ} (hw : Measurable w)
    {P : ℝ × (ℝ × ℝ) → Prop}
    (hP : ∀ᵐ p ∂(volume.prod (volume.prod volume)), P p) :
    ∀ᵐ p ∂(volume.prod (volume.prod volume)), P (movingSpatialMap w p) :=
  (movingSpatialMap_measurePreserving hw).quasiMeasurePreserving.ae hP

theorem movingTranslate_ae_support {B : ℝ} {w : ℝ → ℝ} (hw : Measurable w)
    {Z : Spacetime2} (hZ : VanishesAbove B Z) :
    ∀ᵐ p ∂(volume.prod (volume.prod volume)),
      B < p.2.1 + w p.1 → movingTranslate w Z p = 0 := by
  simpa only [movingSpatialMap, movingTranslate] using movingSpatialMap_ae hw hZ

theorem movingGalilean_eq_zero_of_translate_eq_zero
    {a : ℝ} {w : ℝ → ℝ} {Z : Spacetime2} {p : ℝ × (ℝ × ℝ)}
    (hzero : Z (p.1, (p.2.1 + w p.1, p.2.2)) = 0) :
    movingGalilean a w Z p = 0 := by
  simp [movingGalilean, movingTranslate, hzero]

/-- A pointwise version of the inherited support statement.  It is used
before the final measure-preserving change-of-variables step. -/
theorem oneStepMovingGalilean_zero_above_h
    {B h a b δ t y₁ y₂ : ℝ} (hh : 0 ≤ h) (Z : Spacetime2)
    (hZ : ∀ p : ℝ × (ℝ × ℝ), B < p.2.1 → Z p = 0)
    (hy : h < y₁) :
    movingGalilean a (oneStepMovingBoundary B h a b δ) Z (t, (y₁, y₂)) = 0 := by
  apply movingGalilean_eq_zero_of_translate_eq_zero
  apply hZ
  have hprofile := (oneStepProfile_mem_Icc a b δ t).1
  have hmul : -h ≤ h * oneStepProfile a b δ t := by
    have hmul' := mul_le_mul_of_nonneg_left hprofile hh
    simpa only [mul_neg, mul_one] using hmul'
  change B < y₁ + oneStepMovingBoundary B h a b δ t
  unfold oneStepMovingBoundary
  linarith

/-- On the support of the time-cutoff derivative the inherited support is
stronger by another `h`, because the boundary is exactly `B + 2h`. -/
theorem oneStepMovingGalilean_zero_on_cutoff_deriv
    {B h a b δ t y₁ y₂ : ℝ} (hδ : 0 < δ) (Z : Spacetime2)
    (hZ : ∀ p : ℝ × (ℝ × ℝ), B < p.2.1 → Z p = 0)
    (hderiv : deriv (oneStepTimeCutoff a b δ) t ≠ 0)
    (hy : -2 * h < y₁) :
    movingGalilean a (oneStepMovingBoundary B h a b δ) Z (t, (y₁, y₂)) = 0 := by
  apply movingGalilean_eq_zero_of_translate_eq_zero
  apply hZ
  rw [oneStepMovingBoundary_eq_safe_of_timeCutoff_deriv_ne_zero hδ hderiv]
  linarith

theorem oneStepMovingGalilean_vanishesAbove
    {B h a b δ : ℝ} (hh : 0 ≤ h) (Z : Spacetime2) (hZ : VanishesAbove B Z) :
    VanishesAbove h (movingGalilean a (oneStepMovingBoundary B h a b δ) Z) := by
  have hshear := movingTranslate_ae_support
    (oneStepMovingBoundary_contDiff B h a b δ).continuous.measurable hZ
  filter_upwards [hshear] with p hp
  intro hy
  apply movingGalilean_eq_zero_of_translate_eq_zero
  apply hp
  have hprofile := (oneStepProfile_mem_Icc a b δ p.1).1
  have hmul : -h ≤ h * oneStepProfile a b δ p.1 := by
    have hmul' := mul_le_mul_of_nonneg_left hprofile hh
    simpa only [mul_neg, mul_one] using hmul'
  change B < p.2.1 + oneStepMovingBoundary B h a b δ p.1
  unfold oneStepMovingBoundary
  linarith

theorem oneStepMovingGalilean_ae_zero_on_cutoff_deriv
    {B h a b δ : ℝ} (hδ : 0 < δ) (Z : Spacetime2) (hZ : VanishesAbove B Z) :
    ∀ᵐ p ∂(volume.prod (volume.prod volume)),
      deriv (oneStepTimeCutoff a b δ) p.1 ≠ 0 → -2 * h < p.2.1 →
        movingGalilean a (oneStepMovingBoundary B h a b δ) Z p = 0 := by
  have hshear := movingTranslate_ae_support
    (oneStepMovingBoundary_contDiff B h a b δ).continuous.measurable hZ
  filter_upwards [hshear] with p hp
  intro hderiv hy
  apply movingGalilean_eq_zero_of_translate_eq_zero
  apply hp
  rw [oneStepMovingBoundary_eq_safe_of_timeCutoff_deriv_ne_zero hδ hderiv]
  linarith

/-- The exact remainder after the acceleration potential is split into a
bounded near part and a far exponentially separated part. -/
def oneStepCutoffError (B h a b δ : ℝ) (U : Spacetime2) : Spacetime2 :=
  fun p => (oneStepTimeCutoff a b δ p.1 : ℂ) *
      oneStepFarAcceleration B h a b δ p * U p +
    Complex.I * ((deriv (oneStepTimeCutoff a b δ) p.1 : ℝ) : ℂ) * U p

/-- Multiplication of a spacetime distribution by a smooth scalar function of
time. -/
def timeMultiplier (η : ℝ → ℂ) (U : Spacetime2) : Spacetime2 :=
  fun p => η p.1 * U p

lemma schrodinger2DAdjointTest_timeMultiplier (η : ℝ → ℂ) (Ψ : Spacetime2)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (p : ℝ × (ℝ × ℝ)) :
    schrodinger2DAdjointTest (timeMultiplier η Ψ) p =
      η p.1 * schrodinger2DAdjointTest Ψ p -
        Complex.I * deriv η p.1 * Ψ p := by
  have hη1 : DifferentiableAt ℝ η p.1 := hη.differentiable (by simp) p.1
  have hΨtcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Ψ (t, p.2)) :=
    hΨ.comp (by fun_prop)
  have hΨt : DifferentiableAt ℝ (fun t => Ψ (t, p.2)) p.1 :=
    hΨtcd.differentiable (by simp) p.1
  have hΨxcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Ψ (p.1, (x, p.2.2))) := hΨ.comp (by fun_prop)
  have hΨx : ContDiffAt ℝ 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 :=
    hΨxcd.contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hΨycd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => Ψ (p.1, (p.2.1, y))) := hΨ.comp (by fun_prop)
  have hΨy : ContDiffAt ℝ 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2 :=
    hΨycd.contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  unfold schrodinger2DAdjointTest timeMultiplier
  change -Complex.I * deriv (fun t => η t * Ψ (t, p.2)) p.1 +
      iteratedDeriv 2 (fun x => η p.1 * Ψ (p.1, (x, p.2.2))) p.2.1 +
      iteratedDeriv 2 (fun y => η p.1 * Ψ (p.1, (p.2.1, y))) p.2.2 = _
  rw [show (fun t => η t * Ψ (t, p.2)) = η * (fun t => Ψ (t, p.2)) by rfl,
    deriv_mul hη1 hΨt,
    iteratedDeriv_const_mul (η p.1) hΨx,
    iteratedDeriv_const_mul (η p.1) hΨy]
  ring

set_option maxHeartbeats 2000000 in
/-- The distributional smooth time-product rule.  The two support assumptions
state that the multiplier and its derivative are supported in the time set
on which the original weak equation is known. -/
theorem weakSchrodinger2D_timeMultiplier {J : Set ℝ} {U R : Spacetime2}
    (hUR : IsWeakSchrodinger2DOn J U R)
    (η : ℝ → ℂ) (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηJ : ∀ t ∈ tsupport η, t ∈ J)
    (hηdJ : ∀ t ∈ tsupport (deriv η), t ∈ J) :
    IsWeakSchrodinger2D (timeMultiplier η U)
      (fun p => η p.1 * R p + Complex.I * deriv η p.1 * U p) := by
  intro Ψ hΨ hΨc
  let Φ : Spacetime2 := timeMultiplier η Ψ
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    dsimp [Φ, timeMultiplier]
    exact (hη.comp (by fun_prop)).mul hΨ
  have hΦc : HasCompactSupport Φ := by
    apply hΨc.mono
    intro p hp hzero
    exact hp (by simp [Φ, timeMultiplier, hzero])
  have hΦJ : ∀ p ∈ tsupport Φ, p.1 ∈ J := by
    intro p hp
    have hpηsp : p ∈ tsupport (fun q : ℝ × (ℝ × ℝ) => η q.1) := by
      apply tsupport_mul_subset_left
      change p ∈ tsupport (fun q : ℝ × (ℝ × ℝ) => η q.1 * Ψ q) at hp
      exact hp
    apply hηJ p.1
    exact (tsupport_comp_subset_preimage η continuous_fst) hpηsp
  obtain ⟨hUΦ, hUadjΦ, hRΦ, heq⟩ := hUR Φ hΦ hΦc hΦJ
  let χ : Spacetime2 := fun p => Complex.I * deriv η p.1 * Ψ p
  have hηd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv η) :=
    (contDiff_infty_iff_deriv.mp hη).2
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    dsimp [χ]
    exact (contDiff_const.mul (hηd.comp (by fun_prop))).mul hΨ
  have hχc : HasCompactSupport χ := by
    apply hΨc.mono
    intro p hp hzero
    exact hp (by simp [χ, hzero])
  have hχJ : ∀ p ∈ tsupport χ, p.1 ∈ J := by
    intro p hp
    have hpcoef : p ∈ tsupport (fun q : ℝ × (ℝ × ℝ) =>
        Complex.I * deriv η q.1) := by
      apply tsupport_mul_subset_left
      simpa only [χ] using hp
    have hpderivComp : p ∈ tsupport (fun q : ℝ × (ℝ × ℝ) => deriv η q.1) := by
      apply tsupport_comp_subset (g := fun z : ℂ => Complex.I * z) (by simp)
      change p ∈ tsupport ((fun z : ℂ => Complex.I * z) ∘
        (fun q : ℝ × (ℝ × ℝ) => deriv η q.1)) at hpcoef
      exact hpcoef
    apply hηdJ p.1
    exact (tsupport_comp_subset_preimage (deriv η) continuous_fst) hpderivComp
  obtain ⟨hUχ, _, _, _⟩ := hUR χ hχ hχc hχJ
  have hadj (p : ℝ × (ℝ × ℝ)) :
      schrodinger2DAdjointTest Φ p = η p.1 * schrodinger2DAdjointTest Ψ p -
        Complex.I * deriv η p.1 * Ψ p :=
    schrodinger2DAdjointTest_timeMultiplier η Ψ hη hΨ p
  have hleft (p : ℝ × (ℝ × ℝ)) :
      timeMultiplier η U p * schrodinger2DAdjointTest Ψ p =
        U p * schrodinger2DAdjointTest Φ p + U p * χ p := by
    rw [hadj]
    dsimp [timeMultiplier, χ]
    ring
  have hright (p : ℝ × (ℝ × ℝ)) :
      (η p.1 * R p + Complex.I * deriv η p.1 * U p) * Ψ p =
        R p * Φ p + U p * χ p := by
    dsimp [Φ, timeMultiplier, χ]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hUΦ.congr
    filter_upwards [] with p
    dsimp [Φ, timeMultiplier]
    ring
  · exact (hUadjΦ.add hUχ).congr
      (Filter.Eventually.of_forall (fun p => (hleft p).symm))
  · exact (hRΦ.add hUχ).congr
      (Filter.Eventually.of_forall (fun p => (hright p).symm))
  · calc
      (∫ p, timeMultiplier η U p * schrodinger2DAdjointTest Ψ p
          ∂(volume.prod (volume.prod volume))) =
          ∫ p, (U p * schrodinger2DAdjointTest Φ p + U p * χ p)
            ∂(volume.prod (volume.prod volume)) :=
        integral_congr_ae (Filter.Eventually.of_forall hleft)
      _ = (∫ p, U p * schrodinger2DAdjointTest Φ p
            ∂(volume.prod (volume.prod volume))) +
          ∫ p, U p * χ p ∂(volume.prod (volume.prod volume)) :=
        integral_add hUadjΦ hUχ
      _ = (∫ p, R p * Φ p ∂(volume.prod (volume.prod volume))) +
          ∫ p, U p * χ p ∂(volume.prod (volume.prod volume)) := by rw [heq]
      _ = ∫ p, (R p * Φ p + U p * χ p)
          ∂(volume.prod (volume.prod volume)) := (integral_add hRΦ hUχ).symm
      _ = ∫ p, (η p.1 * R p + Complex.I * deriv η p.1 * U p) * Ψ p
          ∂(volume.prod (volume.prod volume)) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => (hright p).symm))

/-- Schrödinger equation with a multiplicative spacetime potential on a time set. -/
def IsWeakPotentialEquation (J : Set ℝ) (Z W : Spacetime2) : Prop :=
  IsWeakSchrodinger2DOn J Z (fun p => W p * Z p)

/-! ## Distributional Galilean transform -/


def movingSpatialHomeomorph (w : ℝ → ℝ) (hw : Continuous w) :
    (ℝ × (ℝ × ℝ)) ≃ₜ (ℝ × (ℝ × ℝ)) where
  toFun := movingSpatialMap w
  invFun := movingSpatialMap (fun t => -w t)
  left_inv := by intro p; simp [movingSpatialMap]
  right_inv := by intro p; simp [movingSpatialMap]
  continuous_toFun := by unfold movingSpatialMap; fun_prop
  continuous_invFun := by unfold movingSpatialMap; fun_prop

def galGamma (w : ℝ → ℝ) (t : ℝ) : ℝ := deriv w t / 2

def galTheta (a : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in a..t, galGamma w s ^ 2

def galPhase (a : ℝ) (w : ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  Complex.exp (-Complex.I * ((galGamma w p.1 * p.2.1 + galTheta a w p.1 : ℝ) : ℂ))

def galTest (a : ℝ) (w : ℝ → ℝ) (Ψ : Spacetime2) : Spacetime2 := fun p =>
  galPhase a w (p.1, (p.2.1 - w p.1, p.2.2)) *
    Ψ (p.1, (p.2.1 - w p.1, p.2.2))

lemma galGamma_smooth (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (galGamma w) := by
  unfold galGamma
  exact (contDiff_infty_iff_deriv.mp hw).2.div_const 2

lemma galTheta_smooth (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (galTheta a w) := by
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (galGamma w) := galGamma_smooth w hw
  have hg2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => galGamma w t ^ 2) := hg.pow 2
  rw [contDiff_infty_iff_deriv]
  constructor
  · exact intervalIntegral.differentiable_integral_of_continuous hg2.continuous
  · have hd : deriv (galTheta a w) = fun t => galGamma w t ^ 2 := by
      funext t
      exact (intervalIntegral.integral_hasDerivAt_right
        (hg2.continuous.intervalIntegrable _ _)
        hg2.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hg2.continuous.continuousAt).deriv
    rw [hd]
    exact hg2

lemma galPhase_smooth (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (galPhase a w) := by
  unfold galPhase
  have hg := galGamma_smooth w hw
  have ht := galTheta_smooth a w hw
  have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => galGamma w p.1 * p.2.1 + galTheta a w p.1) := by
    fun_prop
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => ((galGamma w p.1 * p.2.1 + galTheta a w p.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  exact Complex.contDiff_exp.comp (contDiff_const.mul hc)

lemma galTest_smooth (a : ℝ) (w : ℝ → ℝ) (Ψ : Spacetime2)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (galTest a w Ψ) := by
  unfold galTest
  have hp := galPhase_smooth a w hw
  have hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => (p.1, (p.2.1 - w p.1, p.2.2))) :=
    contDiff_fst.prodMk
      (contDiff_snd.fst.sub (hw.comp contDiff_fst) |>.prodMk contDiff_snd.snd)
  exact (hp.comp hm).mul (hΨ.comp hm)

end CubicNLSPhaseRetrieval

namespace CubicNLSPhaseRetrieval

lemma galGamma_deriv (w : ℝ → ℝ) (t : ℝ) :
    deriv (galGamma w) t = iteratedDeriv 2 w t / 2 := by
  unfold galGamma
  rw [deriv_div_const]
  rw [show iteratedDeriv 2 w = deriv (iteratedDeriv 1 w) by
    simpa using (iteratedDeriv_succ (n := 1) (f := w))]
  rw [iteratedDeriv_one]

lemma galTheta_deriv (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (t : ℝ) :
    deriv (galTheta a w) t = galGamma w t ^ 2 := by
  have hg := galGamma_smooth w hw
  exact (intervalIntegral.integral_hasDerivAt_right
    ((hg.pow 2).continuous.intervalIntegrable _ _)
    (hg.pow 2).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hg.pow 2).continuous.continuousAt).deriv

lemma galPhase_space_hasDerivAt (a : ℝ) (w : ℝ → ℝ) (t y₂ x : ℝ) :
    HasDerivAt (fun y => galPhase a w (t, (y, y₂)))
      (galPhase a w (t, (x, y₂)) *
        (-Complex.I * ((galGamma w t : ℝ) : ℂ))) x := by
  have hr : HasDerivAt (fun y : ℝ => galGamma w t * y + galTheta a w t)
      (galGamma w t) x := by
    simpa [id] using
      ((hasDerivAt_id x).const_mul (galGamma w t) |>.add_const (galTheta a w t))
  have hc := hr.ofReal_comp.const_mul (-Complex.I) |>.cexp
  simpa [galPhase] using hc

lemma galPhase_space_deriv (a : ℝ) (w : ℝ → ℝ) (t y₂ x : ℝ) :
    deriv (fun y => galPhase a w (t, (y, y₂))) x =
      galPhase a w (t, (x, y₂)) * (-Complex.I * ((galGamma w t : ℝ) : ℂ)) :=
  (galPhase_space_hasDerivAt a w t y₂ x).deriv

lemma galPhase_space_iteratedDeriv_two (a : ℝ) (w : ℝ → ℝ) (t y₂ x : ℝ) :
    iteratedDeriv 2 (fun y => galPhase a w (t, (y, y₂))) x =
      -((galGamma w t) ^ 2 : ℝ) * galPhase a w (t, (x, y₂)) := by
  rw [show iteratedDeriv 2 (fun y => galPhase a w (t, (y, y₂))) =
      deriv (iteratedDeriv 1 (fun y => galPhase a w (t, (y, y₂)))) by
    simpa using (iteratedDeriv_succ (n := 1)
      (f := fun y => galPhase a w (t, (y, y₂))))]
  rw [iteratedDeriv_one]
  have hfun : deriv (fun y => galPhase a w (t, (y, y₂))) = fun y =>
      galPhase a w (t, (y, y₂)) * (-Complex.I * ((galGamma w t : ℝ) : ℂ)) := by
    funext y
    exact galPhase_space_deriv a w t y₂ y
  rw [hfun]
  rw [deriv_mul_const (galPhase_space_hasDerivAt a w t y₂ x).differentiableAt]
  rw [galPhase_space_deriv]
  calc
    galPhase a w (t, (x, y₂)) * (-Complex.I * ((galGamma w t : ℝ) : ℂ)) *
        (-Complex.I * ((galGamma w t : ℝ) : ℂ)) =
      galPhase a w (t, (x, y₂)) * (Complex.I * Complex.I) *
        (((galGamma w t : ℝ) : ℂ) ^ 2) := by ring
    _ = -((galGamma w t) ^ 2 : ℝ) * galPhase a w (t, (x, y₂)) := by
      rw [Complex.I_mul_I]
      push_cast
      ring

end CubicNLSPhaseRetrieval

namespace CubicNLSPhaseRetrieval

lemma galPsi_inverse_time_deriv (w : ℝ → ℝ) (Ψ : Spacetime2)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (t x y₂ : ℝ) :
    deriv (fun s => Ψ (s, (x - w s, y₂))) t =
      deriv (fun s => Ψ (s, (x - w t, y₂))) t -
        ((deriv w t : ℝ) : ℂ) * deriv (fun y => Ψ (t, (y, y₂))) (x - w t) := by
  let p : ℝ × (ℝ × ℝ) := (t, (x - w t, y₂))
  let D := fderiv ℝ Ψ p
  have hΨF : HasFDerivAt Ψ D p :=
    (hΨ.differentiable (by simp) p).hasFDerivAt
  have hwD : HasDerivAt w (deriv w t) t :=
    (hw.differentiable (by simp) t).hasDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (s, (x - w s, y₂)))
      (1, (-deriv w t, 0)) t := by
    have hb := (hasDerivAt_id t).prodMk
      ((hasDerivAt_const t x).sub hwD |>.prodMk (hasDerivAt_const t y₂))
    convert hb using 1
    · funext s
      simp [id]
    · simp
  have hcomp : HasDerivAt (fun s => Ψ (s, (x - w s, y₂)))
      (D (1, (-deriv w t, 0))) t := by
    simpa only [Function.comp_def, p, D] using hΨF.comp_hasDerivAt t hcurve
  have htimeCurve : HasDerivAt (fun s : ℝ => (s, (x - w t, y₂)))
      (1, (0, 0)) t :=
    (hasDerivAt_id t).prodMk
      ((hasDerivAt_const t (x - w t)).prodMk (hasDerivAt_const t y₂))
  have htime : HasDerivAt (fun s => Ψ (s, (x - w t, y₂)))
      (D (1, (0, 0))) t := by
    simpa only [Function.comp_def, p, D] using hΨF.comp_hasDerivAt t htimeCurve
  have hxCurve : HasDerivAt (fun y : ℝ => (t, (y, y₂)))
      (0, (1, 0)) (x - w t) :=
    (hasDerivAt_const (x - w t) t).prodMk
      ((hasDerivAt_id (x - w t)).prodMk (hasDerivAt_const (x - w t) y₂))
  have hx : HasDerivAt (fun y => Ψ (t, (y, y₂)))
      (D (0, (1, 0))) (x - w t) := by
    simpa only [Function.comp_def, p, D] using hΨF.comp_hasDerivAt (x - w t) hxCurve
  rw [hcomp.deriv, htime.deriv, hx.deriv]
  have hv : ((1 : ℝ), ((-deriv w t : ℝ), (0 : ℝ))) =
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        (-deriv w t) • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
    ext <;> simp
  rw [hv, map_add, map_smul]
  rw [Complex.real_smul]
  push_cast
  ring

lemma galPhase_inverse_time_hasDerivAt (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (t x y₂ : ℝ) :
    HasDerivAt (fun s => galPhase a w (s, (x - w s, y₂)))
      (galPhase a w (t, (x - w t, y₂)) *
        (-Complex.I * (((deriv (galGamma w) t * (x - w t) -
          galGamma w t ^ 2 : ℝ)) : ℂ))) t := by
  have hgD : HasDerivAt (galGamma w) (deriv (galGamma w) t) t :=
    ((galGamma_smooth w hw).differentiable (by simp) t).hasDerivAt
  have hwD : HasDerivAt w (deriv w t) t :=
    (hw.differentiable (by simp) t).hasDerivAt
  have hyD : HasDerivAt (fun s => x - w s) (-deriv w t) t :=
    hwD.const_sub x
  have hθD : HasDerivAt (galTheta a w) (galGamma w t ^ 2) t := by
    have h := ((galTheta_smooth a w hw).differentiable (by simp) t).hasDerivAt
    rw [galTheta_deriv a w hw t] at h
    exact h
  have hr0 := hgD.mul hyD |>.add hθD
  change HasDerivAt (fun s => galGamma w s * (x - w s) + galTheta a w s)
    (deriv (galGamma w) t * (x - w t) +
      galGamma w t * (-deriv w t) + galGamma w t ^ 2) t at hr0
  have hcoef : deriv (galGamma w) t * (x - w t) +
      galGamma w t * (-deriv w t) + galGamma w t ^ 2 =
      deriv (galGamma w) t * (x - w t) - galGamma w t ^ 2 := by
    rw [show deriv w t = 2 * galGamma w t by unfold galGamma; ring]
    ring
  rw [hcoef] at hr0
  have hr : HasDerivAt
      (fun s => galGamma w s * (x - w s) + galTheta a w s)
      (deriv (galGamma w) t * (x - w t) - galGamma w t ^ 2) t := hr0
  have hc := hr.ofReal_comp.const_mul (-Complex.I) |>.cexp
  simpa [galPhase] using hc

end CubicNLSPhaseRetrieval

namespace CubicNLSPhaseRetrieval

lemma iteratedDeriv_mul_two_formula (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (f * g) x = iteratedDeriv 2 f x * g x +
      2 * deriv f x * deriv g x + f x * iteratedDeriv 2 g x := by
  rw [iteratedDeriv_mul hf hg]
  norm_num [iteratedDeriv_zero, iteratedDeriv_one, Finset.sum_range_succ]
  ring

set_option maxHeartbeats 1000000 in
lemma schrodinger2DAdjointTest_galTest (a : ℝ) (w : ℝ → ℝ) (Ψ : Spacetime2)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (p : ℝ × (ℝ × ℝ)) :
    schrodinger2DAdjointTest (galTest a w Ψ) p =
      galPhase a w (p.1, (p.2.1 - w p.1, p.2.2)) *
        (schrodinger2DAdjointTest Ψ (p.1, (p.2.1 - w p.1, p.2.2)) -
          (((iteratedDeriv 2 w p.1 / 2) * (p.2.1 - w p.1) : ℝ) : ℂ) *
            Ψ (p.1, (p.2.1 - w p.1, p.2.2))) := by
  let t := p.1
  let x := p.2.1
  let y₂ := p.2.2
  let y := x - w t
  let E : ℂ := galPhase a w (t, (y, y₂))
  have hcurve : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => (s, (x - w s, y₂))) :=
    contDiff_id.prodMk ((contDiff_const.sub hw).prodMk contDiff_const)
  have hΨcomp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s => Ψ (s, (x - w s, y₂))) := hΨ.comp hcurve
  have hΨtimeD : HasDerivAt (fun s => Ψ (s, (x - w s, y₂)))
      (deriv (fun s => Ψ (s, (x - w t, y₂))) t -
        ((deriv w t : ℝ) : ℂ) * deriv (fun z => Ψ (t, (z, y₂))) y) t := by
    have h := (hΨcomp.differentiable (by simp) t).hasDerivAt
    rw [galPsi_inverse_time_deriv w Ψ hw hΨ t x y₂] at h
    simpa only [y] using h
  have hEtimeD := galPhase_inverse_time_hasDerivAt a w hw t x y₂
  have htime : deriv (fun s => galTest a w Ψ (s, (x, y₂))) t =
      E * (-Complex.I * (((deriv (galGamma w) t * y - galGamma w t ^ 2 : ℝ)) : ℂ)) *
          Ψ (t, (y, y₂)) +
        E * (deriv (fun s => Ψ (s, (y, y₂))) t -
          ((deriv w t : ℝ) : ℂ) * deriv (fun z => Ψ (t, (z, y₂))) y) := by
    have hmul := hEtimeD.mul hΨtimeD
    have hd := hmul.deriv
    change deriv ((fun s => galPhase a w (s, (x - w s, y₂))) *
      (fun s => Ψ (s, (x - w s, y₂)))) t = _
    simpa only [y, E] using hd
  let f : ℝ → ℂ := fun z => galPhase a w (t, (z, y₂))
  let g : ℝ → ℂ := fun z => Ψ (t, (z, y₂))
  have hf : ContDiffAt ℝ 2 f y := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
      (galPhase_smooth a w hw).comp
        (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
    exact hs.contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiffAt ℝ 2 g y := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
      hΨ.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
    exact hs.contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hspace1 : iteratedDeriv 2 (fun z => galTest a w Ψ (t, (z, y₂))) x =
      -((galGamma w t) ^ 2 : ℝ) * E * Ψ (t, (y, y₂)) +
        2 * (E * (-Complex.I * ((galGamma w t : ℝ) : ℂ))) *
          deriv (fun z => Ψ (t, (z, y₂))) y +
        E * iteratedDeriv 2 (fun z => Ψ (t, (z, y₂))) y := by
    change iteratedDeriv 2 (fun z => f (z - w t) * g (z - w t)) x = _
    rw [show (fun z => f (z - w t) * g (z - w t)) =
        fun z => (f * g) (z - w t) by rfl]
    rw [congrFun (iteratedDeriv_comp_sub_const 2 (f * g) (w t)) x]
    rw [iteratedDeriv_mul_two_formula f g y hf hg]
    rw [galPhase_space_iteratedDeriv_two a w t y₂ y,
      galPhase_space_deriv a w t y₂ y]
  have hΨspace2 : ContDiffAt ℝ 2 (fun z => Ψ (t, (y, z))) y₂ := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Ψ (t, (y, z))) :=
      hΨ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
    exact hs.contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hspace2 : iteratedDeriv 2 (fun z => galTest a w Ψ (t, (x, z))) y₂ =
      E * iteratedDeriv 2 (fun z => Ψ (t, (y, z))) y₂ := by
    change iteratedDeriv 2 (fun z =>
      galPhase a w (t, (y, z)) * Ψ (t, (y, z))) y₂ = _
    rw [show (fun z => galPhase a w (t, (y, z)) * Ψ (t, (y, z))) =
        fun z => E * Ψ (t, (y, z)) by rfl]
    exact iteratedDeriv_const_mul E hΨspace2
  unfold schrodinger2DAdjointTest
  change -Complex.I * deriv (fun s => galTest a w Ψ (s, (x, y₂))) t +
      iteratedDeriv 2 (fun z => galTest a w Ψ (t, (z, y₂))) x +
      iteratedDeriv 2 (fun z => galTest a w Ψ (t, (x, z))) y₂ = _
  rw [htime, hspace1, hspace2, galGamma_deriv]
  rw [show deriv w t = 2 * galGamma w t by unfold galGamma; ring]
  dsimp only [t, x, y₂, y, E]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Weak-equation part of the moving Galilean identity, including the
acceleration potential produced by a smooth moving interface. -/
theorem moving_galilean_weak_equation (J : Set ℝ) (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (Z W : Spacetime2)
    (hZW : IsWeakPotentialEquation J Z W) :
  IsWeakPotentialEquation J (movingGalilean a w Z)
    (fun p => W (p.1, (p.2.1 + w p.1, p.2.2)) +
      (((iteratedDeriv 2 w p.1 / 2) * p.2.1 : ℝ) : ℂ)) := by
  change IsWeakSchrodinger2DOn J Z (fun p => W p * Z p) at hZW
  change IsWeakSchrodinger2DOn J (movingGalilean a w Z)
    (fun p => (W (p.1, (p.2.1 + w p.1, p.2.2)) +
      (((iteratedDeriv 2 w p.1 / 2) * p.2.1 : ℝ) : ℂ)) *
        movingGalilean a w Z p)
  intro Ψ hΨ hΨc hΨJ
  let Φ : Spacetime2 := galTest a w Ψ
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := galTest_smooth a w Ψ hw hΨ
  let eh : (ℝ × (ℝ × ℝ)) ≃ₜ (ℝ × (ℝ × ℝ)) :=
    movingSpatialHomeomorph w hw.continuous
  have hΨcompc : HasCompactSupport (Ψ ∘ eh.symm) := hΨc.comp_homeomorph eh.symm
  have hΦc : HasCompactSupport Φ := by
    apply hΨcompc.mono
    intro p hp hzero
    have hz : Ψ (p.1, (p.2.1 - w p.1, p.2.2)) = 0 := by
      simpa [Function.comp_apply, eh, movingSpatialHomeomorph, movingSpatialMap,
        sub_eq_add_neg] using hzero
    exact hp (by simp [Φ, galTest, hz])
  have hΦJ : ∀ p ∈ tsupport Φ, p.1 ∈ J := by
    intro p hp
    have hΦdef : Φ = fun q =>
        galPhase a w (q.1, (q.2.1 - w q.1, q.2.2)) * (Ψ ∘ eh.symm) q := by
      funext q
      rfl
    have hpcomp : p ∈ tsupport (Ψ ∘ eh.symm) := by
      apply tsupport_mul_subset_right
      rwa [← hΦdef]
    have hpinv : eh.symm p ∈ tsupport Ψ :=
      (tsupport_comp_subset_preimage Ψ eh.symm.continuous) hpcomp
    have := hΨJ (eh.symm p) hpinv
    simpa [eh, movingSpatialHomeomorph, movingSpatialMap] using this
  obtain ⟨hZΦ, hZadjΦ, hWZΦ, heq⟩ := hZW Φ hΦ hΦc hΦJ
  let A : Spacetime2 := fun p =>
    ((((iteratedDeriv 2 w p.1 / 2) * (p.2.1 - w p.1) : ℝ) : ℂ))
  let χ : Spacetime2 := fun p => A p * Φ p
  have hiter : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedDeriv 2 w) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 2 hw
  have hAreal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) =>
        (iteratedDeriv 2 w p.1 / 2) * (p.2.1 - w p.1)) := by
    exact ((hiter.comp contDiff_fst).div_const 2).mul
      (contDiff_snd.fst.sub (hw.comp contDiff_fst))
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    exact Complex.ofRealCLM.contDiff.comp hAreal
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hA.mul hΦ
  have hχc : HasCompactSupport χ := by
    apply hΦc.mono
    intro p hp hzero
    exact hp (by simp [χ, hzero])
  have hχJ : ∀ p ∈ tsupport χ, p.1 ∈ J := by
    intro p hp
    apply hΦJ p
    exact tsupport_mul_subset_right hp
  obtain ⟨hZχ, _, _, _⟩ := hZW χ hχ hχc hχJ
  let e : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    movingSpatialEquiv (fun t => -w t) hw.continuous.measurable.neg
  have hePres : MeasurePreserving e
      (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume)) := by
    change MeasurePreserving (movingSpatialMap (fun t => -w t))
      (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume))
    exact movingSpatialMap_measurePreserving hw.continuous.measurable.neg
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have he_apply (p : ℝ × (ℝ × ℝ)) :
      e p = (p.1, (p.2.1 - w p.1, p.2.2)) := by
    simp [e, movingSpatialEquiv, movingSpatialMap, sub_eq_add_neg]
  have hplain (p : ℝ × (ℝ × ℝ)) :
      (fun q => movingGalilean a w Z q * Ψ q) (e p) = Z p * Φ p := by
    rw [he_apply]
    dsimp [Φ, galTest, movingGalilean, movingTranslate, galPhase, galGamma, galTheta]
    ring
  have hadj (p : ℝ × (ℝ × ℝ)) :
      (fun q => movingGalilean a w Z q * schrodinger2DAdjointTest Ψ q) (e p) =
        Z p * schrodinger2DAdjointTest Φ p + Z p * χ p := by
    have hid := schrodinger2DAdjointTest_galTest a w Ψ hw hΨ p
    rw [he_apply]
    rw [hid]
    dsimp [Φ, χ, A, galTest, movingGalilean, movingTranslate,
      galPhase, galGamma, galTheta]
    ring
  have hsource (p : ℝ × (ℝ × ℝ)) :
      (fun q =>
        ((W (q.1, (q.2.1 + w q.1, q.2.2)) +
          (((iteratedDeriv 2 w q.1 / 2) * q.2.1 : ℝ) : ℂ)) *
            movingGalilean a w Z q) * Ψ q) (e p) =
        (W p * Z p) * Φ p + Z p * χ p := by
    rw [he_apply]
    dsimp [Φ, χ, A, galTest, movingGalilean, movingTranslate,
      galPhase, galGamma, galTheta]
    ring
  have transfer {f g : Spacetime2} (hg : Integrable g)
      (hfg : ∀ p, f (e p) = g p) : Integrable f := by
    apply (hePres.integrable_comp_emb hemb).mp
    apply hg.congr
    filter_upwards [] with p
    exact (hfg p).symm
  refine ⟨transfer hZΦ hplain, ?_, ?_, ?_⟩
  · exact transfer (hZadjΦ.add hZχ) hadj
  · exact transfer (hWZΦ.add hZχ) hsource
  · calc
      (∫ q, movingGalilean a w Z q * schrodinger2DAdjointTest Ψ q
          ∂(volume.prod (volume.prod volume))) =
          ∫ p, (fun q => movingGalilean a w Z q *
            schrodinger2DAdjointTest Ψ q) (e p)
              ∂(volume.prod (volume.prod volume)) :=
        (hePres.integral_comp hemb _).symm
      _ = ∫ p, (Z p * schrodinger2DAdjointTest Φ p + Z p * χ p)
          ∂(volume.prod (volume.prod volume)) :=
        integral_congr_ae (Filter.Eventually.of_forall hadj)
      _ = (∫ p, Z p * schrodinger2DAdjointTest Φ p
          ∂(volume.prod (volume.prod volume))) +
            ∫ p, Z p * χ p ∂(volume.prod (volume.prod volume)) :=
        integral_add hZadjΦ hZχ
      _ = (∫ p, (W p * Z p) * Φ p ∂(volume.prod (volume.prod volume))) +
            ∫ p, Z p * χ p ∂(volume.prod (volume.prod volume)) := by rw [heq]
      _ = ∫ p, ((W p * Z p) * Φ p + Z p * χ p)
          ∂(volume.prod (volume.prod volume)) := (integral_add hWZΦ hZχ).symm
      _ = ∫ p, (fun q =>
          ((W (q.1, (q.2.1 + w q.1, q.2.2)) +
            (((iteratedDeriv 2 w q.1 / 2) * q.2.1 : ℝ) : ℂ)) *
              movingGalilean a w Z q) * Ψ q) (e p)
            ∂(volume.prod (volume.prod volume)) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => (hsource p).symm))
      _ = ∫ q,
          ((W (q.1, (q.2.1 + w q.1, q.2.2)) +
            (((iteratedDeriv 2 w q.1 / 2) * q.2.1 : ℝ) : ℂ)) *
              movingGalilean a w Z q) * Ψ q
            ∂(volume.prod (volume.prod volume)) :=
        hePres.integral_comp hemb (fun q =>
          ((W (q.1, (q.2.1 + w q.1, q.2.2)) +
            (((iteratedDeriv 2 w q.1 / 2) * q.2.1 : ℝ) : ℂ)) *
              movingGalilean a w Z q) * Ψ q)

/-- `lem:moving-galilean-distribution`: exact rough-class gauge identity. -/
theorem moving_galilean_distribution (J : Set ℝ) (a : ℝ) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (Z W : Spacetime2)
    (hZW : IsWeakPotentialEquation J Z W) :
  IsWeakPotentialEquation J (movingGalilean a w Z)
    (fun p => W (p.1, (p.2.1 + w p.1, p.2.2)) +
      (((iteratedDeriv 2 w p.1 / 2) * p.2.1 : ℝ) : ℂ)) ∧
  ∀ (J : Set ℝ),
    carlemanXprimeNorm J (movingGalilean a w Z) = carlemanXprimeNorm J Z := by
  refine ⟨moving_galilean_weak_equation J a w hw Z W hZW, ?_⟩
  intro K
  exact carlemanXprimeNorm_movingGalilean K a w (hw.of_le (by norm_num)) Z

/-- Far-interface error with its two exponentially separated components. -/
def momentError (h : ℝ) (A η : ℝ → ℂ) (U : Spacetime2)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  if p.2.1 ≤ -h then
    η p.1 * A p.1 * (p.2.1 : ℂ) * U p + Complex.I * deriv η p.1 * U p
  else 0

theorem exponentialWeight_le_at_far_halfspace {h β y : ℝ}
    (hβ : 0 ≤ β) (hy : y ≤ -h) :
    Real.exp (β * y) ≤ Real.exp (-β * h) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Uniform spatial bound retaining the essential linear moment factor.  For
`β ≥ 1`, the polynomial factor is absorbed without introducing a `1/β`
singularity. -/
theorem far_linear_exponentialWeight_le {h β y : ℝ}
    (hh : 0 < h) (hβ : 1 ≤ β) (hy : y ≤ -h) :
    |y| * Real.exp (β * y) ≤ (h + 1) * Real.exp (-β * h) := by
  let q : ℝ := -h - y
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hyneg : y < 0 := lt_of_le_of_lt hy (neg_lt_zero.mpr hh)
  have habs : |y| = h + q := by
    rw [abs_of_neg hyneg]
    dsimp [q]
    ring
  have hexp : Real.exp (β * y) =
      Real.exp (-β * h) * Real.exp (-β * q) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [q]
    ring
  have hexp_q : Real.exp (-β * q) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hqexp : q * Real.exp (-β * q) ≤ 1 := by
    have harg : -β * q ≤ -q := by nlinarith
    calc
      q * Real.exp (-β * q) ≤ q * Real.exp (-q) := by
        gcongr
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one q
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [habs, hexp]
  calc
    (h + q) * (Real.exp (-β * h) * Real.exp (-β * q)) =
        Real.exp (-β * h) *
          (h * Real.exp (-β * q) + q * Real.exp (-β * q)) := by ring
    _ ≤ Real.exp (-β * h) * (h + 1) := by
      gcongr
      nlinarith
    _ = (h + 1) * Real.exp (-β * h) := by ring

theorem exponentialWeight_momentError_norm_le
    {h β : ℝ} (hh : 0 < h) (hβ : 1 ≤ β) (A η : ℝ → ℂ) (U : Spacetime2)
    (hηbound : ∀ t, ‖η t‖ ≤ 1) (p : ℝ × (ℝ × ℝ)) :
    ‖exponentialWeight β (momentError h A η U) p‖ ≤
      ((h + 1) * Real.exp (-β * h)) *
        (‖A p.1‖ + ‖deriv η p.1‖) * ‖U p‖ := by
  by_cases hfar : p.2.1 ≤ -h
  · have hβ0 : 0 ≤ β := le_trans (by norm_num) hβ
    have hfarLinear := far_linear_exponentialWeight_le hh hβ hfar
    have hfarExp := exponentialWeight_le_at_far_halfspace hβ0 hfar
    have hKExp : Real.exp (β * p.2.1) ≤
        (h + 1) * Real.exp (-β * h) := by
      calc
        Real.exp (β * p.2.1) ≤ Real.exp (-β * h) := hfarExp
        _ ≤ (h + 1) * Real.exp (-β * h) := by
          have hexp0 := Real.exp_pos (-β * h)
          nlinarith
    have hfirst : Real.exp (β * p.2.1) * ‖η p.1‖ * ‖A p.1‖ * |p.2.1| ≤
        ((h + 1) * Real.exp (-β * h)) * ‖A p.1‖ := by
      calc
        Real.exp (β * p.2.1) * ‖η p.1‖ * ‖A p.1‖ * |p.2.1| =
            ‖η p.1‖ * ‖A p.1‖ *
              (|p.2.1| * Real.exp (β * p.2.1)) := by ring
        _ ≤ 1 * ‖A p.1‖ * ((h + 1) * Real.exp (-β * h)) := by
          gcongr
          exact hηbound p.1
        _ = ((h + 1) * Real.exp (-β * h)) * ‖A p.1‖ := by ring
    have hsecond : Real.exp (β * p.2.1) * ‖deriv η p.1‖ ≤
        ((h + 1) * Real.exp (-β * h)) * ‖deriv η p.1‖ := by
      gcongr
    rw [exponentialWeight, momentError, if_pos hfar, norm_mul, Complex.norm_exp]
    simp only [Complex.ofReal_re]
    calc
      Real.exp (β * p.2.1) *
          ‖η p.1 * A p.1 * (p.2.1 : ℂ) * U p +
            Complex.I * deriv η p.1 * U p‖ ≤
          Real.exp (β * p.2.1) *
            (‖η p.1 * A p.1 * (p.2.1 : ℂ) * U p‖ +
              ‖Complex.I * deriv η p.1 * U p‖) := by
        gcongr
        exact norm_add_le _ _
      _ = (Real.exp (β * p.2.1) * ‖η p.1‖ * ‖A p.1‖ * |p.2.1| +
            Real.exp (β * p.2.1) * ‖deriv η p.1‖) * ‖U p‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num
        ring
      _ ≤ (((h + 1) * Real.exp (-β * h)) * ‖A p.1‖ +
            ((h + 1) * Real.exp (-β * h)) * ‖deriv η p.1‖) * ‖U p‖ := by
        gcongr
      _ = ((h + 1) * Real.exp (-β * h)) *
          (‖A p.1‖ + ‖deriv η p.1‖) * ‖U p‖ := by ring
  · rw [exponentialWeight, momentError, if_neg hfar, mul_zero, norm_zero]
    positivity

theorem exponentialWeight_momentError_sectionENorm_le
    {h β : ℝ} (hh : 0 < h) (hβ : 1 ≤ β) (A η : ℝ → ℂ) (U : Spacetime2)
    (hηbound : ∀ t, ‖η t‖ ≤ 1) (t : ℝ) :
    sectionENorm (volume.prod volume) 2
        (exponentialWeight β (momentError h A η U)) t ≤
      ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) *
        (‖A t‖ + ‖deriv η t‖)) *
        sectionENorm (volume.prod volume) 2 U t := by
  let C : ℝ := ((h + 1) * Real.exp (-β * h)) *
    (‖A t‖ + ‖deriv η t‖)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  unfold sectionENorm
  calc
    eLpNorm (fun x => exponentialWeight β (momentError h A η U) (t, x)) 2
        (volume.prod volume) ≤
        eLpNorm (fun x => ((C : ℝ) : ℂ) * U (t, x)) 2
          (volume.prod volume) := by
      apply eLpNorm_mono_enorm
      intro x
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      change ‖exponentialWeight β (momentError h A η U) (t, x)‖ ≤ C * ‖U (t, x)‖
      simpa only [C] using
        (exponentialWeight_momentError_norm_le hh hβ A η U hηbound (t, x))
    _ = ENNReal.ofReal C * eLpNorm (fun x => U (t, x)) 2
        (volume.prod volume) := by
      change eLpNorm (((C : ℝ) : ℂ) • (fun x => U (t, x))) 2
        (volume.prod volume) = _
      rw [eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hC]
    _ = ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) *
          (‖A t‖ + ‖deriv η t‖)) *
        eLpNorm (fun x => U (t, x)) 2 (volume.prod volume) := by rfl

theorem exponentialWeight_momentError_mixed_le
    {h β : ℝ} (hh : 0 < h) (hβ : 1 ≤ β) (A η : ℝ → ℂ) (U : Spacetime2)
    (hA : Integrable A) (hderiv : Integrable (deriv η))
    (hηbound : ∀ t, ‖η t‖ ≤ 1)
    (hU : scalarMixedENorm volume (volume.prod volume) ⊤ 2 U < ⊤) :
    scalarMixedENorm volume (volume.prod volume) 1 2
        (exponentialWeight β (momentError h A η U)) ≤
      ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) *
        ∫ t : ℝ, (‖A t‖ + ‖deriv η t‖)) *
        scalarMixedENorm volume (volume.prod volume) ⊤ 2 U := by
  let M : ℝ≥0∞ := scalarMixedENorm volume (volume.prod volume) ⊤ 2 U
  let K : ℝ := (h + 1) * Real.exp (-β * h)
  let D : ℝ → ℝ := fun t => ‖A t‖ + ‖deriv η t‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : Integrable D := hA.norm.add hderiv.norm
  have hKD : Integrable (fun t => K * D t) := hD.const_mul K
  have hMtop : M ≠ ⊤ := ne_of_lt hU
  have hUae : ∀ᵐ t ∂volume,
      sectionENorm (volume.prod volume) 2 U t ≤ M := by
    have hae := ae_le_eLpNormEssSup
      (f := fun t => sectionENorm (volume.prod volume) 2 U t) (μ := volume)
    simpa only [M, scalarMixedENorm, eLpNorm_exponent_top, enorm_eq_self] using hae
  unfold scalarMixedENorm
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    (∫⁻ t, ‖sectionENorm (volume.prod volume) 2
        (exponentialWeight β (momentError h A η U)) t‖ₑ) ≤
        ∫⁻ t, ENNReal.ofReal (K * D t) * M := by
      apply lintegral_mono_ae
      filter_upwards [hUae] with t ht
      rw [enorm_eq_self]
      calc
        sectionENorm (volume.prod volume) 2
            (exponentialWeight β (momentError h A η U)) t ≤
            ENNReal.ofReal (K * D t) *
              sectionENorm (volume.prod volume) 2 U t := by
          simpa only [K, D] using
            (exponentialWeight_momentError_sectionENorm_le hh hβ A η U hηbound t)
        _ ≤ ENNReal.ofReal (K * D t) * M := mul_le_mul_left' ht _
    _ = (∫⁻ t, ENNReal.ofReal (K * D t)) * M := by
      exact lintegral_mul_const' M (fun t => ENNReal.ofReal (K * D t)) hMtop
    _ = ENNReal.ofReal (∫ t : ℝ, K * D t) * M := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKD]
      filter_upwards [] with t
      exact mul_nonneg hK (by dsimp [D]; positivity)
    _ = ENNReal.ofReal (K * ∫ t : ℝ, D t) * M := by
      rw [integral_const_mul]
    _ = ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) *
          ∫ t : ℝ, (‖A t‖ + ‖deriv η t‖)) *
        scalarMixedENorm volume (volume.prod volume) ⊤ 2 U := by rfl

theorem oneStepCutoffError_eq_momentError_ae
    {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 < h) (Z : Spacetime2)
    (hZ : VanishesAbove B Z) :
    oneStepCutoffError B h a b δ
        (movingGalilean a (oneStepMovingBoundary B h a b δ) Z) =ᵐ[
          volume.prod (volume.prod volume)]
      momentError h (oneStepAcceleration B h a b δ)
        (fun t => (oneStepTimeCutoff a b δ t : ℂ))
        (movingGalilean a (oneStepMovingBoundary B h a b δ) Z) := by
  have hsafe := oneStepMovingGalilean_ae_zero_on_cutoff_deriv
    (B := B) (h := h) (a := a) (b := b) (δ := δ) hδ Z hZ
  filter_upwards [hsafe] with p hp
  rw [momentError, oneStepCutoffError, oneStepTimeCutoff_complex_deriv]
  by_cases hfar : p.2.1 ≤ -h
  · simp only [if_pos hfar, oneStepFarAcceleration]
    ring
  · have hy : -2 * h < p.2.1 := by linarith
    by_cases hderiv : deriv (oneStepTimeCutoff a b δ) p.1 = 0
    · simp [oneStepFarAcceleration, hfar, hderiv]
    · have hzero := hp hderiv hy
      simp [oneStepFarAcceleration, hfar, hzero]

theorem carlemanXNorm_le_scalarMixedL1L2 (J : Set ℝ) (F : Spacetime2)
    (hF : AEStronglyMeasurable F
      ((volume.restrict J).prod (volume.prod volume))) :
    carlemanXNorm J F ≤
      scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2 F := by
  simp [carlemanXNorm, hF]

theorem carlemanXNorm_congr_ae {J : Set ℝ} {F G : Spacetime2}
    (hFG : F =ᵐ[((volume.restrict J).prod (volume.prod volume))] G) :
    carlemanXNorm J F = carlemanXNorm J G := by
  have hmeas : AEStronglyMeasurable F
        ((volume.restrict J).prod (volume.prod volume)) ↔
      AEStronglyMeasurable G
        ((volume.restrict J).prod (volume.prod volume)) := by
    constructor
    · intro h; exact h.congr hFG
    · intro h; exact h.congr hFG.symm
  have hnorm :
      scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2 F =
        scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2 G := by
    unfold scalarMixedENorm sectionENorm
    apply eLpNorm_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hFG] with t ht
    exact eLpNorm_congr_ae ht
  unfold carlemanXNorm
  by_cases hF : AEStronglyMeasurable F
      ((volume.restrict J).prod (volume.prod volume))
  · simp [hF, hmeas.mp hF, hnorm]
  · have hG : ¬ AEStronglyMeasurable G
        ((volume.restrict J).prod (volume.prod volume)) := fun h => hF (hmeas.mpr h)
    simp [hF, hG]

theorem scalarMixedL1Linfty_add_le_of_right_measurable
    (μt : Measure ℝ) (F G : Spacetime2) (hG : Measurable G) :
    scalarMixedENorm μt (volume.prod volume) 1 ⊤ (fun p => F p + G p) ≤
      scalarMixedENorm μt (volume.prod volume) 1 ⊤ F +
        scalarMixedENorm μt (volume.prod volume) 1 ⊤ G := by
  have hsection : Measurable (fun t => sectionENorm (volume.prod volume) ⊤ G t) :=
    measurable_esssup_section μt (volume.prod volume) G hG
  unfold scalarMixedENorm
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm]
  simp only [enorm_eq_self]
  calc
    (∫⁻ t, sectionENorm (volume.prod volume) ⊤ (fun p => F p + G p) t ∂μt) ≤
        ∫⁻ t, (sectionENorm (volume.prod volume) ⊤ F t +
          sectionENorm (volume.prod volume) ⊤ G t) ∂μt := by
      apply lintegral_mono
      intro t
      unfold sectionENorm
      change eLpNorm (fun x => F (t, x) + G (t, x)) ⊤ (volume.prod volume) ≤
        eLpNorm (fun x => F (t, x)) ⊤ (volume.prod volume) +
          eLpNorm (fun x => G (t, x)) ⊤ (volume.prod volume)
      simp only [eLpNorm_exponent_top]
      change eLpNormEssSup
          ((fun x => F (t, x)) + (fun x => G (t, x))) (volume.prod volume) ≤ _
      exact eLpNormEssSup_add_le
    _ = (∫⁻ t, sectionENorm (volume.prod volume) ⊤ F t ∂μt) +
        ∫⁻ t, sectionENorm (volume.prod volume) ⊤ G t ∂μt := by
      exact lintegral_add_right _ hsection

/-- `lem:moment-error`: the far error vanishes in the exponentially weighted
source norm.  The cutoff assumptions state exactly what the proof uses. -/
theorem moment_error (h : ℝ) (hh : 0 < h) (A η : ℝ → ℂ) (U : Spacetime2)
    (hA : Integrable A) (hderiv : Integrable (deriv η))
    (hηmeas : Measurable η)
    (hηbound : ∀ t, ‖η t‖ ≤ 1)
    (hUmeas : AEStronglyMeasurable U (volume.prod (volume.prod volume)))
    (hU : scalarMixedENorm volume (volume.prod volume) ⊤ 2 U < ⊤) :
    Tendsto (fun β : ℝ => carlemanXNorm Set.univ
      (exponentialWeight β (momentError h A η U))) atTop (nhds 0) := by
  let D : ℝ := ∫ t : ℝ, (‖A t‖ + ‖deriv η t‖)
  let M : ℝ≥0∞ := scalarMixedENorm volume (volume.prod volume) ⊤ 2 U
  have hmulTop : Tendsto (fun β : ℝ => β * h) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hh tendsto_id
  have hexp : Tendsto (fun β : ℝ => Real.exp (-β * h)) atTop (nhds 0) := by
    apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmulTop).congr'
    filter_upwards [] with β
    simp only [Function.comp_apply]
    congr 1
    ring
  have hreal : Tendsto
      (fun β : ℝ => ((h + 1) * Real.exp (-β * h)) * D) atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hexp).mul tendsto_const_nhds using 1 <;> ring
  have hofReal : Tendsto
      (fun β : ℝ => ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) * D))
      atTop (nhds 0) := by
    have hx := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    change Tendsto
      (fun β : ℝ => ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) * D))
      atTop (nhds (ENNReal.ofReal 0)) at hx
    simpa only [ENNReal.ofReal_zero] using hx
  have hupper : Tendsto
      (fun β : ℝ => ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) * D) * M)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hofReal (Or.inr (ne_of_lt hU))
  have hUtimeη : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => η p.1)
      (volume.prod (volume.prod volume)) := hηmeas.aestronglyMeasurable.comp_fst
  have hUtimeA : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => A p.1)
      (volume.prod (volume.prod volume)) := hA.1.comp_fst
  have hUtimeDeriv : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) => deriv η p.1)
      (volume.prod (volume.prod volume)) := hderiv.1.comp_fst
  have hy : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) => (p.2.1 : ℂ))
      (volume.prod (volume.prod volume)) :=
    (by fun_prop : Measurable (fun p : ℝ × (ℝ × ℝ) => (p.2.1 : ℂ))).aestronglyMeasurable
  let E : Set (ℝ × (ℝ × ℝ)) := {p | p.2.1 ≤ -h}
  have hE : MeasurableSet E :=
    measurableSet_le (measurable_fst.comp measurable_snd) measurable_const
  have hbase : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        η p.1 * A p.1 * (p.2.1 : ℂ) * U p + Complex.I * deriv η p.1 * U p)
      (volume.prod (volume.prod volume)) :=
    (((hUtimeη.mul hUtimeA).mul hy).mul hUmeas).add
      ((hUtimeDeriv.const_mul Complex.I).mul hUmeas)
  have hmoment : AEStronglyMeasurable (momentError h A η U)
      (volume.prod (volume.prod volume)) := by
    have hind := hbase.indicator hE
    exact hind.congr <| by
      filter_upwards [] with p
      by_cases hp : p.2.1 ≤ -h <;> simp [momentError, E, hp]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    have hmoment' : AEStronglyMeasurable (momentError h A η U)
        ((volume.restrict Set.univ).prod (volume.prod volume)) := by
      simpa only [Measure.restrict_univ] using hmoment
    calc
      carlemanXNorm Set.univ (exponentialWeight β (momentError h A η U)) ≤
          scalarMixedENorm volume (volume.prod volume) 1 2
            (exponentialWeight β (momentError h A η U)) := by
        simpa only [Measure.restrict_univ] using carlemanXNorm_le_scalarMixedL1L2 Set.univ
          (exponentialWeight β (momentError h A η U))
          ((by fun_prop : Measurable (fun p : ℝ × (ℝ × ℝ) =>
            Complex.exp ((β * p.2.1 : ℝ) : ℂ))).aestronglyMeasurable.mul hmoment')
      _ ≤ ENNReal.ofReal (((h + 1) * Real.exp (-β * h)) * D) * M := by
        simpa only [D, M] using
          exponentialWeight_momentError_mixed_le hh hβ A η U hA hderiv hηbound hU

theorem oneStepTimeCutoff_complex_deriv_integrable {a b δ : ℝ} (hδ : 0 < δ) :
    Integrable (deriv (fun t => (oneStepTimeCutoff a b δ t : ℂ))) := by
  have hcont : ContDiff ℝ 1 (fun t => (oneStepTimeCutoff a b δ t : ℂ)) := by
    have hcut : ContDiff ℝ 1 (oneStepTimeCutoff a b δ) :=
      (oneStepTimeCutoff_contDiff a b δ).of_le (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    change ContDiff ℝ 1 (Complex.ofRealCLM ∘ oneStepTimeCutoff a b δ)
    exact Complex.ofRealCLM.contDiff.comp hcut
  exact (hcont.continuous_deriv le_rfl).integrable_of_hasCompactSupport
    (oneStepTimeCutoff_complex_hasCompactSupport hδ).deriv

theorem oneStepTimeCutoff_complex_norm_le_one (a b δ t : ℝ) :
    ‖(oneStepTimeCutoff a b δ t : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (oneStepTimeCutoff_mem_Icc a b δ t).1]
  exact (oneStepTimeCutoff_mem_Icc a b δ t).2

theorem oneStep_momentError_tendsto {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (U : Spacetime2)
    (hUmeas : AEStronglyMeasurable U (volume.prod (volume.prod volume)))
    (hU : scalarMixedENorm volume (volume.prod volume) ⊤ 2 U < ⊤) :
    Tendsto (fun β : ℝ => carlemanXNorm Set.univ
      (exponentialWeight β
        (momentError h (oneStepAcceleration B h a b δ)
          (fun t => (oneStepTimeCutoff a b δ t : ℂ)) U))) atTop (nhds 0) :=
  moment_error h hh _ _ U (oneStepAcceleration_integrable hδ)
    (oneStepTimeCutoff_complex_deriv_integrable hδ)
    (Complex.ofRealCLM.continuous.comp
      (oneStepTimeCutoff_contDiff a b δ).continuous).measurable
    (oneStepTimeCutoff_complex_norm_le_one a b δ) hUmeas hU

/-- `lem:one-slab`: small-potential exponential separation on one slab. -/
theorem one_slab :
  ∃ εstar : ℝ≥0∞, 0 < εstar ∧ ∀ (H : ℝ) (U V R : Spacetime2),
    HasBoundedTimeSupport U → VanishesAbove H U →
    IsWeakSchrodinger2D U (fun p => V p * U p + R p) →
    (∀ β : ℝ, 0 < β →
      carlemanXprimeNorm Set.univ (exponentialWeight β U) < ⊤) →
    carlemanYNorm Set.univ V ≤ εstar →
    Tendsto (fun β : ℝ => carlemanXNorm Set.univ (exponentialWeight β R)) atTop (nhds 0) →
    ∀ᵐ p ∂(volume.prod (volume.prod volume)), 0 < p.2.1 → U p = 0 :=
  exponential_separation

/-- Restrict a spacetime field to a time interval without changing its representative. -/
def restrictTimeField (J : Set ℝ) (F : Spacetime2) : Spacetime2 :=
  (J ×ˢ (Set.univ : Set (ℝ × ℝ))).indicator F

theorem aestronglyMeasurable_of_carlemanXprimeNorm_lt_top
    (J : Set ℝ) (F : Spacetime2) (hF : carlemanXprimeNorm J F < ⊤) :
    AEStronglyMeasurable F
      ((volume.restrict J).prod (volume.prod volume)) := by
  by_contra hn
  simp [carlemanXprimeNorm, hn] at hF

theorem restrictTimeField_aestronglyMeasurable
    (J : Set ℝ) (hJ : MeasurableSet J) (F : Spacetime2)
    (hF : AEStronglyMeasurable F
      ((volume.restrict J).prod (volume.prod volume))) :
    AEStronglyMeasurable (restrictTimeField J F)
      (volume.prod (volume.prod volume)) := by
  unfold restrictTimeField
  rw [aestronglyMeasurable_indicator_iff (hJ.prod MeasurableSet.univ)]
  rwa [← Measure.restrict_prod_eq_prod_univ]

theorem scalarMixedENorm_restrictTimeField (J : Set ℝ) (hJ : MeasurableSet J)
    (p q : ℝ≥0∞) (F : Spacetime2) :
    scalarMixedENorm volume (volume.prod volume) p q (restrictTimeField J F) =
      scalarMixedENorm (volume.restrict J) (volume.prod volume) p q F := by
  unfold scalarMixedENorm
  have hsections :
      (fun t => sectionENorm (volume.prod volume) q (restrictTimeField J F) t) =
        J.indicator (fun t => sectionENorm (volume.prod volume) q F t) := by
    funext t
    by_cases ht : t ∈ J
    · simp [sectionENorm, restrictTimeField, ht]
    · simp [sectionENorm, restrictTimeField, ht]
  rw [hsections, eLpNorm_indicator_eq_eLpNorm_restrict hJ]

theorem restrictTimeField_mixed_finite_of_carlemanXprime
    (J : Set ℝ) (hJ : MeasurableSet J) (F : Spacetime2)
    (hF : carlemanXprimeNorm J F < ⊤) :
    scalarMixedENorm volume (volume.prod volume) ⊤ 2 (restrictTimeField J F) < ⊤ := by
  rw [scalarMixedENorm_restrictTimeField J hJ]
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict J).prod (volume.prod volume)) := by
    by_contra hn
    simp [carlemanXprimeNorm, hn] at hF
  simp only [carlemanXprimeNorm, hmeas, if_true] at hF
  exact hF

theorem carlemanXprimeNorm_restrictTimeField (J : Set ℝ) (hJ : MeasurableSet J)
    (F : Spacetime2) :
    carlemanXprimeNorm J (restrictTimeField J F) = carlemanXprimeNorm J F := by
  have htime : ∀ᵐ t ∂volume.restrict J, t ∈ J := ae_restrict_mem hJ
  have hsections : ∀ᵐ t ∂volume.restrict J,
      sectionENorm (volume.prod volume) 2 (restrictTimeField J F) t =
        sectionENorm (volume.prod volume) 2 F t := by
    filter_upwards [htime] with t ht
    unfold sectionENorm
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp [restrictTimeField, ht]
  have hspace : restrictTimeField J F =ᵐ[
      (volume.restrict J).prod (volume.prod volume)] F := by
    have htimeProd : ∀ᵐ p : ℝ × (ℝ × ℝ)
        ∂((volume.restrict J).prod (volume.prod volume)),
        p.1 ∈ J := by
      rw [Measure.ae_prod_iff_ae_ae (hJ.preimage measurable_fst)]
      filter_upwards [htime] with t ht
      filter_upwards [] with x
      exact ht
    filter_upwards [htimeProd] with p hp
    rcases p with ⟨t, x⟩
    simp [restrictTimeField, hp]
  unfold carlemanXprimeNorm scalarMixedENorm
  have hmeas : AEStronglyMeasurable (restrictTimeField J F)
        ((volume.restrict J).prod (volume.prod volume)) ↔
      AEStronglyMeasurable F
        ((volume.restrict J).prod (volume.prod volume)) := by
    constructor <;> intro h
    · exact h.congr hspace
    · exact h.congr hspace.symm
  by_cases hF : AEStronglyMeasurable F
      ((volume.restrict J).prod (volume.prod volume))
  · have hr := hmeas.mpr hF
    simp only [hF, hr, if_true]
    rw [eLpNorm_congr_ae hsections]
  · have hr : ¬ AEStronglyMeasurable (restrictTimeField J F)
        ((volume.restrict J).prod (volume.prod volume)) := fun h => hF (hmeas.mp h)
    simp [hF, hr]

theorem carlemanXprimeNorm_restrictTimeField_global_lt_top
    (J : Set ℝ) (hJ : MeasurableSet J) (F : Spacetime2)
    (hF : carlemanXprimeNorm J F < ⊤) :
    carlemanXprimeNorm Set.univ (restrictTimeField J F) < ⊤ := by
  have hFmeas := aestronglyMeasurable_of_carlemanXprimeNorm_lt_top J F hF
  have hrmeas : AEStronglyMeasurable (restrictTimeField J F)
      ((volume.restrict Set.univ).prod (volume.prod volume)) := by
    simpa only [Measure.restrict_univ] using
      restrictTimeField_aestronglyMeasurable J hJ F hFmeas
  simp only [carlemanXprimeNorm, hFmeas, if_true] at hF
  rw [carlemanXprimeNorm, if_pos hrmeas]
  simpa only [Measure.restrict_univ,
    scalarMixedENorm_restrictTimeField J hJ] using hF

/-- A jointly measurable field pointwise dominated by a finite-`X'` field
also has finite `X'` gauge. -/
theorem carlemanXprimeNorm_lt_top_of_ae_nnnorm_le
    (J : Set ℝ) (f g : Spacetime2)
    (hf : AEStronglyMeasurable f
      ((volume.restrict J).prod (volume.prod volume)))
    (hg : carlemanXprimeNorm J g < ⊤) (c : NNReal)
    (hfg : ∀ᵐ p ∂((volume.restrict J).prod (volume.prod volume)),
      ‖f p‖₊ ≤ c * ‖g p‖₊) :
    carlemanXprimeNorm J f < ⊤ := by
  have hgmeas := aestronglyMeasurable_of_carlemanXprimeNorm_lt_top J g hg
  have hgscalar :
      scalarMixedENorm (volume.restrict J) (volume.prod volume) ⊤ 2 g < ⊤ := by
    simpa only [carlemanXprimeNorm, hgmeas, if_true] using hg
  have hsections : ∀ᵐ t ∂volume.restrict J,
      sectionENorm (volume.prod volume) 2 f t ≤
        c • sectionENorm (volume.prod volume) 2 g t := by
    have hcurried := Measure.ae_ae_of_ae_prod hfg
    filter_upwards [hcurried] with t ht
    unfold sectionENorm
    simpa only using
      (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul ht 2)
  rw [carlemanXprimeNorm, if_pos hf]
  unfold scalarMixedENorm at hgscalar ⊢
  rw [eLpNorm_exponent_top] at hgscalar ⊢
  refine (eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (f := fun t => sectionENorm (volume.prod volume) 2 f t)
    (g := fun t => sectionENorm (volume.prod volume) 2 g t)
    (c := (c : ℝ≥0∞)) ?_).trans_lt ?_
  · filter_upwards [hsections] with t ht
    simp only [enorm_eq_self]
    change sectionENorm (volume.prod volume) 2 f t ≤
      c • sectionENorm (volume.prod volume) 2 g t
    exact ht
  · simpa only [smul_eq_mul] using
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hgscalar)

theorem oneStepLocalizedMovingGalilean_vanishesAbove
    {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) (Z : Spacetime2)
    (hZ : VanishesAbove B (restrictTimeField (Set.Ioo a b) Z)) :
    VanishesAbove h
      (oneStepLocalizedField a b δ
        (movingGalilean a (oneStepMovingBoundary B h a b δ) Z)) := by
  have hmove := oneStepMovingGalilean_vanishesAbove
    (a := a) (b := b) (δ := δ) hh
    (restrictTimeField (Set.Ioo a b) Z) hZ
  filter_upwards [hmove] with p hp
  intro hy
  by_cases ht : p.1 ∈ Set.Ioo a b
  · have hzero := hp hy
    unfold oneStepLocalizedField
    rw [show movingGalilean a (oneStepMovingBoundary B h a b δ) Z p =
        movingGalilean a (oneStepMovingBoundary B h a b δ)
          (restrictTimeField (Set.Ioo a b) Z) p by
      unfold movingGalilean movingTranslate restrictTimeField
      simp [ht]]
    simp [hzero]
  · simp [oneStepLocalizedField,
      oneStepTimeCutoff_eq_zero_of_notMem_Ioo hδ ht]

theorem oneStep_momentError_restrictTimeField
    {B h a b δ : ℝ} (hδ : 0 < δ) (U : Spacetime2) :
    momentError h (oneStepAcceleration B h a b δ)
        (fun t => (oneStepTimeCutoff a b δ t : ℂ))
        (restrictTimeField (Set.Ioo a b) U) =
      momentError h (oneStepAcceleration B h a b δ)
        (fun t => (oneStepTimeCutoff a b δ t : ℂ)) U := by
  funext p
  by_cases ht : p.1 ∈ Set.Ioo a b
  · simp [momentError, restrictTimeField, ht]
  · have heta : oneStepTimeCutoff a b δ p.1 = 0 := by
      have hor : p.1 ≤ a ∨ b ≤ p.1 := by
        simpa only [Set.mem_Ioo, not_and_or, not_lt] using ht
      rcases hor with hleft | hright
      · exact oneStepTimeCutoff_eq_zero_of_left hδ (by linarith)
      · exact oneStepTimeCutoff_eq_zero_of_right hδ (by linarith)
    have hderiv := oneStepTimeCutoff_deriv_eq_zero_of_notMem_Ioo hδ ht
    by_cases hfar : p.2.1 ≤ -h
    · simp [momentError, hfar, heta, oneStepTimeCutoff_complex_deriv, hderiv]
    · simp [momentError, hfar]

theorem oneStep_restricted_momentError_tendsto
    {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 < h) (U : Spacetime2)
    (hU : carlemanXprimeNorm (Set.Ioo a b) U < ⊤) :
    Tendsto (fun β : ℝ => carlemanXNorm Set.univ
      (exponentialWeight β
        (momentError h (oneStepAcceleration B h a b δ)
          (fun t => (oneStepTimeCutoff a b δ t : ℂ))
          (restrictTimeField (Set.Ioo a b) U)))) atTop (nhds 0) := by
  have hUmeas := aestronglyMeasurable_of_carlemanXprimeNorm_lt_top
    (Set.Ioo a b) U hU
  exact oneStep_momentError_tendsto hδ hh _
    (restrictTimeField_aestronglyMeasurable
      (Set.Ioo a b) measurableSet_Ioo U hUmeas)
    (restrictTimeField_mixed_finite_of_carlemanXprime
      (Set.Ioo a b) measurableSet_Ioo U hU)

theorem oneStepCutoffError_tendsto
    {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 < h) (Z : Spacetime2)
    (hZ : VanishesAbove B Z)
    (hU : carlemanXprimeNorm (Set.Ioo a b)
      (movingGalilean a (oneStepMovingBoundary B h a b δ) Z) < ⊤) :
    Tendsto (fun β : ℝ => carlemanXNorm Set.univ
      (exponentialWeight β
        (oneStepCutoffError B h a b δ
          (movingGalilean a (oneStepMovingBoundary B h a b δ) Z))))
      atTop (nhds 0) := by
  let U := movingGalilean a (oneStepMovingBoundary B h a b δ) Z
  have hmoment := oneStep_restricted_momentError_tendsto
    (B := B) (h := h) (a := a) (b := b) (δ := δ) hδ hh U hU
  rw [oneStep_momentError_restrictTimeField hδ U] at hmoment
  apply hmoment.congr'
  filter_upwards [] with β
  apply carlemanXNorm_congr_ae
  have herr := oneStepCutoffError_eq_momentError_ae
    (B := B) (h := h) (a := a) (b := b) (δ := δ) hδ hh Z hZ
  have herrβ : exponentialWeight β (oneStepCutoffError B h a b δ U) =ᵐ[
      volume.prod (volume.prod volume)]
      exponentialWeight β
        (momentError h (oneStepAcceleration B h a b δ)
          (fun t => (oneStepTimeCutoff a b δ t : ℂ)) U) := by
    filter_upwards [herr] with p hp
    unfold exponentialWeight
    simpa only [U] using
      congrArg (fun z : ℂ => Complex.exp ((β * p.2.1 : ℝ) : ℂ) * z) hp
  simpa only [Measure.restrict_univ] using herrβ.symm

theorem carlemanYNorm_le_scalarMixedL1Linfty (J : Set ℝ) (W : Spacetime2)
    (hW : AEStronglyMeasurable W
      ((volume.restrict J).prod (volume.prod volume))) :
    carlemanYNorm J W ≤
      scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 ⊤ W := by
  simp [carlemanYNorm, hW]

/-- Potential in the localized, moving coordinate frame. -/
def oneStepEffectivePotential (B h a b δ : ℝ) (W : Spacetime2) : Spacetime2 :=
  fun p => restrictTimeField (Set.Ioo a b)
      (movingTranslate (oneStepMovingBoundary B h a b δ) W) p +
    oneStepNearAcceleration B h a b δ p

theorem oneStepEffectivePotential_Y_le
    {B h a b δ : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h)
    (hsep : a + 3 * δ ≤ b - 3 * δ) (W : Spacetime2)
    (hWmeas : AEStronglyMeasurable W
      ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume))) :
    carlemanYNorm Set.univ (oneStepEffectivePotential B h a b δ W) ≤
      scalarMixedENorm (volume.restrict (Set.Ioo a b)) (volume.prod volume) 1 ⊤ W +
        ENNReal.ofReal (3 * oneStepTransitionSecondMass * h ^ 2 / δ) := by
  calc
    carlemanYNorm Set.univ (oneStepEffectivePotential B h a b δ W) ≤
      scalarMixedENorm volume (volume.prod volume) 1 ⊤
          (oneStepEffectivePotential B h a b δ W) := by
      have hmove : AEStronglyMeasurable
          (movingTranslate (oneStepMovingBoundary B h a b δ) W)
          ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)) :=
        (movingTranslate_aestronglyMeasurable_iff (Set.Ioo a b)
          (oneStepMovingBoundary B h a b δ)
          (oneStepMovingBoundary_contDiff B h a b δ).continuous.measurable W).mpr hWmeas
      have hrestrict := restrictTimeField_aestronglyMeasurable
        (Set.Ioo a b) measurableSet_Ioo _ hmove
      have hnear : AEStronglyMeasurable (oneStepNearAcceleration B h a b δ)
          (volume.prod (volume.prod volume)) :=
        (oneStepNearAcceleration_measurable B h a b δ).aestronglyMeasurable
      have hVmeas : AEStronglyMeasurable
          (oneStepEffectivePotential B h a b δ W)
          ((volume.restrict Set.univ).prod (volume.prod volume)) := by
        have hsum : AEStronglyMeasurable
            (restrictTimeField (Set.Ioo a b)
                (movingTranslate (oneStepMovingBoundary B h a b δ) W) +
              oneStepNearAcceleration B h a b δ)
            ((volume.restrict Set.univ).prod (volume.prod volume)) := by
          simpa only [Measure.restrict_univ] using hrestrict.add hnear
        exact hsum.congr <| by
          filter_upwards [] with p
          rfl
      simpa only [oneStepEffectivePotential, Measure.restrict_univ] using
        carlemanYNorm_le_scalarMixedL1Linfty Set.univ
        (oneStepEffectivePotential B h a b δ W) hVmeas
    _ ≤ scalarMixedENorm volume (volume.prod volume) 1 ⊤
          (restrictTimeField (Set.Ioo a b)
            (movingTranslate (oneStepMovingBoundary B h a b δ) W)) +
        scalarMixedENorm volume (volume.prod volume) 1 ⊤
          (oneStepNearAcceleration B h a b δ) := by
      exact scalarMixedL1Linfty_add_le_of_right_measurable volume _ _
        (oneStepNearAcceleration_measurable B h a b δ)
    _ = scalarMixedENorm (volume.restrict (Set.Ioo a b))
          (volume.prod volume) 1 ⊤ W +
        scalarMixedENorm volume (volume.prod volume) 1 ⊤
          (oneStepNearAcceleration B h a b δ) := by
      rw [scalarMixedENorm_restrictTimeField (Set.Ioo a b) measurableSet_Ioo,
        scalarMixedENorm_movingTranslate]
    _ ≤ scalarMixedENorm (volume.restrict (Set.Ioo a b))
          (volume.prod volume) 1 ⊤ W +
        ENNReal.ofReal (3 * oneStepTransitionSecondMass * h ^ 2 / δ) := by
      gcongr
      exact oneStepNearAcceleration_mixed_le_scaled hδ hh hsep

theorem oneStep_pullback_inner_vanishing
    {B h a b δ : ℝ} (hδ : 0 < δ) (Z : Spacetime2)
    (hzero : ∀ᵐ p ∂(volume.prod (volume.prod volume)), 0 < p.2.1 →
      oneStepLocalizedField a b δ
        (movingGalilean a (oneStepMovingBoundary B h a b δ) Z) p = 0) :
    VanishesAbove (B - h)
      (restrictTimeField (Set.Ioo (a + 4 * δ) (b - 4 * δ)) Z) := by
  let w : ℝ → ℝ := oneStepMovingBoundary B h a b δ
  have hwneg : Measurable (fun t => -w t) :=
    (oneStepMovingBoundary_contDiff B h a b δ).continuous.measurable.neg
  have hpull := movingSpatialMap_ae hwneg hzero
  filter_upwards [hpull] with p hp
  intro hx
  by_cases ht : p.1 ∈ Set.Ioo (a + 4 * δ) (b - 4 * δ)
  · have hwinner : w p.1 = B - h := by
      exact oneStepMovingBoundary_eq_inner hδ (by linarith [ht.1]) (by linarith [ht.2])
    have hypos : 0 < p.2.1 + (-w p.1) := by
      rw [hwinner]
      linarith
    have hloc := hp hypos
    have hη : oneStepTimeCutoff a b δ p.1 = 1 :=
      (oneStep_inner_identities hδ ht).2
    have hphase : Complex.exp (-Complex.I *
        ((((deriv w p.1) / 2) * (p.2.1 + -w p.1) +
          ∫ s in a..p.1, ((deriv w s) / 2) ^ 2 : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have hZp : Z p = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hphase
      simpa only [movingSpatialMap, oneStepLocalizedField, hη, Complex.ofReal_one,
        one_mul, movingGalilean, movingTranslate, w, neg_add_cancel_right,
        Prod.eta] using hloc
    simpa [restrictTimeField, ht, hZp]
  · simp [restrictTimeField, ht]

theorem weakPotentialEquation_mono {J K : Set ℝ} {Z W : Spacetime2}
    (hKJ : K ⊆ J) (h : IsWeakPotentialEquation J Z W) :
    IsWeakPotentialEquation K Z W := by
  intro Ψ hΨsmooth hΨcompact hΨ
  exact h Ψ hΨsmooth hΨcompact (fun p hp => hKJ (hΨ p hp))

theorem carlemanXprimeNorm_mono {J K : Set ℝ} (hKJ : K ⊆ J)
    (Z : Spacetime2) : carlemanXprimeNorm K Z ≤ carlemanXprimeNorm J Z := by
  unfold carlemanXprimeNorm scalarMixedENorm
  by_cases hJ : AEStronglyMeasurable Z
      ((volume.restrict J).prod (volume.prod volume))
  · have hmeasure :
        ((volume : Measure ℝ).restrict K).prod
            ((volume : Measure ℝ).prod (volume : Measure ℝ)) ≤
          ((volume : Measure ℝ).restrict J).prod
            ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      Measure.prod_mono (Measure.restrict_mono hKJ le_rfl) le_rfl
    have hK : AEStronglyMeasurable Z
        ((volume.restrict K).prod (volume.prod volume)) :=
      hJ.mono_ac (Measure.absolutelyContinuous_of_le hmeasure)
    simp only [hJ, hK, if_true]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hKJ le_rfl)
  · simp [hJ]

theorem scalarMixedL1Linfty_mono {J K : Set ℝ} (hKJ : K ⊆ J)
    (W : Spacetime2) :
    scalarMixedENorm (volume.restrict K) (volume.prod volume) 1 ⊤ W ≤
      scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 ⊤ W := by
  unfold scalarMixedENorm
  exact eLpNorm_mono_measure _ (Measure.restrict_mono hKJ le_rfl)

theorem vanishesAbove_restrict_mono {J K : Set ℝ} (hKJ : K ⊆ J)
    {B : ℝ} {Z : Spacetime2}
    (h : VanishesAbove B (restrictTimeField J Z)) :
    VanishesAbove B (restrictTimeField K Z) := by
  filter_upwards [h] with p hp
  intro hB
  by_cases hpt : p.1 ∈ K
  · have hpJ : p.1 ∈ J := hKJ hpt
    have hz : Z p = 0 := by
      have := hp hB
      simpa [restrictTimeField, hpJ] using this
    simpa [restrictTimeField, hpt, hz]
  · simp [restrictTimeField, hpt]

theorem exists_oneStepSmallnessConstant (εstar : ℝ≥0∞) (hεstar : 0 < εstar) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ (a b δ h B : ℝ),
      0 < δ → δ < (b - a) / 8 → 0 < h → h ≤ c0 * Real.sqrt δ →
      ∀ W : Spacetime2,
        AEStronglyMeasurable W
          ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)) →
        scalarMixedENorm (volume.restrict (Set.Ioo a b))
            (volume.prod volume) 1 ⊤ W ≤ ENNReal.ofReal c0 →
        carlemanYNorm Set.univ (oneStepEffectivePotential B h a b δ W) ≤ εstar := by
  by_cases hεtop : εstar = ⊤
  · refine ⟨1, by norm_num, ?_⟩
    intro a b δ h B hδ hδsmall hh hscale W hWmeas hW
    rw [hεtop]
    exact le_top
  · let K : ℝ := 3 * oneStepTransitionSecondMass
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (by norm_num) oneStepTransitionSecondMass_nonneg
    have hεreal : 0 < εstar.toReal :=
      ENNReal.toReal_pos (ne_of_gt hεstar) hεtop
    let c0 : ℝ := min 1 (εstar.toReal / (2 * (1 + K)))
    have hdenom : 0 < 2 * (1 + K) := by positivity
    have hc0 : 0 < c0 := by
      dsimp [c0]
      exact lt_min (by norm_num) (div_pos hεreal hdenom)
    refine ⟨c0, hc0, ?_⟩
    intro a b δ h B hδ hδsmall hh hscale W hWmeas hW
    have hsep : a + 3 * δ ≤ b - 3 * δ := by linarith
    have hc01 : c0 ≤ 1 := min_le_left _ _
    have hc0frac : c0 ≤ εstar.toReal / (2 * (1 + K)) := min_le_right _ _
    have hsqrt0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
    have hsquare : h ^ 2 ≤ c0 ^ 2 * δ := by
      have hsq := (sq_le_sq₀ hh.le (mul_nonneg hc0.le hsqrt0)).2 hscale
      rw [mul_pow, Real.sq_sqrt hδ.le] at hsq
      exact hsq
    have hratio : h ^ 2 / δ ≤ c0 ^ 2 := by
      apply (div_le_iff₀ hδ).2
      nlinarith
    have hnearReal : 3 * oneStepTransitionSecondMass * h ^ 2 / δ ≤ K * c0 ^ 2 := by
      change K * h ^ 2 / δ ≤ K * c0 ^ 2
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hratio hK
    have htotalReal : c0 + K * c0 ^ 2 ≤ εstar.toReal := by
      have hquad : K * c0 ^ 2 ≤ K * c0 := by
        gcongr
        nlinarith
      have hhalf : c0 * (1 + K) ≤ εstar.toReal / 2 := by
        calc
          c0 * (1 + K) ≤
              (εstar.toReal / (2 * (1 + K))) * (1 + K) := by gcongr
          _ = εstar.toReal / 2 := by field_simp
      nlinarith
    calc
      carlemanYNorm Set.univ (oneStepEffectivePotential B h a b δ W) ≤
          scalarMixedENorm (volume.restrict (Set.Ioo a b))
              (volume.prod volume) 1 ⊤ W +
            ENNReal.ofReal (3 * oneStepTransitionSecondMass * h ^ 2 / δ) :=
        oneStepEffectivePotential_Y_le hδ hh.le hsep W hWmeas
      _ ≤ ENNReal.ofReal c0 + ENNReal.ofReal (K * c0 ^ 2) := by
        exact add_le_add hW (ENNReal.ofReal_le_ofReal hnearReal)
      _ = ENNReal.ofReal (c0 + K * c0 ^ 2) := by
        rw [ENNReal.ofReal_add hc0.le (mul_nonneg hK (sq_nonneg c0))]
      _ ≤ εstar := by
        rw [ENNReal.ofReal_le_iff_le_toReal hεtop]
        exact htotalReal

/-- All quantitative and geometric parts of one-step propagation.  The sole
extra premise is the global weak equation obtained by the Galilean
change-of-variables and multiplication by the smooth time cutoff. -/
theorem one_step_propagation_of_localized_equation :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ (a b δ h B : ℝ), a < b →
      0 < δ → δ < (b - a) / 8 → 0 < h → h ≤ c0 * Real.sqrt δ →
      ∀ (Z W : Spacetime2), IsWeakPotentialEquation (Set.Ioo a b) Z W →
        carlemanXprimeNorm (Set.Ioo a b) Z < ⊤ →
        AEStronglyMeasurable W
          ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)) →
        scalarMixedENorm (volume.restrict (Set.Ioo a b)) (volume.prod volume) 1 ⊤ W ≤
          ENNReal.ofReal c0 →
        VanishesAbove B (restrictTimeField (Set.Ioo a b) Z) →
        IsWeakSchrodinger2D
          (oneStepLocalizedField a b δ
            (movingGalilean a (oneStepMovingBoundary B h a b δ)
              (restrictTimeField (Set.Ioo a b) Z)))
          (fun p => oneStepEffectivePotential B h a b δ W p *
              oneStepLocalizedField a b δ
                (movingGalilean a (oneStepMovingBoundary B h a b δ)
                  (restrictTimeField (Set.Ioo a b) Z)) p +
            oneStepCutoffError B h a b δ
              (movingGalilean a (oneStepMovingBoundary B h a b δ)
                (restrictTimeField (Set.Ioo a b) Z)) p) →
        VanishesAbove (B - h)
          (restrictTimeField (Set.Ioo (a + 4 * δ) (b - 4 * δ)) Z) := by
  obtain ⟨εstar, hεstar, hslab⟩ := one_slab
  obtain ⟨c0, hc0, hsmall⟩ := exists_oneStepSmallnessConstant εstar hεstar
  refine ⟨c0, hc0, ?_⟩
  intro a b δ h B hab hδ hδsmall hh hscale Z W hZW hZnorm hWmeas hW hZ hglobal
  let J : Set ℝ := Set.Ioo a b
  let Zr : Spacetime2 := restrictTimeField J Z
  let U : Spacetime2 := movingGalilean a (oneStepMovingBoundary B h a b δ) Zr
  let Y : Spacetime2 := oneStepLocalizedField a b δ U
  let V : Spacetime2 := oneStepEffectivePotential B h a b δ W
  let R : Spacetime2 := oneStepCutoffError B h a b δ U
  have habSupport : a + δ < b - δ := by linarith
  have hYtime : HasBoundedTimeSupport Y :=
    oneStepLocalizedField_hasBoundedTimeSupport hδ habSupport U
  have hUzero : VanishesAbove h U := by
    exact oneStepMovingGalilean_vanishesAbove hh.le Zr hZ
  have hYzero : VanishesAbove h Y := by
    filter_upwards [hUzero] with p hp
    intro hyp
    simp [Y, oneStepLocalizedField, hp hyp]
  have hVsmall : carlemanYNorm Set.univ V ≤ εstar := by
    exact hsmall a b δ h B hδ hδsmall hh hscale W hWmeas hW
  have hUnorm : carlemanXprimeNorm J U < ⊤ := by
    dsimp [U, Zr, J]
    rw [carlemanXprimeNorm_movingGalilean (Set.Ioo a b) a
      (oneStepMovingBoundary B h a b δ)
      ((oneStepMovingBoundary_contDiff B h a b δ).of_le (by norm_num)),
      carlemanXprimeNorm_restrictTimeField (Set.Ioo a b) measurableSet_Ioo]
    exact hZnorm
  have hUrestrict : restrictTimeField J U = U := by
    funext p
    by_cases ht : p.1 ∈ J
    · simp [restrictTimeField, ht]
    · simp [restrictTimeField, U, Zr, movingGalilean, movingTranslate, ht]
  have hUglobal : carlemanXprimeNorm Set.univ U < ⊤ := by
    have hr := carlemanXprimeNorm_restrictTimeField_global_lt_top
      J measurableSet_Ioo U hUnorm
    rw [hUrestrict] at hr
    exact hr
  have hUmeas : AEStronglyMeasurable U
      ((volume.restrict Set.univ).prod (volume.prod volume)) :=
    aestronglyMeasurable_of_carlemanXprimeNorm_lt_top Set.univ U hUglobal
  have hYmeas : AEStronglyMeasurable Y
      ((volume.restrict Set.univ).prod (volume.prod volume)) := by
    have hcut : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        (oneStepTimeCutoff a b δ p.1 : ℂ)) :=
      Complex.ofRealCLM.continuous.measurable.comp
        ((oneStepTimeCutoff_contDiff a b δ).continuous.measurable.comp measurable_fst)
    exact hcut.aestronglyMeasurable.mul hUmeas
  have hYdom : ∀ᵐ p ∂((volume.restrict Set.univ).prod (volume.prod volume)),
      ‖Y p‖₊ ≤ (1 : NNReal) * ‖U p‖₊ := by
    filter_upwards [] with p
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, NNReal.coe_one, one_mul]
    change ‖Y p‖ ≤ ‖U p‖
    have hcut := oneStepTimeCutoff_mem_Icc a b δ p.1
    dsimp [Y, oneStepLocalizedField]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcut.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hcut.2
  have hYglobal : carlemanXprimeNorm Set.univ Y < ⊤ :=
    carlemanXprimeNorm_lt_top_of_ae_nnnorm_le Set.univ Y U hYmeas hUglobal 1 hYdom
  have hYweighted : ∀ β : ℝ, 0 < β →
      carlemanXprimeNorm Set.univ (exponentialWeight β Y) < ⊤ := by
    intro β hβ
    let cβ : NNReal := ⟨Real.exp (β * h), (Real.exp_pos _).le⟩
    have hweightMeas : AEStronglyMeasurable (exponentialWeight β Y)
        ((volume.restrict Set.univ).prod (volume.prod volume)) := by
      have hm : Measurable (fun p : ℝ × (ℝ × ℝ) =>
          Complex.exp ((β * p.2.1 : ℝ) : ℂ)) := by fun_prop
      exact hm.aestronglyMeasurable.mul hYmeas
    have hdom : ∀ᵐ p ∂((volume.restrict Set.univ).prod (volume.prod volume)),
        ‖exponentialWeight β Y p‖₊ ≤ cβ * ‖Y p‖₊ := by
      have hYzero' : ∀ᵐ p ∂((volume.restrict Set.univ).prod (volume.prod volume)),
          h < p.2.1 → Y p = 0 := by
        simpa only [Measure.restrict_univ] using
          (show ∀ᵐ p ∂(volume.prod (volume.prod volume)),
            h < p.2.1 → Y p = 0 from hYzero)
      filter_upwards [hYzero'] with p hp
      by_cases hph : h < p.2.1
      · have hz : Y p = 0 := hp hph
        simp [exponentialWeight, hz]
      · apply NNReal.coe_le_coe.mp
        simp only [NNReal.coe_mul]
        change ‖exponentialWeight β Y p‖ ≤ Real.exp (β * h) * ‖Y p‖
        unfold exponentialWeight
        rw [norm_mul, Complex.norm_exp]
        simp only [Complex.ofReal_re]
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
            (le_of_not_gt hph) hβ.le)) (norm_nonneg _)
    exact carlemanXprimeNorm_lt_top_of_ae_nnnorm_le Set.univ
      (exponentialWeight β Y) Y hweightMeas hYglobal cβ hdom
  have hRdecay : Tendsto (fun β : ℝ =>
      carlemanXNorm Set.univ (exponentialWeight β R)) atTop (nhds 0) := by
    exact oneStepCutoffError_tendsto hδ hh Zr hZ hUnorm
  have hpositive : ∀ᵐ p ∂(volume.prod (volume.prod volume)),
      0 < p.2.1 → Y p = 0 := by
    apply hslab h Y V R hYtime hYzero
    · simpa only [Y, V, R, U, Zr, J] using hglobal
    · exact hYweighted
    · exact hVsmall
    · exact hRdecay
  have hpull : VanishesAbove (B - h)
      (restrictTimeField (Set.Ioo (a + 4 * δ) (b - 4 * δ)) Zr) := by
    exact oneStep_pullback_inner_vanishing hδ Zr hpositive
  filter_upwards [hpull] with p hp
  intro hBp
  by_cases ht : p.1 ∈ Set.Ioo (a + 4 * δ) (b - 4 * δ)
  · have htJ : p.1 ∈ J := by
      dsimp [J]
      constructor <;> linarith [ht.1, ht.2]
    have hz := hp hBp
    simpa [restrictTimeField, Zr, ht, htJ] using hz
  · simp [restrictTimeField, ht]

lemma oneStepTimeCutoff_tsupport_subset {a b δ : ℝ} (hδ : 0 < δ) :
    tsupport (oneStepTimeCutoff a b δ) ⊆ Set.Icc (a + δ) (b - δ) := by
  apply closure_minimal
  · intro t ht
    by_contra hnot
    have hor : t < a + δ ∨ b - δ < t := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hnot
    rcases hor with hleft | hright
    · exact ht (oneStepTimeCutoff_eq_zero_of_left hδ hleft.le)
    · exact ht (oneStepTimeCutoff_eq_zero_of_right hδ hright.le)
  · exact isClosed_Icc

lemma oneStepTimeCutoff_complex_tsupport_subset {a b δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun t => (oneStepTimeCutoff a b δ t : ℂ)) ⊆ Set.Icc (a + δ) (b - δ) := by
  refine (tsupport_comp_subset (f := oneStepTimeCutoff a b δ)
    (g := fun x : ℝ => (x : ℂ)) (by norm_num)).trans ?_
  exact oneStepTimeCutoff_tsupport_subset hδ

lemma weakSchrodinger2D_congr_ae {U U' R R' : Spacetime2}
    (h : IsWeakSchrodinger2D U R)
    (hU : U =ᵐ[volume.prod (volume.prod volume)] U')
    (hR : R =ᵐ[volume.prod (volume.prod volume)] R') :
    IsWeakSchrodinger2D U' R' := by
  intro Ψ hΨ hΨc
  obtain ⟨hUΨ, hUadj, hRΨ, heq⟩ := h Ψ hΨ hΨc
  have hUΨeq : (fun p => U p * Ψ p) =ᵐ[volume.prod (volume.prod volume)]
      (fun p => U' p * Ψ p) := by
    filter_upwards [hU] with p hp
    rw [hp]
  have hUadjeq : (fun p => U p * schrodinger2DAdjointTest Ψ p) =ᵐ[
      volume.prod (volume.prod volume)]
      (fun p => U' p * schrodinger2DAdjointTest Ψ p) :=
    by
      filter_upwards [hU] with p hp
      rw [hp]
  have hRΨeq : (fun p => R p * Ψ p) =ᵐ[volume.prod (volume.prod volume)]
      (fun p => R' p * Ψ p) := by
    filter_upwards [hR] with p hp
    rw [hp]
  refine ⟨hUΨ.congr hUΨeq, hUadj.congr hUadjeq, hRΨ.congr hRΨeq, ?_⟩
  calc
    (∫ p, U' p * schrodinger2DAdjointTest Ψ p
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, U p * schrodinger2DAdjointTest Ψ p
        ∂(volume.prod (volume.prod volume)) := integral_congr_ae hUadjeq.symm
    _ = ∫ p, R p * Ψ p ∂(volume.prod (volume.prod volume)) := heq
    _ = ∫ p, R' p * Ψ p ∂(volume.prod (volume.prod volume)) :=
      integral_congr_ae hRΨeq

lemma oneStep_acceleration_split_at {B h a b δ : ℝ} {U : Spacetime2}
    {p : ℝ × (ℝ × ℝ)} (hsupport : h < p.2.1 → U p = 0) :
    oneStepAcceleration B h a b δ p.1 * (p.2.1 : ℂ) * U p =
      oneStepNearAcceleration B h a b δ p * U p +
        oneStepFarAcceleration B h a b δ p * U p := by
  by_cases hfar : p.2.1 ≤ -h
  · simp [oneStepNearAcceleration, oneStepFarAcceleration, hfar]
  · by_cases hnear : p.2.1 ≤ h
    · have hlower : -h < p.2.1 := lt_of_not_ge hfar
      simp [oneStepNearAcceleration, oneStepFarAcceleration, hfar, hnear, hlower]
    · have hzero : U p = 0 := hsupport (lt_of_not_ge hnear)
      simp [hzero]

set_option maxHeartbeats 2000000 in
lemma oneStep_localized_equation
    (a b δ h B : ℝ) (hab : a < b) (hδ : 0 < δ)
    (hδsmall : δ < (b - a) / 8) (hh : 0 < h)
    (Z W : Spacetime2) (hZW : IsWeakPotentialEquation (Set.Ioo a b) Z W)
    (hZ : VanishesAbove B (restrictTimeField (Set.Ioo a b) Z)) :
    IsWeakSchrodinger2D
      (oneStepLocalizedField a b δ
        (movingGalilean a (oneStepMovingBoundary B h a b δ)
          (restrictTimeField (Set.Ioo a b) Z)))
      (fun p => oneStepEffectivePotential B h a b δ W p *
          oneStepLocalizedField a b δ
            (movingGalilean a (oneStepMovingBoundary B h a b δ)
              (restrictTimeField (Set.Ioo a b) Z)) p +
        oneStepCutoffError B h a b δ
          (movingGalilean a (oneStepMovingBoundary B h a b δ)
            (restrictTimeField (Set.Ioo a b) Z)) p) := by
  let J : Set ℝ := Set.Ioo a b
  let w : ℝ → ℝ := oneStepMovingBoundary B h a b δ
  let η : ℝ → ℂ := fun t => (oneStepTimeCutoff a b δ t : ℂ)
  let Zr : Spacetime2 := restrictTimeField J Z
  let U0 : Spacetime2 := movingGalilean a w Z
  let U : Spacetime2 := movingGalilean a w Zr
  let V0 : Spacetime2 := fun p => W (p.1, (p.2.1 + w p.1, p.2.2)) +
    (((iteratedDeriv 2 w p.1 / 2) * p.2.1 : ℝ) : ℂ)
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    exact oneStepMovingBoundary_contDiff B h a b δ
  have hmove : IsWeakPotentialEquation J U0 V0 := by
    exact moving_galilean_weak_equation J a w hw Z W hZW
  have hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := by
    exact Complex.ofRealCLM.contDiff.comp (oneStepTimeCutoff_contDiff a b δ)
  have hηJ : ∀ t ∈ tsupport η, t ∈ J := by
    intro t ht
    have htIcc : t ∈ Set.Icc (a + δ) (b - δ) :=
      oneStepTimeCutoff_complex_tsupport_subset hδ ht
    rcases htIcc with ⟨htl, htr⟩
    dsimp [J]
    constructor <;> linarith
  have hηdJ : ∀ t ∈ tsupport (deriv η), t ∈ J := by
    intro t ht
    exact hηJ t (tsupport_deriv_subset ht)
  have hraw : IsWeakSchrodinger2D (timeMultiplier η U0)
      (fun p => η p.1 * (V0 p * U0 p) + Complex.I * deriv η p.1 * U0 p) := by
    exact weakSchrodinger2D_timeMultiplier hmove η hη hηJ hηdJ
  have hfield : timeMultiplier η U0 =
      oneStepLocalizedField a b δ U := by
    funext p
    by_cases ht : p.1 ∈ J
    · simp [timeMultiplier, oneStepLocalizedField, η, U0, U, Zr,
        movingGalilean, movingTranslate, restrictTimeField, ht]
    · have hηzero : oneStepTimeCutoff a b δ p.1 = 0 := by
        exact oneStepTimeCutoff_eq_zero_of_notMem_Ioo hδ ht
      simp [timeMultiplier, oneStepLocalizedField, η, hηzero]
  have hUzero : VanishesAbove h U := by
    exact oneStepMovingGalilean_vanishesAbove hh.le Zr hZ
  have hsource : (fun p => η p.1 * (V0 p * U0 p) +
      Complex.I * deriv η p.1 * U0 p) =ᵐ[volume.prod (volume.prod volume)]
      (fun p => oneStepEffectivePotential B h a b δ W p *
          oneStepLocalizedField a b δ U p + oneStepCutoffError B h a b δ U p) := by
    filter_upwards [hUzero] with p hp
    by_cases ht : p.1 ∈ J
    · have hUeq : U0 p = U p := by
        simp [U0, U, Zr, movingGalilean, movingTranslate, restrictTimeField, ht]
      have hpProd : p ∈ Set.Ioo a b ×ˢ (Set.univ : Set (ℝ × ℝ)) :=
        ⟨ht, Set.mem_univ p.2⟩
      have hacc : ((((iteratedDeriv 2 w p.1 / 2) * p.2.1 : ℝ) : ℂ)) =
          oneStepAcceleration B h a b δ p.1 * (p.2.1 : ℂ) := by
        dsimp [w]
        unfold oneStepAcceleration
        push_cast
        ring
      have hsplit := oneStep_acceleration_split_at
        (B := B) (h := h) (a := a) (b := b) (δ := δ) (U := U) (p := p) hp
      rw [hUeq]
      dsimp [V0]
      rw [hacc]
      rw [add_mul]
      rw [hsplit]
      rw [oneStepTimeCutoff_complex_deriv]
      dsimp [η, V0, J]
      simp only [oneStepEffectivePotential, restrictTimeField, ht,
        oneStepLocalizedField, oneStepCutoffError, movingTranslate, w]
      rw [Set.indicator_of_mem hpProd]
      unfold movingTranslate
      ring
    · have hηzero : oneStepTimeCutoff a b δ p.1 = 0 :=
        oneStepTimeCutoff_eq_zero_of_notMem_Ioo hδ ht
      have hηdzero : deriv (oneStepTimeCutoff a b δ) p.1 = 0 :=
        oneStepTimeCutoff_deriv_eq_zero_of_notMem_Ioo hδ ht
      rw [oneStepTimeCutoff_complex_deriv]
      simp [η, hηzero, hηdzero, oneStepLocalizedField, oneStepCutoffError]
  rw [hfield] at hraw
  exact weakSchrodinger2D_congr_ae hraw (Filter.Eventually.of_forall fun _ => rfl) hsource

/-- `lem:one-step-propagation`: move a half-space boundary by one quantitative step. -/
lemma one_step_propagation :
  ∃ c0 : ℝ, 0 < c0 ∧ ∀ (a b δ h B : ℝ), a < b →
    0 < δ → δ < (b - a) / 8 → 0 < h → h ≤ c0 * Real.sqrt δ →
    ∀ (Z W : Spacetime2), IsWeakPotentialEquation (Set.Ioo a b) Z W →
      carlemanXprimeNorm (Set.Ioo a b) Z < ⊤ →
      AEStronglyMeasurable W
        ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)) →
      scalarMixedENorm (volume.restrict (Set.Ioo a b)) (volume.prod volume) 1 ⊤ W ≤
        ENNReal.ofReal c0 →
      VanishesAbove B (restrictTimeField (Set.Ioo a b) Z) →
      VanishesAbove (B - h) (restrictTimeField (Set.Ioo (a + 4 * δ) (b - 4 * δ)) Z) := by
  obtain ⟨c0, hc0, hconditional⟩ := one_step_propagation_of_localized_equation
  refine ⟨c0, hc0, ?_⟩
  intro a b δ h B hab hδ hδsmall hh hscale Z W hZW hZnorm hWmeas hW hZ
  apply hconditional a b δ h B hab hδ hδsmall hh hscale Z W hZW hZnorm
    hWmeas hW hZ
  exact oneStep_localized_equation a b δ h B hab hδ hδsmall hh Z W hZW hZ
private theorem one_step_iterate (c0 : ℝ) (hc0 : 0 < c0)
    (hstep : ∀ (a b δ h B : ℝ), a < b →
      0 < δ → δ < (b - a) / 8 → 0 < h → h ≤ c0 * Real.sqrt δ →
      ∀ (Z W : Spacetime2), IsWeakPotentialEquation (Set.Ioo a b) Z W →
        carlemanXprimeNorm (Set.Ioo a b) Z < ⊤ →
        AEStronglyMeasurable W
          ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)) →
        scalarMixedENorm (volume.restrict (Set.Ioo a b)) (volume.prod volume) 1 ⊤ W ≤
          ENNReal.ofReal c0 →
        VanishesAbove B (restrictTimeField (Set.Ioo a b) Z) →
        VanishesAbove (B - h)
          (restrictTimeField (Set.Ioo (a + 4 * δ) (b - 4 * δ)) Z))
    (a b δ h B : ℝ) (N : ℕ) (hδ : 0 < δ) (hh : 0 < h)
    (hhc : h ≤ c0 * Real.sqrt δ)
    (hinterval : ∀ k : ℕ, k < N → a + 4 * (k : ℝ) * δ < b - 4 * (k : ℝ) * δ)
    (hδsmall : ∀ k : ℕ, k < N →
      δ < ((b - 4 * (k : ℝ) * δ) - (a + 4 * (k : ℝ) * δ)) / 8)
    (Z W : Spacetime2) (heq : IsWeakPotentialEquation (Set.Ioo a b) Z W)
    (hZ : carlemanXprimeNorm (Set.Ioo a b) Z < ⊤)
    (hWmeas : AEStronglyMeasurable W
      ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)))
    (hW : scalarMixedENorm (volume.restrict (Set.Ioo a b))
      (volume.prod volume) 1 ⊤ W ≤ ENNReal.ofReal c0)
    (hzero : VanishesAbove B (restrictTimeField (Set.Ioo a b) Z)) :
    VanishesAbove (B - (N : ℝ) * h)
      (restrictTimeField
        (Set.Ioo (a + 4 * (N : ℝ) * δ) (b - 4 * (N : ℝ) * δ)) Z) := by
  have hiter : ∀ k : ℕ, k ≤ N →
      VanishesAbove (B - (k : ℝ) * h)
        (restrictTimeField
          (Set.Ioo (a + 4 * (k : ℝ) * δ) (b - 4 * (k : ℝ) * δ)) Z) := by
    intro k hk
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
        have hkN : k < N := Nat.lt_of_succ_le hk
        have hk_le : k ≤ N := Nat.le_of_lt hkN
        have hsub : Set.Ioo (a + 4 * (k : ℝ) * δ) (b - 4 * (k : ℝ) * δ) ⊆
            Set.Ioo a b := by
          intro t ht
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          rcases ht with ⟨htl, htr⟩
          constructor <;> nlinarith [mul_nonneg hk0 (le_of_lt hδ)]
        have hnext := hstep
          (a + 4 * (k : ℝ) * δ) (b - 4 * (k : ℝ) * δ) δ h
          (B - (k : ℝ) * h) (hinterval k hkN) hδ (hδsmall k hkN) hh hhc Z W
          (weakPotentialEquation_mono hsub heq)
          ((carlemanXprimeNorm_mono hsub Z).trans_lt hZ)
          (hWmeas.mono_ac (Measure.absolutelyContinuous_of_le
            (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)))
          ((scalarMixedL1Linfty_mono hsub W).trans hW) (ih hk_le)
        convert hnext using 1 <;> push_cast <;> ring
  exact hiter N le_rfl

/-- Iterating the quantitative step annihilates a solution on the middle
three quarters of any interval on which the first `Y` summand is small. -/
theorem halfspace_small_L1Linfty :
  ∃ c0 : ℝ, 0 < c0 ∧ ∀ (a b B : ℝ) (Z W : Spacetime2), a < b →
    IsWeakPotentialEquation (Set.Ioo a b) Z W →
    carlemanXprimeNorm (Set.Ioo a b) Z < ⊤ →
    AEStronglyMeasurable W
      ((volume.restrict (Set.Ioo a b)).prod (volume.prod volume)) →
    scalarMixedENorm (volume.restrict (Set.Ioo a b)) (volume.prod volume) 1 ⊤ W ≤
      ENNReal.ofReal c0 →
    VanishesAbove B (restrictTimeField (Set.Ioo a b) Z) →
    ∀ᵐ p ∂((volume.restrict
      (Set.Ioo (a + (b - a) / 8) (b - (b - a) / 8))).prod (volume.prod volume)),
      Z p = 0 := by
  obtain ⟨c0, hc0, hstep⟩ := one_step_propagation
  refine ⟨c0, hc0, ?_⟩
  intro a b B Z W hab heq hZ hWmeas hW hzero
  let J0 : Set ℝ := Set.Ioo a b
  let Jmid : Set ℝ := Set.Ioo (a + (b - a) / 8) (b - (b - a) / 8)
  have hL : 0 < b - a := sub_pos.mpr hab
  have hvanish : ∀ N : ℕ, 0 < N →
      VanishesAbove
        (B - (N : ℝ) * ((c0 / 2) * Real.sqrt ((b - a) / (32 * (N : ℝ)))))
        (restrictTimeField Jmid Z) := by
    intro N hN
    let δ : ℝ := (b - a) / (32 * (N : ℝ))
    let h : ℝ := (c0 / 2) * Real.sqrt δ
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hδ : 0 < δ := div_pos hL (by positivity)
    have hh : 0 < h := mul_pos (by positivity) (Real.sqrt_pos.2 hδ)
    have hδle : δ ≤ (b - a) / 32 := by
      rw [show δ = (b - a) / (32 * (N : ℝ)) by rfl]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * (N : ℝ))).2
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hmul := mul_le_mul_of_nonneg_left hN1 hL.le
      calc
        b - a ≤ (b - a) * (N : ℝ) := by simpa using hmul
        _ = (b - a) / 32 * (32 * (N : ℝ)) := by ring
    have hshift : ∀ k : ℕ, k ≤ N →
        0 ≤ 4 * (k : ℝ) * δ ∧ 4 * (k : ℝ) * δ ≤ (b - a) / 8 := by
      intro k hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
      constructor
      · positivity
      · rw [show 4 * (k : ℝ) * δ =
            ((k : ℝ) / (N : ℝ)) * ((b - a) / 8) by
              dsimp [δ]
              field_simp
              ring]
        have hratio : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNr).2 hkN
        nlinarith [div_nonneg hk0 hNr.le, div_nonneg hL.le (by norm_num : (0 : ℝ) ≤ 8)]
    have hinterval : ∀ k : ℕ, k < N →
        a + 4 * (k : ℝ) * δ < b - 4 * (k : ℝ) * δ := by
      intro k hk
      have hs := (hshift k hk.le).2
      nlinarith
    have hδsmall : ∀ k : ℕ, k < N →
        δ < ((b - 4 * (k : ℝ) * δ) - (a + 4 * (k : ℝ) * δ)) / 8 := by
      intro k hk
      have hs := (hshift k hk.le).2
      nlinarith [hδle, hL]
    have hhc : h ≤ c0 * Real.sqrt δ := by
      dsimp [h]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg δ)
    have hi := one_step_iterate c0 hc0 hstep a b δ h B N hδ hh
      hhc hinterval hδsmall Z W heq hZ hWmeas hW hzero
    have hJ : Set.Ioo (a + 4 * (N : ℝ) * δ) (b - 4 * (N : ℝ) * δ) = Jmid := by
      congr 1 <;> dsimp [δ, Jmid] <;> field_simp <;> ring
    simpa [h, δ, hJ] using hi
  have hsquares : ∀ n : ℕ,
      VanishesAbove
        (B - (((n + 1) ^ 2 : ℕ) : ℝ) *
          ((c0 / 2) * Real.sqrt ((b - a) /
            (32 * ((((n + 1) ^ 2 : ℕ) : ℝ))))))
        (restrictTimeField Jmid Z) := by
    intro n
    exact hvanish ((n + 1) ^ 2) (by positivity)
  have hallae : ∀ᵐ p ∂(volume.prod (volume.prod volume)), ∀ n : ℕ,
      B - (((n + 1) ^ 2 : ℕ) : ℝ) *
          ((c0 / 2) * Real.sqrt ((b - a) /
            (32 * ((((n + 1) ^ 2 : ℕ) : ℝ))))) < p.2.1 →
        restrictTimeField Jmid Z p = 0 :=
    ae_all_iff.2 hsquares
  have hrestricted : ∀ᵐ p ∂((volume.restrict Jmid).prod (volume.prod volume)),
      ∀ n : ℕ,
        B - (((n + 1) ^ 2 : ℕ) : ℝ) *
            ((c0 / 2) * Real.sqrt ((b - a) /
              (32 * ((((n + 1) ^ 2 : ℕ) : ℝ))))) < p.2.1 →
          restrictTimeField Jmid Z p = 0 :=
    (ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)) hallae
  have htmem : ∀ᵐ p : ℝ × (ℝ × ℝ)
      ∂((volume.restrict Jmid).prod (volume.prod volume)), p.1 ∈ Jmid :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict Jmid)
      (ν := volume.prod volume)).ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hrestricted, htmem] with p hp hpt
  let C : ℝ := (c0 / 2) * Real.sqrt ((b - a) / 32)
  have hC : 0 < C := mul_pos (by positivity) (Real.sqrt_pos.2 (div_pos hL (by norm_num)))
  obtain ⟨m : ℕ, hm : (B - p.2.1) / C < m⟩ := exists_nat_gt ((B - p.2.1) / C)
  let n : ℕ := m
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hsqrt : Real.sqrt ((((n + 1) ^ 2 : ℕ) : ℝ)) = (n + 1 : ℕ) := by
    rw [show ((((n + 1) ^ 2 : ℕ) : ℝ)) = ((n + 1 : ℝ) ^ 2) by norm_num]
    simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))] using
      Real.sqrt_sq_eq_abs (n + 1 : ℝ)
  have hfactor :
      ((((n + 1) ^ 2 : ℕ) : ℝ)) *
          ((c0 / 2) * Real.sqrt ((b - a) /
            (32 * ((((n + 1) ^ 2 : ℕ) : ℝ))))) = (n + 1 : ℝ) * C := by
    rw [show (b - a) / (32 * ((((n + 1) ^ 2 : ℕ) : ℝ))) =
        ((b - a) / 32) / ((((n + 1) ^ 2 : ℕ) : ℝ)) by ring]
    rw [Real.sqrt_div (div_nonneg hL.le (by norm_num)), hsqrt]
    dsimp [C]
    field_simp
    push_cast
    ring
  have hthreshold :
      B - (((n + 1) ^ 2 : ℕ) : ℝ) *
          ((c0 / 2) * Real.sqrt ((b - a) /
            (32 * ((((n + 1) ^ 2 : ℕ) : ℝ))))) < p.2.1 := by
    rw [hfactor]
    have hm' : (B - p.2.1) / C < (n + 1 : ℝ) := by
      dsimp [n]
      exact hm.trans_le (by norm_num)
    have := (div_lt_iff₀ hC).1 hm'
    linarith
  have hz := hp n hthreshold
  simpa [restrictTimeField, hpt] using hz

end CubicNLSPhaseRetrieval
