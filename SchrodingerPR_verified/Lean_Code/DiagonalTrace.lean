import Lean_Code.FourierSobolev
import Lean_Code.WronskianExterior
import Lean_Code.ExteriorLocalData
import Lean_Code.PhysicalExterior
import Lean_Code.CriticalZeroSafeRecovery
import Lean_Code.SmoothHsMultiplier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Distribution-valued diagonal traces

Blueprint chapter: `chap:traces` (module 11).
Imports: modules 1 and 10.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology Pointwise
open LineDeriv

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Local `L²` membership on every compact interval. -/
def IsLocalL2 (h : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → MemLp h 2 (volume.restrict (Set.Icc a b))

/-- A function and a proposed second derivative agree distributionally. -/
def HasWeakSecondDerivative (h h2 : ℝ → ℂ) : Prop :=
  ∀ φ : 𝓢(ℝ, ℂ),
    ∫ x, h x * iteratedDeriv 2 (φ : ℝ → ℂ) x = ∫ x, h2 x * φ x

/-- Concrete local `H²` regularity of a representative. -/
def IsLocalH2 (h : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b →
    MemLp h 2 (volume.restrict (Set.Icc a b)) ∧
    MemLp (deriv h) 2 (volume.restrict (Set.Icc a b)) ∧
    MemLp (iteratedDeriv 2 h) 2 (volume.restrict (Set.Icc a b)) ∧
    ∀ φ : ℝ → ℂ, ContDiff ℝ 1 φ →
      (∫ x in a..b, deriv h x * deriv φ x) =
        deriv h b * φ b - deriv h a * φ a -
          ∫ x in a..b, iteratedDeriv 2 h x * φ x

/-- Two integrations by parts on a finite interval. This is the analytic core
of the one-dimensional jump identity, with both endpoint traces explicit. -/
theorem integral_mul_second_deriv_eq (h φ : ℝ → ℂ) (a b : ℝ)
    (hh : ContDiff ℝ 2 h) (hφ : ContDiff ℝ 2 φ) :
    (∫ s in a..b, h s * iteratedDeriv 2 φ s) =
      h b * deriv φ b - h a * deriv φ a -
        (deriv h b * φ b - deriv h a * φ a) +
        ∫ s in a..b, iteratedDeriv 2 h s * φ s := by
  have hh1 : ∀ x ∈ Set.uIcc a b, HasDerivAt h (deriv h x) x := by
    intro x hx
    exact (hh.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x).hasDerivAt
  have hh2 : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (deriv h) (iteratedDeriv 2 h x) x := by
    intro x hx
    rw [← iteratedDeriv_one]
    rw [show iteratedDeriv 2 h = deriv (iteratedDeriv 1 h) by
      simpa using (iteratedDeriv_succ (n := 1) (f := h))]
    exact (hh.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
  have hφ1 : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (deriv φ x) x := by
    intro x hx
    exact (hφ.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x).hasDerivAt
  have hφ2 : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (deriv φ) (iteratedDeriv 2 φ x) x := by
    intro x hx
    rw [← iteratedDeriv_one]
    rw [show iteratedDeriv 2 φ = deriv (iteratedDeriv 1 φ) by
      simpa using (iteratedDeriv_succ (n := 1) (f := φ))]
    exact (hφ.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
  have hhi : IntervalIntegrable (deriv h) volume a b := by
    simpa only [iteratedDeriv_one] using
      (hh.continuous_iteratedDeriv 1 (by norm_num)).intervalIntegrable a b
  have hh2i : IntervalIntegrable (iteratedDeriv 2 h) volume a b :=
    (hh.continuous_iteratedDeriv 2 (by norm_num)).intervalIntegrable _ _
  have hφi : IntervalIntegrable (deriv φ) volume a b := by
    simpa only [iteratedDeriv_one] using
      (hφ.continuous_iteratedDeriv 1 (by norm_num)).intervalIntegrable a b
  have hφ2i : IntervalIntegrable (iteratedDeriv 2 φ) volume a b :=
    (hφ.continuous_iteratedDeriv 2 (by norm_num)).intervalIntegrable _ _
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hh1 hφ2 hhi hφ2i
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hh2 hφ1 hh2i hφi
  rw [hfirst, hsecond]
  ring

theorem integral_Iio_eq_interval_of_zero_below (f : ℝ → ℂ) (a b : ℝ)
    (hab : a ≤ b) (hf : IntegrableOn f (Set.Iio b))
    (hzero : ∀ x, x < a → f x = 0) :
    (∫ x in Set.Iio b, f x) = ∫ x in a..b, f x := by
  have hfa : IntegrableOn f (Set.Iio a) :=
    hf.mono_set (Set.Iio_subset_Iio hab)
  have hinta : (∫ x in Set.Iio a, f x) = 0 := by
    calc
      (∫ x in Set.Iio a, f x) = ∫ x in Set.Iio a, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
        exact hzero x hx
      _ = 0 := by simp
  have h := intervalIntegral.integral_Iio_sub_Iio' hf hfa
  rwa [hinta, sub_zero] at h

/-- Pairing form of the lower-half-line jump formula for classical `C²`
functions. It is the smooth core used before passing to local `H²` limits. -/
theorem lower_halfline_jump_pairing_contDiff (h φ : ℝ → ℂ)
    (hh : ContDiff ℝ 2 h) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    (∫ s in Set.Iio 0, h s * iteratedDeriv 2 φ s) =
      h 0 * deriv φ 0 - deriv h 0 * φ 0 +
        ∫ s in Set.Iio 0, iteratedDeriv 2 h s * φ s := by
  rcases hφc.isCompact.bddBelow with ⟨c, hc⟩
  let a : ℝ := min c 0 - 1
  have ha0 : a ≤ 0 := by dsimp [a]; linarith [min_le_right c 0]
  have halower : ∀ x ∈ tsupport φ, a ≤ x := by
    intro x hx
    dsimp [a]
    have hcx : c ≤ x := hc hx
    have hmin : min c 0 ≤ c := min_le_left _ _
    linarith
  have hφzero : ∀ x, x < a → φ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge (halower x (subset_tsupport _ hn))) hx
  have hφdzero : ∀ x, x < a → deriv φ x = 0 := by
    intro x hx
    by_contra hn
    have hs : x ∈ tsupport φ := tsupport_deriv_subset (subset_tsupport _ hn)
    exact (not_lt_of_ge (halower x hs)) hx
  have hφ2zero : ∀ x, x < a → iteratedDeriv 2 φ x = 0 := by
    intro x hx
    rw [show iteratedDeriv 2 φ = deriv (deriv φ) by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]]
    by_contra hn
    have hxsupp : x ∈ Function.support (deriv (deriv φ)) := hn
    have hs2 : x ∈ tsupport (deriv (deriv φ)) := subset_tsupport _ hxsupp
    have hs1 : x ∈ tsupport (deriv φ) := tsupport_deriv_subset hs2
    have hs : x ∈ tsupport φ := tsupport_deriv_subset hs1
    exact (not_lt_of_ge (halower x hs)) hx
  have hleftInt : Integrable (fun s => h s * iteratedDeriv 2 φ s) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hh.continuous.mul (hφ.continuous_iteratedDeriv 2 (by norm_num))
    · change HasCompactSupport (h * iteratedDeriv 2 φ)
      apply HasCompactSupport.mul_left
      rw [show iteratedDeriv 2 φ = deriv (deriv φ) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_one]]
      exact hφc.deriv.deriv
  have hrightInt : Integrable (fun s => iteratedDeriv 2 h s * φ s) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hh.continuous_iteratedDeriv 2 (by norm_num)).mul hφ.continuous
    · change HasCompactSupport (iteratedDeriv 2 h * φ)
      exact hφc.mul_left
  have hleft := integral_Iio_eq_interval_of_zero_below
    (fun s => h s * iteratedDeriv 2 φ s) a 0 ha0 hleftInt.integrableOn (by
      intro x hx
      rw [hφ2zero x hx, mul_zero])
  have hright := integral_Iio_eq_interval_of_zero_below
    (fun s => iteratedDeriv 2 h s * φ s) a 0 ha0 hrightInt.integrableOn (by
      intro x hx
      rw [hφzero x hx, mul_zero])
  have hac : a < c := by
    dsimp [a]
    linarith [min_le_left c 0]
  have hφa : φ a = 0 := by
    by_contra hn
    exact (not_lt_of_ge (hc (subset_tsupport _ hn))) hac
  have hφda : deriv φ a = 0 := by
    by_contra hn
    have hs : a ∈ tsupport φ := tsupport_deriv_subset (subset_tsupport _ hn)
    exact (not_lt_of_ge (hc hs)) hac
  rw [hleft, hright, integral_mul_second_deriv_eq h φ a 0 hh hφ,
    hφa, hφda]
  ring

/-- The lower-half-line jump formula for the genuine local Sobolev interface:
`h` is `C¹`, its recorded second derivative is locally `L²`, and the weak
integration-by-parts identity is part of `IsLocalH2`. -/
theorem lower_halfline_jump_pairing_localH2 (h φ : ℝ → ℂ)
    (hh1 : ContDiff ℝ 1 h) (hh2 : IsLocalH2 h)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ s in Set.Iio 0, h s * iteratedDeriv 2 φ s) =
      h 0 * deriv φ 0 - deriv h 0 * φ 0 +
        ∫ s in Set.Iio 0, iteratedDeriv 2 h s * φ s := by
  rcases hφc.isCompact.bddBelow with ⟨c, hc⟩
  let a : ℝ := min c 0 - 1
  have ha0 : a < 0 := by dsimp [a]; linarith [min_le_right c 0]
  have hac : a < c := by dsimp [a]; linarith [min_le_left c 0]
  have hφzero : ∀ x, x ≤ a → φ x = 0 := by
    intro x hx
    by_contra hn
    have hcx : c ≤ x := hc (subset_tsupport _ hn)
    linarith
  have hφdzero : ∀ x, x ≤ a → deriv φ x = 0 := by
    intro x hx
    by_contra hn
    have hs : x ∈ tsupport φ := tsupport_deriv_subset (subset_tsupport _ hn)
    have hcx : c ≤ x := hc hs
    linarith
  have hφ2zero : ∀ x, x < a → iteratedDeriv 2 φ x = 0 := by
    intro x hx
    rw [show iteratedDeriv 2 φ = deriv (deriv φ) by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]]
    by_contra hn
    have hxsupp : x ∈ Function.support (deriv (deriv φ)) := hn
    have hs2 : x ∈ tsupport (deriv (deriv φ)) := subset_tsupport _ hxsupp
    have hs1 : x ∈ tsupport (deriv φ) := tsupport_deriv_subset hs2
    have hs : x ∈ tsupport φ := tsupport_deriv_subset hs1
    have hcx : c ≤ x := hc hs
    linarith
  have hleftInt : Integrable (fun s => h s * iteratedDeriv 2 φ s) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hh1.continuous.mul (hφ.continuous_iteratedDeriv 2 (by norm_num))
    · change HasCompactSupport (h * iteratedDeriv 2 φ)
      apply HasCompactSupport.mul_left
      rw [show iteratedDeriv 2 φ = deriv (deriv φ) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_one]]
      exact hφc.deriv.deriv
  have hloc := hh2 a 0 ha0
  have hh2loc : MemLp (iteratedDeriv 2 h) 2
      (volume.restrict (Set.Icc a 0)) := hloc.2.2.1
  have hweakIBP := hloc.2.2.2
  have hφLp : MemLp φ 2 (volume : Measure ℝ) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hφLpLoc : MemLp φ 2 (volume.restrict (Set.Icc a 0)) :=
    hφLp.mono_measure Measure.restrict_le_self
  have hprodIcc : IntegrableOn (fun s => iteratedDeriv 2 h s * φ s)
      (Set.Icc a 0) := by
    exact memLp_one_iff_integrable.mp (hφLpLoc.mul' hh2loc)
  have hprodBelow : IntegrableOn (fun s => iteratedDeriv 2 h s * φ s)
      (Set.Iio a) := by
    refine (integrable_zero ℝ ℂ (volume.restrict (Set.Iio a))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    change (0 : ℂ) = iteratedDeriv 2 h x * φ x
    rw [hφzero x hx.le, mul_zero]
  have hrightInt : IntegrableOn (fun s => iteratedDeriv 2 h s * φ s)
      (Set.Iio 0) := by
    have hu := hprodBelow.union (hprodIcc.mono_set (Set.Ico_subset_Icc_self))
    rw [Set.Iio_union_Ico_eq_Iio ha0.le] at hu
    exact hu
  have hleft := integral_Iio_eq_interval_of_zero_below
    (fun s => h s * iteratedDeriv 2 φ s) a 0 ha0.le hleftInt.integrableOn (by
      intro x hx
      rw [hφ2zero x hx, mul_zero])
  have hright := integral_Iio_eq_interval_of_zero_below
    (fun s => iteratedDeriv 2 h s * φ s) a 0 ha0.le hrightInt (by
      intro x hx
      rw [hφzero x hx.le, mul_zero])
  have hhderiv : ∀ x ∈ Set.uIcc a 0, HasDerivAt h (deriv h x) x := by
    intro x hx
    exact (hh1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x).hasDerivAt
  have hφderiv : ∀ x ∈ Set.uIcc a 0,
      HasDerivAt (deriv φ) (iteratedDeriv 2 φ x) x := by
    intro x hx
    rw [← iteratedDeriv_one]
    rw [show iteratedDeriv 2 φ = deriv (iteratedDeriv 1 φ) by
      simpa using (iteratedDeriv_succ (n := 1) (f := φ))]
    exact (hφ.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
  have hh1loc : MemLp (deriv h) 2 (volume.restrict (Set.Icc a 0)) :=
    hloc.2.1
  have hh1int : IntegrableOn (deriv h) (Set.Icc a 0) :=
    memLp_one_iff_integrable.mp (hh1loc.mono_exponent (by norm_num))
  have hh1intu : IntegrableOn (deriv h) (Set.uIcc a 0) := by
    simpa [Set.uIcc_of_le ha0.le] using hh1int
  have hhi : IntervalIntegrable (deriv h) volume a 0 :=
    hh1intu.intervalIntegrable
  have hφ2i : IntervalIntegrable (iteratedDeriv 2 φ) volume a 0 :=
    (hφ.continuous_iteratedDeriv 2 (by norm_num)).intervalIntegrable _ _
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hhderiv hφderiv hhi hφ2i
  have hweak := hweakIBP φ (hφ.of_le (by norm_num))
  rw [hleft, hright, hfirst, hweak, hφzero a le_rfl, hφdzero a le_rfl]
  ring

/-- A translated test in the tangential variable, used by the Neumann limit. -/
def translatedNormalTest (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s z : ℝ) : ℂ :=
  ψ (t, Real.sqrt 2 * z + s)

private def normalTestSection (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun z : ℝ => (t, Real.sqrt 2 * z + s)) (by
    let L : ℝ →L[ℝ] ℝ × ℝ :=
      (0 : ℝ →L[ℝ] ℝ).prod (Real.sqrt 2 • ContinuousLinearMap.id ℝ ℝ)
    have h := L.hasTemperateGrowth.add
      (show Function.HasTemperateGrowth (fun _ : ℝ => (t, s)) by fun_prop)
    have hfun : (⇑L + fun _ : ℝ => (t, s)) =
        (fun z : ℝ => (t, Real.sqrt 2 * z + s)) := by
      funext z
      simp [L, smul_eq_mul]
    rw [← hfun]
    exact h) (by
    refine ⟨1, 1 + |s|, fun z => ?_⟩
    have hsqrt : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    have hsecond : |Real.sqrt 2 * z + s| ≤ ‖(t, Real.sqrt 2 * z + s)‖ := by
      simp only [Prod.norm_def, Real.norm_eq_abs]
      exact le_max_right _ _
    have hz : |z| ≤ |Real.sqrt 2 * z + s| + |s| := by
      calc
        |z| ≤ Real.sqrt 2 * |z| := by nlinarith [abs_nonneg z]
        _ = |Real.sqrt 2 * z| := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
        _ = |(Real.sqrt 2 * z + s) - s| := by ring_nf
        _ ≤ |Real.sqrt 2 * z + s| + |s| := abs_sub _ _
    simp only [Real.norm_eq_abs, pow_one]
    calc
      |z| ≤ |Real.sqrt 2 * z + s| + |s| := hz
      _ ≤ ‖(t, Real.sqrt 2 * z + s)‖ + |s| := by gcongr
      _ ≤ (1 + |s|) * (1 + ‖(t, Real.sqrt 2 * z + s)‖) := by
        nlinarith [abs_nonneg s, norm_nonneg (t, Real.sqrt 2 * z + s)]) ψ

@[simp] private lemma normalTestSection_apply (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t s z : ℝ) : normalTestSection ψ t s z = ψ (t, Real.sqrt 2 * z + s) := rfl

private def normalTestDifference (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) : 𝓢(ℝ, ℂ) :=
  normalTestSection ψ t s - normalTestSection ψ t 0

@[simp] private lemma normalTestDifference_apply (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t s z : ℝ) : normalTestDifference ψ t s z =
      translatedNormalTest ψ t s z - translatedNormalTest ψ t 0 z := rfl

private def normalPartial (ψ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  ∂_{((0, 1) : ℝ × ℝ)} ψ

private lemma deriv_normal_section (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s z : ℝ) :
    deriv (normalTestSection ψ t s : ℝ → ℂ) z =
      (Real.sqrt 2 : ℂ) * normalPartial ψ (t, Real.sqrt 2 * z + s) := by
  have hg : HasDerivAt (fun z : ℝ => (t, Real.sqrt 2 * z + s))
      ((0, Real.sqrt 2) : ℝ × ℝ) z := by
    convert (hasDerivAt_const z t).prodMk
      ((hasDerivAt_const_mul (𝕜 := ℝ) (x := z) (Real.sqrt 2)).add_const s)
  have hp := ψ.hasFDerivAt (t, Real.sqrt 2 * z + s)
  have hc := hp.comp_hasDerivAt z hg
  change deriv ((ψ : ℝ × ℝ → ℂ) ∘
    fun z : ℝ => (t, Real.sqrt 2 * z + s)) z = _
  rw [hc.deriv]
  simp only [normalPartial, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [show ((0, Real.sqrt 2) : ℝ × ℝ) = Real.sqrt 2 • ((0, 1) : ℝ × ℝ) by
    ext <;> simp]
  rw [map_smul]
  simp

private lemma deriv_normalTestDifference (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s z : ℝ) :
    deriv (normalTestDifference ψ t s : ℝ → ℂ) z =
      (Real.sqrt 2 : ℂ) *
        (normalPartial ψ (t, Real.sqrt 2 * z + s) -
          normalPartial ψ (t, Real.sqrt 2 * z)) := by
  rw [show deriv (normalTestDifference ψ t s : ℝ → ℂ) z =
      deriv (normalTestSection ψ t s : ℝ → ℂ) z -
        deriv (normalTestSection ψ t 0 : ℝ → ℂ) z by
    exact deriv_sub (normalTestSection ψ t s).differentiableAt
      (normalTestSection ψ t 0).differentiableAt]
  rw [deriv_normal_section, deriv_normal_section]
  simp only [add_zero]
  ring

private lemma deriv_spatial_section (ψ : 𝓢(ℝ × ℝ, ℂ)) (t r : ℝ) :
    deriv (fun q : ℝ => ψ (t, q)) r = normalPartial ψ (t, r) := by
  have hg : HasDerivAt (fun q : ℝ => (t, q)) ((0, 1) : ℝ × ℝ) r := by
    simpa only [id_eq] using (hasDerivAt_const r t).prodMk (hasDerivAt_id r)
  have hc := (ψ.hasFDerivAt (t, r)).comp_hasDerivAt r hg
  change deriv ((ψ : ℝ × ℝ → ℂ) ∘ fun q : ℝ => (t, q)) r = _
  rw [hc.deriv]
  simp only [normalPartial, SchwartzMap.lineDerivOp_apply_eq_fderiv]

private lemma normalPartial_bound (ψ : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    ‖normalPartial ψ p‖ ≤ SchwartzMap.seminorm ℂ 0 1 ψ := by
  unfold normalPartial
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  calc
    ‖fderiv ℝ (ψ : ℝ × ℝ → ℂ) p ((0, 1) : ℝ × ℝ)‖ ≤
        ‖fderiv ℝ (ψ : ℝ × ℝ → ℂ) p‖ * ‖((0, 1) : ℝ × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (ψ : ℝ × ℝ → ℂ) p‖ := by simp [Prod.norm_def]
    _ ≤ SchwartzMap.seminorm ℂ 0 1 ψ := by
      simpa using (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ 1 p)

private lemma normalPartial_difference_bound (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t r s : ℝ) :
    ‖normalPartial ψ (t, r + s) - normalPartial ψ (t, r)‖ ≤
      SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * |s| := by
  let q : ℝ → ℂ := fun x => normalPartial ψ (t, x)
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ q x := by
    intro x hx
    exact (normalPartial ψ).differentiableAt.comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hderiv (x : ℝ) :
      ‖deriv q x‖ ≤ SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) := by
    have hg : HasDerivAt (fun y : ℝ => (t, y)) ((0, 1) : ℝ × ℝ) x := by
      simpa only [id_eq] using (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
    have hc := ((normalPartial ψ).hasFDerivAt (t, x)).comp_hasDerivAt x hg
    change ‖deriv ((normalPartial ψ : ℝ × ℝ → ℂ) ∘
      fun y : ℝ => (t, y)) x‖ ≤ _
    rw [hc.deriv]
    calc
      ‖fderiv ℝ (normalPartial ψ : ℝ × ℝ → ℂ) (t, x) ((0, 1) : ℝ × ℝ)‖ ≤
          ‖fderiv ℝ (normalPartial ψ : ℝ × ℝ → ℂ) (t, x)‖ := by
        simpa [Prod.norm_def] using
          (ContinuousLinearMap.le_opNorm
            (fderiv ℝ (normalPartial ψ : ℝ × ℝ → ℂ) (t, x))
            ((0, 1) : ℝ × ℝ))
      _ ≤ SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) := by
        simpa using
          (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ
            (normalPartial ψ) 1 (t, x))
  simpa [q, Real.norm_eq_abs] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff
      (fun x _ => hderiv x) (Set.mem_univ _) (Set.mem_univ _) :
        ‖q (r + s) - q r‖ ≤
          SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * ‖(r + s) - r‖)

private lemma normalTestDifference_bound (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t s z : ℝ) :
    ‖normalTestDifference ψ t s z‖ ≤
      SchwartzMap.seminorm ℂ 0 1 ψ * |s| := by
  let q : ℝ → ℂ := fun r => ψ (t, r)
  have hdiff : ∀ r ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ q r := by
    intro r hr
    exact ψ.differentiableAt.comp r
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hderiv (r : ℝ) :
      ‖deriv q r‖ ≤ SchwartzMap.seminorm ℂ 0 1 ψ := by
    rw [show deriv q r = normalPartial ψ (t, r) by
      simpa [q] using deriv_spatial_section ψ t r]
    exact normalPartial_bound ψ (t, r)
  simpa [normalTestDifference_apply, translatedNormalTest, q, Real.norm_eq_abs]
    using
      (convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff
        (fun r _ => hderiv r) (Set.mem_univ _) (Set.mem_univ _) :
        ‖q (Real.sqrt 2 * z + s) - q (Real.sqrt 2 * z)‖ ≤
          SchwartzMap.seminorm ℂ 0 1 ψ *
            ‖(Real.sqrt 2 * z + s) - Real.sqrt 2 * z‖)

private lemma normalTestDifference_deriv_bound (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t s z : ℝ) :
    ‖deriv (normalTestDifference ψ t s : ℝ → ℂ) z‖ ≤
      Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * |s| := by
  rw [deriv_normalTestDifference, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc
    Real.sqrt 2 *
        ‖normalPartial ψ (t, Real.sqrt 2 * z + s) -
          normalPartial ψ (t, Real.sqrt 2 * z)‖ ≤
        Real.sqrt 2 *
          (SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * |s|) :=
      mul_le_mul_of_nonneg_left
        (normalPartial_difference_bound ψ t (Real.sqrt 2 * z) s)
        (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * |s| := by ring

private lemma schwartzSupNorm_normalTestDifference_le
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) :
    schwartzSupNorm (normalTestDifference ψ t s) ≤
      ENNReal.ofReal (SchwartzMap.seminorm ℂ 0 1 ψ * |s|) := by
  apply iSup_le
  intro z
  change ‖normalTestDifference ψ t s z‖ₑ ≤ _
  simpa only [ofReal_norm] using
    ENNReal.ofReal_le_ofReal (normalTestDifference_bound ψ t s z)

private lemma schwartzDerivSupNorm_normalTestDifference_le
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) :
    schwartzDerivSupNorm (normalTestDifference ψ t s) ≤
      ENNReal.ofReal
        (Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * |s|) := by
  apply iSup_le
  intro z
  change ‖deriv (normalTestDifference ψ t s : ℝ → ℂ) z‖ₑ ≤ _
  simpa only [ofReal_norm] using
    ENNReal.ofReal_le_ofReal (normalTestDifference_deriv_bound ψ t s z)

private lemma seminorm_zero_normalTestDifference_le
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) :
    SchwartzMap.seminorm ℂ 0 0 (normalTestDifference ψ t s) ≤
      SchwartzMap.seminorm ℂ 0 1 ψ * |s| := by
  apply SchwartzMap.seminorm_le_bound' ℂ 0 0 _ (by positivity)
  intro z
  simpa using normalTestDifference_bound ψ t s z

private lemma seminorm_one_normalTestDifference_le
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) :
    SchwartzMap.seminorm ℂ 0 1 (normalTestDifference ψ t s) ≤
      Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ) * |s| := by
  apply SchwartzMap.seminorm_le_bound' ℂ 0 1 _ (by positivity)
  intro z
  simpa only [pow_zero, iteratedDeriv_one, one_mul] using
    normalTestDifference_deriv_bound ψ t s z

private lemma seminorm_zero_normalTestSection_le
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) :
    SchwartzMap.seminorm ℂ 0 0 (normalTestSection ψ t s) ≤
      SchwartzMap.seminorm ℂ 0 0 ψ := by
  apply SchwartzMap.seminorm_le_bound' ℂ 0 0 _ (by positivity)
  intro z
  simpa only [pow_zero, one_mul, iteratedDeriv_zero, normalTestSection_apply] using
    (SchwartzMap.norm_le_seminorm ℂ ψ (t, Real.sqrt 2 * z + s))

private lemma seminorm_one_normalTestSection_le
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ) :
    SchwartzMap.seminorm ℂ 0 1 (normalTestSection ψ t s) ≤
      Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 0 (normalPartial ψ) := by
  apply SchwartzMap.seminorm_le_bound' ℂ 0 1 _ (by positivity)
  intro z
  rw [iteratedDeriv_one, deriv_normal_section, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  simp only [pow_zero, one_mul]
  exact mul_le_mul_of_nonneg_left
    (SchwartzMap.norm_le_seminorm ℂ (normalPartial ψ)
      (t, Real.sqrt 2 * z + s)) (Real.sqrt_nonneg 2)

/-- A uniform-in-translation multiplier bound for the normal test sections. -/
theorem normalTestSection_multiplier_norm_le (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t s : ℝ) (f : Hs (1 / 2 : ℝ)) :
    ‖schwartzHsMultiplier (normalTestSection ψ t s) f‖ ≤
      (Real.sqrt smoothHsMultiplierConstantSq.toReal *
        (SchwartzMap.seminorm ℂ 0 0 ψ +
          Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 0 (normalPartial ψ))) * ‖f‖ := by
  calc
    ‖schwartzHsMultiplier (normalTestSection ψ t s) f‖ ≤
        Real.sqrt smoothHsMultiplierConstantSq.toReal *
          (SchwartzMap.seminorm ℂ 0 0 (normalTestSection ψ t s) +
            SchwartzMap.seminorm ℂ 0 1 (normalTestSection ψ t s)) * ‖f‖ :=
      schwartzHsMultiplier_norm_le _ _
    _ ≤ (Real.sqrt smoothHsMultiplierConstantSq.toReal *
        (SchwartzMap.seminorm ℂ 0 0 ψ +
          Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 0 (normalPartial ψ))) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact add_le_add (seminorm_zero_normalTestSection_le ψ t s)
        (seminorm_one_normalTestSection_le ψ t s)

/-- Multiplication by the change of a translated tangential test gains one
power of the translation parameter in the critical Sobolev norm. -/
theorem translated_test_multiplier (ψ : 𝓢(ℝ × ℝ, ℂ))
    (s0 : ℝ) (hs0 : 0 < s0) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, 0 < |s| → |s| ≤ s0 →
    ∀ f : Hs (1 / 2 : ℝ), ∃ g : Hs (1 / 2 : ℝ),
      ((Hs.toL2 (by norm_num) g : ℝ → ℂ) =ᵐ[volume] fun z =>
        (translatedNormalTest ψ t s z - translatedNormalTest ψ t 0 z) *
          (Hs.toL2 (by norm_num) f : ℝ → ℂ) z) ∧
      ‖g‖ ≤ C * |s| * ‖f‖ := by
  let A : ℝ := SchwartzMap.seminorm ℂ 0 1 ψ
  let B : ℝ := Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 1 (normalPartial ψ)
  let K : ℝ := smoothHsMultiplierConstantSq.toReal
  let C : ℝ := Real.sqrt K * (A + B)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg K) (add_nonneg hA0 hB0)
  refine ⟨C, hC, ?_⟩
  intro t s hs hs0 f
  let chi : 𝓢(ℝ, ℂ) := normalTestDifference ψ t s
  let g : Hs (1 / 2 : ℝ) := schwartzHsMultiplier chi f
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [schwartzHsMultiplier_toL2_ae chi f] with z hz
    rw [hz]
    simp only [chi, normalTestDifference_apply]
    ring
  · have hsemi : SchwartzMap.seminorm ℂ 0 0 chi +
        SchwartzMap.seminorm ℂ 0 1 chi ≤ (A + B) * |s| := by
      calc
        _ ≤ A * |s| + B * |s| := by
          gcongr
          · simpa [chi, A] using seminorm_zero_normalTestDifference_le ψ t s
          · simpa [chi, B, mul_assoc] using seminorm_one_normalTestDifference_le ψ t s
        _ = (A + B) * |s| := by ring
    have hsq : ‖g‖ₑ ^ (2 : ℕ) ≤
        smoothHsMultiplierConstantSq *
          ENNReal.ofReal ((A + B) * |s|) ^ (2 : ℕ) *
            ‖f‖ₑ ^ (2 : ℕ) := by
      calc
        ‖g‖ₑ ^ (2 : ℕ) ≤ smoothHsMultiplierConstantSq *
            ENNReal.ofReal
                (SchwartzMap.seminorm ℂ 0 0 chi +
                  SchwartzMap.seminorm ℂ 0 1 chi) ^ (2 : ℕ) *
              ‖f‖ₑ ^ (2 : ℕ) := by
          simpa [g] using schwartzHsMultiplier_enorm_sq_le chi f
        _ ≤ _ := by
          gcongr
    have hrightTop : smoothHsMultiplierConstantSq *
          ENNReal.ofReal ((A + B) * |s|) ^ (2 : ℕ) *
            ‖f‖ₑ ^ (2 : ℕ) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top smoothHsMultiplierConstantSq_lt_top.ne
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      · exact ENNReal.pow_ne_top enorm_ne_top
    have hreal := (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top enorm_ne_top)
      hrightTop).mpr hsq
    have hab0 : 0 ≤ A + B := add_nonneg hA0 hB0
    have habs0 : 0 ≤ (A + B) * |s| := mul_nonneg hab0 (abs_nonneg s)
    have hsqReal : ‖g‖ ^ 2 ≤ K * ((A + B) * |s|) ^ 2 * ‖f‖ ^ 2 := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ofReal_norm,
        ENNReal.toReal_ofReal habs0, toReal_enorm, K, pow_two] using hreal
    have hsqrt : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK0
    have hrhs0 : 0 ≤ C * |s| * ‖f‖ :=
      mul_nonneg (mul_nonneg hC (abs_nonneg s)) (norm_nonneg f)
    have hsquare : (C * |s| * ‖f‖) ^ 2 =
        K * ((A + B) * |s|) ^ 2 * ‖f‖ ^ 2 := by
      dsimp [C]
      calc
        (Real.sqrt K * (A + B) * |s| * ‖f‖) ^ 2 =
            (Real.sqrt K) ^ 2 * (A + B) ^ 2 * |s| ^ 2 * ‖f‖ ^ 2 := by ring
        _ = _ := by rw [hsqrt]; ring
    rw [← hsquare] at hsqReal
    nlinarith [sq_nonneg (‖g‖ - C * |s| * ‖f‖), norm_nonneg g]

lemma normalTestMultiplier_sub (ψ : 𝓢(ℝ × ℝ, ℂ)) (t s : ℝ)
    (f : Hs (1 / 2 : ℝ)) :
    schwartzHsMultiplier (normalTestSection ψ t s) f -
        schwartzHsMultiplier (normalTestSection ψ t 0) f =
      schwartzHsMultiplier (normalTestDifference ψ t s) f := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  have hsub : Hs.toL2 (by norm_num)
      (schwartzHsMultiplier (normalTestSection ψ t s) f -
        schwartzHsMultiplier (normalTestSection ψ t 0) f) =
      Hs.toL2 (by norm_num) (schwartzHsMultiplier (normalTestSection ψ t s) f) -
        Hs.toL2 (by norm_num) (schwartzHsMultiplier (normalTestSection ψ t 0) f) := by
    rw [← hsHalfToL2CLM_apply, map_sub, hsHalfToL2CLM_apply,
      hsHalfToL2CLM_apply]
  filter_upwards [schwartzHsMultiplier_toL2_ae (normalTestSection ψ t s) f,
    schwartzHsMultiplier_toL2_ae (normalTestSection ψ t 0) f,
    schwartzHsMultiplier_toL2_ae (normalTestDifference ψ t s) f,
    Lp.coeFn_sub
      (Hs.toL2 (by norm_num) (schwartzHsMultiplier (normalTestSection ψ t s) f))
      (Hs.toL2 (by norm_num) (schwartzHsMultiplier (normalTestSection ψ t 0) f))]
      with z hs h0 hd hcoe
  have hsubz := congrFun (congrArg (fun q : FourierL2 => (q : ℝ → ℂ)) hsub) z
  rw [hsubz, hcoe]
  change (Hs.toL2 (by norm_num)
      (schwartzHsMultiplier (normalTestSection ψ t s) f) : ℝ → ℂ) z -
      (Hs.toL2 (by norm_num)
        (schwartzHsMultiplier (normalTestSection ψ t 0) f) : ℝ → ℂ) z = _
  rw [hs, h0, hd]
  simp only [normalTestDifference_apply, normalTestSection_apply,
    translatedNormalTest]
  ring

theorem translated_test_multiplier_tendsto (ψ : 𝓢(ℝ × ℝ, ℂ))
    (t : ℝ) (f : Hs (1 / 2 : ℝ)) :
    Tendsto (fun s : ℝ => schwartzHsMultiplier (normalTestSection ψ t s) f)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (schwartzHsMultiplier (normalTestSection ψ t 0) f)) := by
  obtain ⟨C, hC, hbound⟩ := translated_test_multiplier ψ 1 (by norm_num)
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _)
  · have hsmall : ∀ᶠ s : ℝ in nhdsWithin 0 {0}ᶜ, |s| ≤ 1 := by
      apply Filter.Eventually.filter_mono inf_le_left
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)]
        with s hs
      change dist s 0 < 1 at hs
      simpa [Real.dist_eq] using hs.le
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs1 hsne
    have habs : 0 < |s| := abs_pos.mpr (by simpa using hsne)
    obtain ⟨g, hgphys, hgnorm⟩ := hbound t s habs (by simpa using hs1) f
    have hgeq :
        schwartzHsMultiplier (normalTestSection ψ t s) f -
            schwartzHsMultiplier (normalTestSection ψ t 0) f = g := by
      rw [normalTestMultiplier_sub]
      apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
      apply Lp.ext
      filter_upwards [schwartzHsMultiplier_toL2_ae
        (normalTestDifference ψ t s) f, hgphys] with z hm hg
      rw [hm, hg]
      simp only [normalTestDifference_apply]
      ring
    rw [hgeq]
    exact hgnorm
  · have habs : Tendsto (fun s : ℝ => |s|) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      change Tendsto abs (nhds (0 : ℝ) ⊓ Filter.principal ({0}ᶜ : Set ℝ)) (nhds 0)
      simpa only [abs_zero] using
        (continuous_abs.tendsto (0 : ℝ)).mono_left
          (show nhds (0 : ℝ) ⊓ Filter.principal ({0}ᶜ : Set ℝ) ≤ nhds 0 from
            inf_le_left)
    have hmul : Tendsto (fun s : ℝ => (C * ‖f‖) * |s|)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      simpa using habs.const_mul (C * ‖f‖)
    convert hmul using 1
    funext s
    ring

/-- Scalarization of a normal-coordinate spacetime field against `(t,r)` test data. -/
def normalScalarization (F : ℝ × (ℝ × ℝ) → ℂ)
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (s : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, F (z.1, (s, z.2)) * ψ z ∂(volume.prod volume)

/-- Scalarization formed from the jointly measurable exterior representative.
Unlike `normalScalarization`, this is the representative that occurs in the
proved weak equation. -/
def measurableNormalScalarization {σ : ℝ} (u v : GlobalSolution σ)
    (ψ : ℝ × ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, measurableNormalExterior u v (z.1, (s, z.2)) * ψ z
    ∂(volume.prod volume)

/-- Antisymmetry of the exterior product makes every fixed tangential
scalarization odd in the normal coordinate. -/
lemma measurableNormalScalarization_neg {σ : ℝ} (u v : GlobalSolution σ)
    (ψ : ℝ × ℝ → ℂ) (s : ℝ) :
    measurableNormalScalarization u v ψ (-s) =
      -measurableNormalScalarization u v ψ s := by
  unfold measurableNormalScalarization
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with z
  rw [show ((-s, z.2) : ℝ × ℝ) = normalReflection (s, z.2) by
    simp [normalReflection]]
  rw [measurableNormalExterior_reflection]
  ring

/-- In particular, the measurable scalarization has an exact zero
Dirichlet value, independently of any choice of `L²` representative. -/
@[simp] lemma measurableNormalScalarization_zero {σ : ℝ}
    (u v : GlobalSolution σ) (ψ : ℝ × ℝ → ℂ) :
    measurableNormalScalarization u v ψ 0 = 0 := by
  have h := measurableNormalScalarization_neg u v ψ 0
  simp only [neg_zero] at h
  have htwo : (2 : ℂ) * measurableNormalScalarization u v ψ 0 = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- `def:dirichlet-trace`: diagonal value of the scalarized `C¹` representative. -/
def dirichletTrace (u v : ℝ → L2) (ψ : 𝓢(ℝ × ℝ, ℂ)) : ℂ :=
  normalScalarization (normalExterior u v) ψ 0

/-- `prop:Dirichlet-trace`: antisymmetry makes the diagonal trace vanish. -/
theorem dirichlet_trace_zero (u v : ℝ → L2) (ψ : 𝓢(ℝ × ℝ, ℂ)) :
    dirichletTrace u v ψ = 0 := by
  simp [dirichletTrace, normalScalarization, normalExterior, exteriorProduct,
    fromNormalCoordinates, mul_comm]

/-- `def:neumann-trace`: normal derivative of the scalarized `C¹` representative. -/
def neumannTrace (u v : ℝ → L2) (ψ : 𝓢(ℝ × ℝ, ℂ)) : ℂ :=
  deriv (normalScalarization (normalExterior u v) ψ) 0

/-- `lem:neumann-localization`: nested cutoffs localize every translated test. -/
theorem neumann_localization (σ : ℝ) (u v : GlobalSolution σ)
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (hψ : HasCompactSupport (ψ : ℝ × ℝ → ℂ))
    (s0 : ℝ) (hs0 : 0 < s0) :
  ∃ χ0 χ1 : 𝓢(ℝ, ℂ),
    HasCompactSupport (χ0 : ℝ → ℂ) ∧ HasCompactSupport (χ1 : ℝ → ℂ) ∧
    (∀ t z s, |s| ≤ s0 → ψ (t, Real.sqrt 2 * z + s) ≠ 0 →
      χ0 z = 1 ∧ χ1 z = 1 ∧ χ1 (z + Real.sqrt 2 * s) = 1) ∧
    ∀ t : ℝ,
      HasCompactSupport (normalTestSection ψ t 0 : ℝ → ℂ) ∧
      ∀ x ∈ Metric.closedBall (0 : ℝ) 1 +
          tsupport (normalTestSection ψ t 0 : ℝ → ℂ),
        χ1 x = 1 ∧ deriv (χ1 : ℝ → ℂ) x = 0 := by
  obtain ⟨R, hR⟩ := hψ.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let L : ℝ := |R| + s0 + Real.sqrt 2 * s0 + 1
  have hL : 0 < L := by
    dsimp [L]
    positivity
  let b : ContDiffBump (0 : ℝ) := ⟨L, L + 1, hL, by linarith⟩
  let χfun : ℝ → ℂ := fun x => (b x : ℂ)
  have hχc : HasCompactSupport χfun := by
    have hb := b.hasCompactSupport.comp_left
      (g := fun x : ℝ => (x : ℂ)) (by norm_num)
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ (b : ℝ → ℝ))
    exact hb
  have hχd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χfun := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  let χ : 𝓢(ℝ, ℂ) := hχc.toSchwartzMap hχd
  have hχapply (x : ℝ) : χ x = (b x : ℂ) := rfl
  have hone (x : ℝ) (hx : |x| ≤ L) : χ x = 1 := by
    rw [hχapply]
    norm_cast
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, Real.dist_0_eq_abs, b] using hx
  have hflat (x : ℝ) (hx : |x| < L) :
      χ x = 1 ∧ deriv (χ : ℝ → ℂ) x = 0 := by
    have hxmem : x ∈ Metric.ball (0 : ℝ) b.rIn := by
      simpa [Metric.mem_ball, Real.dist_0_eq_abs, b] using hx
    have heq : (b : ℝ → ℝ) =ᶠ[nhds x] (1 : ℝ → ℝ) :=
      b.eventuallyEq_one_of_mem_ball hxmem
    have heqC : χfun =ᶠ[nhds x] (1 : ℝ → ℂ) := by
      filter_upwards [heq] with y hy
      change ((b y : ℝ) : ℂ) = 1
      rw [hy]
      norm_num
    constructor
    · change χfun x = 1
      exact heqC.eq_of_nhds
    · change deriv χfun x = 0
      rw [heqC.deriv_eq]
      exact (hasDerivAt_const x (1 : ℂ)).deriv
  refine ⟨χ, χ, ?_, ?_, ?_, ?_⟩
  · exact hχc
  · exact hχc
  · intro t z s hs hψnz
    have hp : (t, Real.sqrt 2 * z + s) ∈ tsupport (ψ : ℝ × ℝ → ℂ) :=
      subset_tsupport _ hψnz
    have hpball := hR hp
    have hsecond : |Real.sqrt 2 * z + s| ≤ R := by
      have hnorm : ‖(t, Real.sqrt 2 * z + s)‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hpball
      exact (show |Real.sqrt 2 * z + s| ≤ ‖(t, Real.sqrt 2 * z + s)‖ by
        simp only [Prod.norm_def, Real.norm_eq_abs]
        exact le_max_right _ _).trans hnorm
    have hz : |z| ≤ |R| + s0 := by
      have hsqrt : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      have hraw : Real.sqrt 2 * |z| ≤ |R| + s0 := by
        calc
          Real.sqrt 2 * |z| = |Real.sqrt 2 * z| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
          _ = |(Real.sqrt 2 * z + s) - s| := by ring_nf
          _ ≤ |Real.sqrt 2 * z + s| + |s| := abs_sub _ _
          _ ≤ |R| + s0 := by
            have hRle : |Real.sqrt 2 * z + s| ≤ |R| :=
              hsecond.trans (le_abs_self R)
            gcongr
      nlinarith [abs_nonneg z]
    have hzL : |z| ≤ L := by
      dsimp [L]
      linarith [mul_nonneg (Real.sqrt_nonneg 2) hs0.le]
    have hshift : |z + Real.sqrt 2 * s| ≤ L := by
      calc
        |z + Real.sqrt 2 * s| ≤ |z| + |Real.sqrt 2 * s| := abs_add_le _ _
        _ = |z| + Real.sqrt 2 * |s| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
        _ ≤ (|R| + s0) + Real.sqrt 2 * s0 := by gcongr
        _ ≤ L := by dsimp [L]; linarith
    exact ⟨hone z hzL, hone z hzL, hone (z + Real.sqrt 2 * s) hshift⟩
  · intro t
    have hsecSubset : tsupport (normalTestSection ψ t 0 : ℝ → ℂ) ⊆
        Metric.closedBall (0 : ℝ) |R| := by
      intro z hz
      have hp : (t, Real.sqrt 2 * z) ∈ tsupport (ψ : ℝ × ℝ → ℂ) := by
        have hp' := tsupport_comp_subset_preimage (f := fun z : ℝ =>
          (t, Real.sqrt 2 * z + 0)) (ψ : ℝ × ℝ → ℂ) (by fun_prop) hz
        change (t, Real.sqrt 2 * z + 0) ∈ tsupport (ψ : ℝ × ℝ → ℂ) at hp'
        simpa using hp'
      have hpball := hR hp
      have hsecond : |Real.sqrt 2 * z| ≤ |R| := by
        have hn : ‖(t, Real.sqrt 2 * z)‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hpball
        exact (show |Real.sqrt 2 * z| ≤ ‖(t, Real.sqrt 2 * z)‖ by
          simp only [Prod.norm_def, Real.norm_eq_abs]
          exact le_max_right _ _).trans (hn.trans (le_abs_self R))
      have hsqrt : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)] at hsecond
      have hzR : |z| ≤ |R| := by nlinarith [abs_nonneg z]
      simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using hzR
    have hsecCompact : HasCompactSupport
        (normalTestSection ψ t 0 : ℝ → ℂ) :=
      (isCompact_closedBall (0 : ℝ) |R|).of_isClosed_subset
        (isClosed_tsupport _) hsecSubset
    refine ⟨hsecCompact, ?_⟩
    intro x hx
    rcases Set.mem_add.mp hx with ⟨q, hq, z, hz, rfl⟩
    have hq1 : |q| ≤ 1 := by
      simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using hq
    have hzR : |z| ≤ |R| := by
      have := hsecSubset hz
      simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using this
    apply hflat
    calc
      |q + z| ≤ |q| + |z| := abs_add_le _ _
      _ ≤ 1 + |R| := by gcongr
      _ < L := by
        dsimp [L]
        nlinarith [hs0, mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hs0]

/-- The derivative and difference quotient selected by the proved Fourier interface. -/
noncomputable def hsDerivative : Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)) :=
  Classical.choose translation_dq

noncomputable def hsDifferenceQuotient (h : ℝ) :
    Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)) :=
  (Classical.choose (Classical.choose_spec translation_dq)) h

lemma hsDifferenceQuotient_eq_hsNegOfL2 (h : ℝ) (hh : h ≠ 0)
    (f : Hs (1 / 2 : ℝ)) :
    hsDifferenceQuotient h f =
      hsNegOfL2 (((h : ℂ)⁻¹) •
        (translateL2 h (Hs.toL2 (by norm_num) f) -
          Hs.toL2 (by norm_num) f)) := by
  apply Hs.toTempered_injective (-(1 / 2 : ℝ))
  rw [hsNegOfL2_toTempered]
  exact (Classical.choose_spec (Classical.choose_spec translation_dq)).2.1 h hh f

lemma hsDerivative_eq_criticalDerivative : hsDerivative = criticalDerivative := rfl

theorem hsDifferenceQuotient_scaled_tendsto (f : Hs (1 / 2 : ℝ)) :
    Tendsto (fun s : ℝ =>
      (Real.sqrt 2 : ℂ) • hsDifferenceQuotient (Real.sqrt 2 * s) f)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((Real.sqrt 2 : ℂ) • hsDerivative f)) := by
  let D := Classical.choose translation_dq
  let Q := Classical.choose (Classical.choose_spec translation_dq)
  obtain ⟨hD, hQ, hconv, C, hC, hQbound⟩ :=
    Classical.choose_spec (Classical.choose_spec translation_dq)
  have hk : 0 < Real.sqrt 2 := by positivity
  have hscale : Tendsto (fun s : ℝ => Real.sqrt 2 * s)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((tendsto_const_nhds.mul tendsto_id).mono_left inf_le_left :
          Tendsto (fun s : ℝ => Real.sqrt 2 * s)
            (nhdsWithin 0 {0}ᶜ) (nhds (Real.sqrt 2 * 0)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero,
        ne_eq, hk.ne', false_or] using hs
  have hq : Tendsto (fun s : ℝ => Q (Real.sqrt 2 * s) f)
      (nhdsWithin 0 {0}ᶜ) (nhds (D f)) := by
    change Tendsto (((fun h => Q h f) ∘ fun s : ℝ => Real.sqrt 2 * s))
      (nhdsWithin 0 {0}ᶜ) (nhds (D f))
    exact (hconv f).comp hscale
  simpa only [hsDifferenceQuotient, hsDerivative] using
    hq.const_smul (Real.sqrt 2 : ℂ)

def neumannHsIntegrand (ψ : 𝓢(ℝ × ℝ, ℂ))
    (U V : ℝ → Hs (1 / 2 : ℝ)) (s t : ℝ) : ℂ :=
  criticalPairingCLM
      ((Real.sqrt 2 : ℂ) • hsDifferenceQuotient (Real.sqrt 2 * s) (U t))
      (schwartzHsMultiplier (normalTestSection ψ t s) (V t)) -
    criticalPairingCLM
      ((Real.sqrt 2 : ℂ) • hsDifferenceQuotient (Real.sqrt 2 * s) (V t))
      (schwartzHsMultiplier (normalTestSection ψ t s) (U t))

/-- The normal difference-quotient integrand has a uniform bilinear bound,
independent of the nonzero normal displacement. -/
theorem neumannHsIntegrand_norm_le (ψ : 𝓢(ℝ × ℝ, ℂ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U V : ℝ → Hs (1 / 2 : ℝ)) (s t : ℝ), s ≠ 0 →
      ‖neumannHsIntegrand ψ U V s t‖ ≤ K * ‖U t‖ * ‖V t‖ := by
  let Cq : ℝ := Classical.choose
    (Classical.choose_spec (Classical.choose_spec translation_dq)).2.2.2
  have hCq : 0 ≤ Cq :=
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec translation_dq)).2.2.2).1
  have hQ :=
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec translation_dq)).2.2.2).2
  let Cm : ℝ := Real.sqrt smoothHsMultiplierConstantSq.toReal *
    (SchwartzMap.seminorm ℂ 0 0 ψ +
      Real.sqrt 2 * SchwartzMap.seminorm ℂ 0 0 (normalPartial ψ))
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  let K : ℝ := 2 * Real.sqrt 2 * Cq * Cm
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro U V s t hs
  have hsqrt : Real.sqrt 2 * s ≠ 0 := mul_ne_zero (by positivity) hs
  have hqu : ‖(Real.sqrt 2 : ℂ) •
      hsDifferenceQuotient (Real.sqrt 2 * s) (U t)‖ ≤
      Real.sqrt 2 * Cq * ‖U t‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    simpa only [hsDifferenceQuotient, Cq, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hQ _ hsqrt (U t))
        (Real.sqrt_nonneg 2))
  have hqv : ‖(Real.sqrt 2 : ℂ) •
      hsDifferenceQuotient (Real.sqrt 2 * s) (V t)‖ ≤
      Real.sqrt 2 * Cq * ‖V t‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    simpa only [hsDifferenceQuotient, Cq, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hQ _ hsqrt (V t))
        (Real.sqrt_nonneg 2))
  have hmu : ‖schwartzHsMultiplier (normalTestSection ψ t s) (U t)‖ ≤
      Cm * ‖U t‖ := by
    simpa [Cm] using normalTestSection_multiplier_norm_le ψ t s (U t)
  have hmv : ‖schwartzHsMultiplier (normalTestSection ψ t s) (V t)‖ ≤
      Cm * ‖V t‖ := by
    simpa [Cm] using normalTestSection_multiplier_norm_le ψ t s (V t)
  have hpair (T : Hs (-(1 / 2 : ℝ))) (f : Hs (1 / 2 : ℝ)) :
      ‖criticalPairingCLM T f‖ ≤ ‖T‖ * ‖f‖ := by
    change ‖hsNegPairing T f‖ ≤ _
    exact hsNegPairing_bound T f
  unfold neumannHsIntegrand
  calc
    ‖criticalPairingCLM
          ((Real.sqrt 2 : ℂ) • hsDifferenceQuotient (Real.sqrt 2 * s) (U t))
          (schwartzHsMultiplier (normalTestSection ψ t s) (V t)) -
        criticalPairingCLM
          ((Real.sqrt 2 : ℂ) • hsDifferenceQuotient (Real.sqrt 2 * s) (V t))
          (schwartzHsMultiplier (normalTestSection ψ t s) (U t))‖ ≤
        ‖(Real.sqrt 2 : ℂ) • hsDifferenceQuotient
            (Real.sqrt 2 * s) (U t)‖ *
            ‖schwartzHsMultiplier (normalTestSection ψ t s) (V t)‖ +
          ‖(Real.sqrt 2 : ℂ) • hsDifferenceQuotient
            (Real.sqrt 2 * s) (V t)‖ *
            ‖schwartzHsMultiplier (normalTestSection ψ t s) (U t)‖ :=
      (norm_sub_le _ _).trans (add_le_add (hpair _ _) (hpair _ _))
    _ ≤ (Real.sqrt 2 * Cq * ‖U t‖) * (Cm * ‖V t‖) +
        (Real.sqrt 2 * Cq * ‖V t‖) * (Cm * ‖U t‖) := by
      gcongr <;> positivity
    _ = K * ‖U t‖ * ‖V t‖ := by dsimp [K]; ring

theorem neumannHsIntegrand_tendsto (ψ : 𝓢(ℝ × ℝ, ℂ))
    (U V : ℝ → Hs (1 / 2 : ℝ)) (t : ℝ) :
    Tendsto (fun s : ℝ => neumannHsIntegrand ψ U V s t)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((Real.sqrt 2 : ℂ) *
        criticalWronskianCurrent (U t) (V t) (normalTestSection ψ t 0))) := by
  have hpair : Continuous (fun p : Hs (-(1 / 2 : ℝ)) × Hs (1 / 2 : ℝ) =>
      criticalPairingCLM p.1 p.2) :=
    Continuous.clm_apply (criticalPairingCLM.continuous.comp continuous_fst)
      continuous_snd
  have hU := hsDifferenceQuotient_scaled_tendsto (U t)
  have hV := hsDifferenceQuotient_scaled_tendsto (V t)
  have htestU := translated_test_multiplier_tendsto ψ t (U t)
  have htestV := translated_test_multiplier_tendsto ψ t (V t)
  have hfirst := (hpair.tendsto
    ((Real.sqrt 2 : ℂ) • hsDerivative (U t),
      schwartzHsMultiplier (normalTestSection ψ t 0) (V t))).comp
        (hU.prodMk_nhds htestV)
  have hsecond := (hpair.tendsto
    ((Real.sqrt 2 : ℂ) • hsDerivative (V t),
      schwartzHsMultiplier (normalTestSection ψ t 0) (U t))).comp
        (hV.prodMk_nhds htestU)
  have hout := hfirst.sub hsecond
  have hout' : Tendsto (fun s => neumannHsIntegrand ψ U V s t)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (criticalPairingCLM
          ((Real.sqrt 2 : ℂ) • hsDerivative (U t))
          (schwartzHsMultiplier (normalTestSection ψ t 0) (V t)) -
        criticalPairingCLM
          ((Real.sqrt 2 : ℂ) • hsDerivative (V t))
          (schwartzHsMultiplier (normalTestSection ψ t 0) (U t)))) := by
    simpa only [neumannHsIntegrand, Function.comp_apply] using hout
  convert hout' using 1
  congr 2
  have hsmul (T : Hs (-(1 / 2 : ℝ))) (q : Hs (1 / 2 : ℝ)) :
      criticalPairingCLM ((Real.sqrt 2 : ℂ) • T) q =
        (Real.sqrt 2 : ℂ) * criticalPairingCLM T q := by
    have h := congrArg (fun L : Hs (1 / 2 : ℝ) →L[ℂ] ℂ => L q)
      (map_smul criticalPairingCLM (Real.sqrt 2 : ℂ) T)
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
  rw [hsmul, hsmul]
  simp only [criticalWronskianCurrent, hsDerivative_eq_criticalDerivative]
  ring

theorem localizedSolutionHsCurve_toL2_ae
    (χ : SchwartzMap ℝ ℂ) (σ : ℝ) (u : GlobalSolution σ)
    (A B : ℝ) (hAB : A ≤ B) :
    ∀ᵐ t : ℝ ∂timeMeasure A B,
      Hs.toL2 (by norm_num)
          ((localizedSolutionHsCurve χ σ u A B hAB :
            ℝ → Hs (1 / 2 : ℝ)) t) =
        cutoffL2CLM χ (u.u t) := by
  filter_upwards [localizedSolutionHsCurve_represents χ σ u A B hAB] with t ht
  rw [Hs.toTempered_toL2 (s := (1 / 2 : ℝ)) (by norm_num)] at ht
  have hinj : Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2 :
        L2 →L[ℂ] TemperedDistribution ℝ ℂ) :=
    LinearMap.ker_eq_bot.mp (by
      simpa using
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := ℂ) (E := ℝ) (μ := volume) (p := (2 : ℝ≥0∞))))
  apply hinj
  change MeasureTheory.Lp.toTemperedDistribution
      (Hs.toL2 (by norm_num)
        ((localizedSolutionHsCurve χ σ u A B hAB :
          ℝ → Hs (1 / 2 : ℝ)) t)) =
    MeasureTheory.Lp.toTemperedDistribution (cutoffL2CLM χ (u.u t))
  rw [toTemperedDistribution_cutoffL2CLM]
  exact ht

def neumannPhysicalIntegrand (σ : ℝ) (u v : GlobalSolution σ)
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (s t : ℝ) : ℂ :=
  ∫ z : ℝ,
    (((s : ℂ)⁻¹ *
          (solutionRepresentative σ u (t, z + Real.sqrt 2 * s) -
            solutionRepresentative σ u (t, z))) *
        solutionRepresentative σ v (t, z) -
      ((s : ℂ)⁻¹ *
          (solutionRepresentative σ v (t, z + Real.sqrt 2 * s) -
            solutionRepresentative σ v (t, z))) *
        solutionRepresentative σ u (t, z)) *
      translatedNormalTest ψ t s z

lemma neumannPhysicalIntegrand_aestronglyMeasurable (σ : ℝ)
    (u v : GlobalSolution σ) (ψ : 𝓢(ℝ × ℝ, ℂ)) (s : ℝ) :
    AEStronglyMeasurable (neumannPhysicalIntegrand σ u v ψ s) volume := by
  let G : ℝ × ℝ → ℂ := fun p =>
    (((s : ℂ)⁻¹ *
          (solutionRepresentative σ u (p.1, p.2 + Real.sqrt 2 * s) -
            solutionRepresentative σ u (p.1, p.2))) *
        solutionRepresentative σ v (p.1, p.2) -
      ((s : ℂ)⁻¹ *
          (solutionRepresentative σ v (p.1, p.2 + Real.sqrt 2 * s) -
            solutionRepresentative σ v (p.1, p.2))) *
        solutionRepresentative σ u (p.1, p.2)) *
      translatedNormalTest ψ p.1 s p.2
  have hG : Measurable G := by
    dsimp [G, translatedNormalTest]
    have hu := solutionRepresentative_measurable σ u
    have hv := solutionRepresentative_measurable σ v
    fun_prop
  change AEStronglyMeasurable (fun t => ∫ z, G (t, z)) volume
  exact hG.aestronglyMeasurable.integral_prod_right'

/-- The affine tangential change of variables identifies the physical normal
difference quotient with the quotient of the measurable scalarized slice. -/
lemma sqrt_two_mul_neumannPhysicalIntegrand
    (σ : ℝ) (u v : GlobalSolution σ) (ψ : 𝓢(ℝ × ℝ, ℂ))
    (s t : ℝ) (hs : s ≠ 0) :
    (Real.sqrt 2 : ℂ) * neumannPhysicalIntegrand σ u v ψ s t =
      (s : ℂ)⁻¹ * ∫ r : ℝ,
        measurableNormalExterior u v (t, (s, r)) * ψ (t, r) := by
  let f : ℝ → ℂ := fun r =>
    (s : ℂ)⁻¹ * measurableNormalExterior u v (t, (s, r)) * ψ (t, r)
  have hpoint (z : ℝ) :
      f (Real.sqrt 2 * z + s) =
        (((s : ℂ)⁻¹ *
              (solutionRepresentative σ u (t, z + Real.sqrt 2 * s) -
                solutionRepresentative σ u (t, z))) *
            solutionRepresentative σ v (t, z) -
          ((s : ℂ)⁻¹ *
              (solutionRepresentative σ v (t, z + Real.sqrt 2 * s) -
                solutionRepresentative σ v (t, z))) *
            solutionRepresentative σ u (t, z)) *
          translatedNormalTest ψ t s z := by
    simp only [f, measurableNormalExterior, measurableExterior,
      fromNormalCoordinates, translatedNormalTest]
    have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
    have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hx : (Real.sqrt 2 * z + s + s) / Real.sqrt 2 =
        z + Real.sqrt 2 * s := by
      apply (div_eq_iff hsqrt).2
      calc
        Real.sqrt 2 * z + s + s = Real.sqrt 2 * z + 2 * s := by ring
        _ = Real.sqrt 2 * (z + Real.sqrt 2 * s) := by
          rw [mul_add, ← mul_assoc, ← pow_two, hsqrt2]
        _ = (z + Real.sqrt 2 * s) * Real.sqrt 2 := by ring
    have hy : (Real.sqrt 2 * z + s - s) / Real.sqrt 2 = z := by
      apply (div_eq_iff hsqrt).2
      ring
    rw [hx, hy]
    field_simp [hs]
    ring
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ => f (x + s)) (Real.sqrt 2)
  have hadd := (MeasureTheory.measurePreserving_add_right
    (volume : Measure ℝ) s).integral_comp
      (MeasurableEquiv.addRight s).measurableEmbedding f
  rw [neumannPhysicalIntegrand]
  have heq : (∫ z : ℝ,
      (((s : ℂ)⁻¹ *
            (solutionRepresentative σ u (t, z + Real.sqrt 2 * s) -
              solutionRepresentative σ u (t, z))) *
          solutionRepresentative σ v (t, z) -
        ((s : ℂ)⁻¹ *
            (solutionRepresentative σ v (t, z + Real.sqrt 2 * s) -
              solutionRepresentative σ v (t, z))) *
          solutionRepresentative σ u (t, z)) *
        translatedNormalTest ψ t s z) =
      ∫ z : ℝ, f (Real.sqrt 2 * z + s) := by
    apply integral_congr_ae
    filter_upwards with z
    exact (hpoint z).symm
  rw [heq]
  change (Real.sqrt 2 : ℂ) * (∫ z : ℝ,
      f (Real.sqrt 2 * z + s)) = _
  rw [hscale, hadd]
  change (Real.sqrt 2 : ℂ) *
      ((|(Real.sqrt 2)⁻¹| : ℝ) • (∫ r : ℝ, f r)) = _
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < Real.sqrt 2))]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  rw [Complex.real_smul]
  have hcoef : (Real.sqrt 2 : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [← mul_assoc, hcoef, one_mul]
  simp only [f]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  ring

private lemma hsNegOfL2_smul_diagonal (c : ℂ) (q : L2) :
    c • hsNegOfL2 q = hsNegOfL2 (c • q) := by
  simp [hsNegOfL2]

set_option maxHeartbeats 5000000 in
lemma neumannHsIntegrand_eq_physical_of_toL2
    (σ : ℝ) (u v : GlobalSolution σ) (ψ : 𝓢(ℝ × ℝ, ℂ))
    (χ : 𝓢(ℝ, ℂ)) (s0 s t : ℝ) (hs : s ≠ 0) (hs0 : |s| ≤ s0)
    (hχ : ∀ z, ψ (t, Real.sqrt 2 * z + s) ≠ 0 →
      χ z = 1 ∧ χ (z + Real.sqrt 2 * s) = 1)
    (U V : Hs (1 / 2 : ℝ))
    (hU : Hs.toL2 (by norm_num) U = cutoffL2CLM χ (u.u t))
    (hV : Hs.toL2 (by norm_num) V = cutoffL2CLM χ (v.u t)) :
    neumannHsIntegrand ψ (fun _ => U) (fun _ => V) s t =
      neumannPhysicalIntegrand σ u v ψ s t := by
  let h : ℝ := Real.sqrt 2 * s
  have hh : h ≠ 0 := mul_ne_zero (by positivity) hs
  let qU : L2 := ((h : ℂ)⁻¹) •
    (translateL2 h (Hs.toL2 (by norm_num) U) - Hs.toL2 (by norm_num) U)
  let qV : L2 := ((h : ℂ)⁻¹) •
    (translateL2 h (Hs.toL2 (by norm_num) V) - Hs.toL2 (by norm_num) V)
  let mU : Hs (1 / 2 : ℝ) :=
    schwartzHsMultiplier (normalTestSection ψ t s) U
  let mV : Hs (1 / 2 : ℝ) :=
    schwartzHsMultiplier (normalTestSection ψ t s) V
  have hpairU : criticalPairingCLM
      ((Real.sqrt 2 : ℂ) • hsDifferenceQuotient h U) mV =
      ∫ z : ℝ, ((Real.sqrt 2 : ℂ) • qU : L2) z *
        (Hs.toL2 (by norm_num) mV : ℝ → ℂ) z := by
    rw [hsDifferenceQuotient_eq_hsNegOfL2 h hh U,
      hsNegOfL2_smul_diagonal, show criticalPairingCLM
        (hsNegOfL2 ((Real.sqrt 2 : ℂ) • qU)) mV =
          hsNegPairing (hsNegOfL2 ((Real.sqrt 2 : ℂ) • qU)) mV by rfl,
      hsNegPairing_hsNegOfL2]
  have hpairV : criticalPairingCLM
      ((Real.sqrt 2 : ℂ) • hsDifferenceQuotient h V) mU =
      ∫ z : ℝ, ((Real.sqrt 2 : ℂ) • qV : L2) z *
        (Hs.toL2 (by norm_num) mU : ℝ → ℂ) z := by
    rw [hsDifferenceQuotient_eq_hsNegOfL2 h hh V,
      hsNegOfL2_smul_diagonal, show criticalPairingCLM
        (hsNegOfL2 ((Real.sqrt 2 : ℂ) • qV)) mU =
          hsNegPairing (hsNegOfL2 ((Real.sqrt 2 : ℂ) • qV)) mU by rfl,
      hsNegPairing_hsNegOfL2]
  have hu := solutionRepresentative_slice σ u t
  have hv := solutionRepresentative_slice σ v t
  have hqU : ∀ᵐ z : ℝ ∂volume, ψ (t, Real.sqrt 2 * z + s) ≠ 0 →
      (((Real.sqrt 2 : ℂ) • qU : L2) : ℝ → ℂ) z =
      (s : ℂ)⁻¹ *
        (solutionRepresentative σ u (t, z + Real.sqrt 2 * s) -
          solutionRepresentative σ u (t, z)) := by
    simp only [qU, hU]
    have hushift := (MeasureTheory.measurePreserving_add_right
      (volume : Measure ℝ) h).quasiMeasurePreserving.ae hu
    filter_upwards [Lp.coeFn_smul (Real.sqrt 2 : ℂ)
        (((h : ℂ)⁻¹) •
          (translateL2 h (cutoffL2CLM χ (u.u t)) - cutoffL2CLM χ (u.u t))),
      Lp.coeFn_smul ((h : ℂ)⁻¹)
        (translateL2 h (cutoffL2CLM χ (u.u t)) - cutoffL2CLM χ (u.u t)),
      Lp.coeFn_sub (translateL2 h (cutoffL2CLM χ (u.u t)))
        (cutoffL2CLM χ (u.u t)),
      coe_translateL2 h (cutoffL2CLM χ (u.u t)),
      (MeasureTheory.measurePreserving_add_right
        (volume : Measure ℝ) h).quasiMeasurePreserving.ae
          (coe_cutoffL2CLM χ (u.u t)),
      coe_cutoffL2CLM χ (u.u t), hushift, hu] with z hc hhsm hsub htr hcshift hc0 hur hu0
    intro hψz
    rw [hc]
    change (Real.sqrt 2 : ℂ) *
      ((((h : ℂ)⁻¹) •
        (translateL2 h (cutoffL2CLM χ (u.u t)) -
          cutoffL2CLM χ (u.u t)) : L2) : ℝ → ℂ) z = _
    rw [hhsm]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [htr, hcshift, hc0]
    obtain ⟨hχ0, hχs⟩ := hχ z hψz
    rw [hχ0, hχs, one_mul, hur, hu0]
    simp only [h]
    push_cast
    field_simp
  have hqV : ∀ᵐ z : ℝ ∂volume, ψ (t, Real.sqrt 2 * z + s) ≠ 0 →
      (((Real.sqrt 2 : ℂ) • qV : L2) : ℝ → ℂ) z =
      (s : ℂ)⁻¹ *
        (solutionRepresentative σ v (t, z + Real.sqrt 2 * s) -
          solutionRepresentative σ v (t, z)) := by
    simp only [qV, hV]
    have hvshift := (MeasureTheory.measurePreserving_add_right
      (volume : Measure ℝ) h).quasiMeasurePreserving.ae hv
    filter_upwards [Lp.coeFn_smul (Real.sqrt 2 : ℂ)
        (((h : ℂ)⁻¹) •
          (translateL2 h (cutoffL2CLM χ (v.u t)) - cutoffL2CLM χ (v.u t))),
      Lp.coeFn_smul ((h : ℂ)⁻¹)
        (translateL2 h (cutoffL2CLM χ (v.u t)) - cutoffL2CLM χ (v.u t)),
      Lp.coeFn_sub (translateL2 h (cutoffL2CLM χ (v.u t)))
        (cutoffL2CLM χ (v.u t)),
      coe_translateL2 h (cutoffL2CLM χ (v.u t)),
      (MeasureTheory.measurePreserving_add_right
        (volume : Measure ℝ) h).quasiMeasurePreserving.ae
          (coe_cutoffL2CLM χ (v.u t)),
      coe_cutoffL2CLM χ (v.u t), hvshift, hv] with z hc hhsm hsub htr hcshift hc0 hvr hv0
    intro hψz
    rw [hc]
    change (Real.sqrt 2 : ℂ) *
      ((((h : ℂ)⁻¹) •
        (translateL2 h (cutoffL2CLM χ (v.u t)) -
          cutoffL2CLM χ (v.u t)) : L2) : ℝ → ℂ) z = _
    rw [hhsm]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [htr, hcshift, hc0]
    obtain ⟨hχ0, hχs⟩ := hχ z hψz
    rw [hχ0, hχs, one_mul, hvr, hv0]
    simp only [h]
    push_cast
    field_simp
  have hmV := schwartzHsMultiplier_toL2_ae (normalTestSection ψ t s) V
  have hmU := schwartzHsMultiplier_toL2_ae (normalTestSection ψ t s) U
  have htermU : (fun z => ((Real.sqrt 2 : ℂ) • qU : L2) z *
      (Hs.toL2 (by norm_num) mV : ℝ → ℂ) z) =ᵐ[volume]
      fun z => ((s : ℂ)⁻¹ *
          (solutionRepresentative σ u (t, z + Real.sqrt 2 * s) -
            solutionRepresentative σ u (t, z))) *
        solutionRepresentative σ v (t, z) * translatedNormalTest ψ t s z := by
    filter_upwards [hqU, hmV, hv, coe_cutoffL2CLM χ (v.u t)]
      with z hqu hmv hvz hcut
    rw [hmv, hV, hcut, hvz]
    by_cases hψz : ψ (t, Real.sqrt 2 * z + s) = 0
    · simp [translatedNormalTest, hψz]
    · rw [hqu hψz, (hχ z hψz).1, one_mul]
      simp only [normalTestSection_apply, translatedNormalTest]
      ring
  have htermV : (fun z => ((Real.sqrt 2 : ℂ) • qV : L2) z *
      (Hs.toL2 (by norm_num) mU : ℝ → ℂ) z) =ᵐ[volume]
      fun z => ((s : ℂ)⁻¹ *
          (solutionRepresentative σ v (t, z + Real.sqrt 2 * s) -
            solutionRepresentative σ v (t, z))) *
        solutionRepresentative σ u (t, z) * translatedNormalTest ψ t s z := by
    filter_upwards [hqV, hmU, hu, coe_cutoffL2CLM χ (u.u t)]
      with z hqv hmu huz hcut
    rw [hmu, hU, hcut, huz]
    by_cases hψz : ψ (t, Real.sqrt 2 * z + s) = 0
    · simp [translatedNormalTest, hψz]
    · rw [hqv hψz, (hχ z hψz).1, one_mul]
      simp only [normalTestSection_apply, translatedNormalTest]
      ring
  have hintU : Integrable (fun z => ((Real.sqrt 2 : ℂ) • qU : L2) z *
      (Hs.toL2 (by norm_num) mV : ℝ → ℂ) z) volume :=
    memLp_one_iff_integrable.mp ((Lp.memLp (Hs.toL2 (by norm_num) mV)).mul'
      (Lp.memLp ((Real.sqrt 2 : ℂ) • qU)))
  have hintV : Integrable (fun z => ((Real.sqrt 2 : ℂ) • qV : L2) z *
      (Hs.toL2 (by norm_num) mU : ℝ → ℂ) z) volume :=
    memLp_one_iff_integrable.mp ((Lp.memLp (Hs.toL2 (by norm_num) mU)).mul'
      (Lp.memLp ((Real.sqrt 2 : ℂ) • qV)))
  rw [neumannHsIntegrand, neumannPhysicalIntegrand]
  rw [show Real.sqrt 2 * s = h by rfl, hpairU, hpairV,
    integral_congr_ae htermU, integral_congr_ae htermV,
    ← integral_sub (hintU.congr htermU) (hintV.congr htermV)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [translatedNormalTest]
  ring

theorem neumann_strong_convergence (I : Set ℝ) (hI : MeasurableSet I)
    (U : ℝ → Hs (1 / 2 : ℝ))
    (hUmeas : AEStronglyMeasurable U (volume.restrict I))
    (hU : eLpNorm U 2 (volume.restrict I) < ⊤) :
  Tendsto (fun h : ℝ => eLpNorm (fun t =>
      (Real.sqrt 2 : ℂ) • hsDifferenceQuotient (Real.sqrt 2 * h) (U t) -
        (Real.sqrt 2 : ℂ) • hsDerivative (U t)) 2 (volume.restrict I))
    (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  let D := Classical.choose translation_dq
  let Q := Classical.choose (Classical.choose_spec translation_dq)
  have hD_id (f : Hs (1 / 2 : ℝ)) : hsDerivative f = D f := by
    rfl
  have hQ_id (h : ℝ) (f : Hs (1 / 2 : ℝ)) :
      hsDifferenceQuotient h f = Q h f := by
    rfl
  obtain ⟨hD, hQ, hconv, C, hC0, hQbound⟩ :=
    Classical.choose_spec (Classical.choose_spec translation_dq)
  let k : ℝ := Real.sqrt 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hscale : Tendsto (fun h : ℝ => k * h)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((tendsto_const_nhds.mul tendsto_id).mono_left inf_le_left :
          Tendsto (fun h : ℝ => k * h) (nhdsWithin 0 {0}ᶜ) (nhds (k * 0)))
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero,
        ne_eq, hk.ne', false_or] using hh
  have hD_bound (f : Hs (1 / 2 : ℝ)) : ‖D f‖ ≤ C * ‖f‖ := by
    exact le_of_tendsto (hconv f).norm
      (by
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact hQbound h (by simpa using hh) f)
  let Z : ℝ → ℝ → Hs (-(1 / 2 : ℝ)) := fun h t =>
    (k : ℂ) • Q (k * h) (U t) - (k : ℂ) • D (U t)
  have hpoint (t : ℝ) : Tendsto (fun h => Z h t)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hq : Tendsto (fun h => Q (k * h) (U t))
        (nhdsWithin 0 {0}ᶜ) (nhds (D (U t))) := by
      change Tendsto (((fun h => Q h (U t)) ∘ fun h => k * h))
        (nhdsWithin 0 {0}ᶜ) (nhds (D (U t)))
      exact (hconv (U t)).comp hscale
    have hs := hq.const_smul (k : ℂ)
    have hd : Tendsto (fun _ : ℝ => (k : ℂ) • D (U t))
        (nhdsWithin 0 {0}ᶜ) (nhds ((k : ℂ) • D (U t))) := tendsto_const_nhds
    simpa only [Z, sub_self] using hs.sub hd
  have hmeas (h : ℝ) : AEStronglyMeasurable (Z h) (volume.restrict I) := by
    have hQc : Continuous (fun f : Hs (1 / 2 : ℝ) => Q (k * h) f) := by
      dsimp only [Q, translation_dq]
      fun_prop
    have hDc : Continuous (fun f : Hs (1 / 2 : ℝ) => D f) := by
      dsimp only [D, translation_dq]
      fun_prop
    exact ((hQc.comp_aestronglyMeasurable hUmeas).const_smul
      (k : ℂ)).sub
        ((hDc.comp_aestronglyMeasurable hUmeas).const_smul
          (k : ℂ))
  let K : ℝ := 2 * k * C
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hbound : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
      ∀ t, ‖Z h t‖ ≤ K * ‖U t‖ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    intro t
    have hkh : k * h ≠ 0 := mul_ne_zero hk.ne' (by simpa using hh)
    calc
      ‖Z h t‖ ≤ ‖(k : ℂ) • Q (k * h) (U t)‖ +
          ‖(k : ℂ) • D (U t)‖ := norm_sub_le _ _
      _ = k * ‖Q (k * h) (U t)‖ + k * ‖D (U t)‖ := by
        simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hk.le]
      _ ≤ k * (C * ‖U t‖) + k * (C * ‖U t‖) := by
        gcongr
        · exact hQbound (k * h) hkh (U t)
        · exact hD_bound (U t)
      _ = K * ‖U t‖ := by dsimp [K]; ring
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hint : Tendsto (fun h =>
      ∫⁻ t, ‖Z h t‖ₑ ^ (2 : ℝ) ∂(volume.restrict I))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hDCT := tendsto_lintegral_filter_of_dominated_convergence'
      (l := nhdsWithin (0 : ℝ) {0}ᶜ) (μ := volume.restrict I)
      (F := fun h t => ‖Z h t‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun t => (ENNReal.ofReal K * ‖U t‖ₑ) ^ (2 : ℝ))
      (by
        filter_upwards with h
        exact (hmeas h).enorm.pow_const 2)
      (by
        filter_upwards [hbound] with h hh
        filter_upwards with t
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hh t))
      (by
        rw [show (fun t => (ENNReal.ofReal K * ‖U t‖ₑ) ^ (2 : ℝ)) =
            fun t => (ENNReal.ofReal K) ^ (2 : ℝ) * ‖U t‖ₑ ^ (2 : ℝ) by
          funext t
          exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
            (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hU).ne)
      (by
        filter_upwards with t
        have ht := (hpoint t).enorm
        have hp := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp ht
        simpa [Function.comp_def] using hp)
    simpa using hDCT
  convert hint.ennrpow_const (1 / ENNReal.toReal 2) using 1 <;>
    norm_num [Z, k, hQ_id, hD_id]

set_option maxHeartbeats 2000000 in
/-- After compact spatial localization, the normal difference quotient has
zero spacetime pairing.  This is the analytic Neumann trace statement used
at the boundary. -/
theorem neumannHsIntegral_tendsto_zero
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (hψ : HasCompactSupport (ψ : ℝ × ℝ → ℂ))
    (A B : ℝ) (hAB : A < B) (hABI : Set.Icc A B ⊆ I) :
    ∃ χ : 𝓢(ℝ, ℂ),
      Tendsto (fun s : ℝ => ∫ t,
          neumannHsIntegrand ψ
            (fun t => (localizedSolutionHsCurve χ σ u A B hAB.le :
              ℝ → Hs (1 / 2 : ℝ)) t)
            (fun t => (localizedSolutionHsCurve χ σ v A B hAB.le :
              ℝ → Hs (1 / 2 : ℝ)) t) s t
          ∂timeMeasure A B)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) ∧
      Tendsto (fun s : ℝ => ∫ t,
          neumannPhysicalIntegrand σ u v ψ s t ∂timeMeasure A B)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  obtain ⟨χ0, χ1, hχ0c, hχ1c, hχ, hflat⟩ :=
    neumann_localization σ u v ψ hψ 1 (by norm_num)
  let U : ℝ → Hs (1 / 2 : ℝ) := fun t =>
    (localizedSolutionHsCurve χ1 σ u A B hAB.le :
      ℝ → Hs (1 / 2 : ℝ)) t
  let V : ℝ → Hs (1 / 2 : ℝ) := fun t =>
    (localizedSolutionHsCurve χ1 σ v A B hAB.le :
      ℝ → Hs (1 / 2 : ℝ)) t
  have hU : MemLp U 2 (timeMeasure A B) := by
    exact Lp.memLp (localizedSolutionHsCurve χ1 σ u A B hAB.le)
  have hV : MemLp V 2 (timeMeasure A B) := by
    exact Lp.memLp (localizedSolutionHsCurve χ1 σ v A B hAB.le)
  obtain ⟨K, hK, hbound⟩ := neumannHsIntegrand_norm_le ψ
  have hdom : Integrable (fun t => K * ‖U t‖ * ‖V t‖)
      (timeMeasure A B) := by
    have hp : Integrable (fun t => ‖U t‖ * ‖V t‖)
        (timeMeasure A B) :=
      memLp_one_iff_integrable.mp (hV.norm.mul' hU.norm)
    simpa only [mul_assoc] using hp.const_mul K
  have hsmall : ∀ᶠ s : ℝ in nhdsWithin 0 {0}ᶜ, |s| ≤ 1 := by
    apply Filter.Eventually.filter_mono inf_le_left
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)]
      with s hs
    change dist s 0 < 1 at hs
    simpa [Real.dist_eq] using hs.le
  have hrepU := localizedSolutionHsCurve_toL2_ae χ1 σ u A B hAB.le
  have hrepV := localizedSolutionHsCurve_toL2_ae χ1 σ v A B hAB.le
  have heqPhysical (s : ℝ) (hs : s ≠ 0) (hs1 : |s| ≤ 1) :
      (fun t => neumannHsIntegrand ψ U V s t) =ᵐ[timeMeasure A B]
        neumannPhysicalIntegrand σ u v ψ s := by
    filter_upwards [hrepU, hrepV] with t hut hvt
    exact neumannHsIntegrand_eq_physical_of_toL2 σ u v ψ χ1 1 s t hs hs1
      (fun z hz => ⟨(hχ t z s hs1 hz).2.1, (hχ t z s hs1 hz).2.2⟩)
      (U t) (V t) hut hvt
  have hmeas : ∀ᶠ s : ℝ in nhdsWithin 0 {0}ᶜ,
      AEStronglyMeasurable (fun t => neumannHsIntegrand ψ U V s t)
        (timeMeasure A B) := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs1 hs
    have hsp : AEStronglyMeasurable (neumannPhysicalIntegrand σ u v ψ s)
        (timeMeasure A B) :=
      (neumannPhysicalIntegrand_aestronglyMeasurable σ u v ψ s).mono_measure
        Measure.restrict_le_self
    exact hsp.congr (heqPhysical s (by simpa using hs) hs1).symm
  have hw := localizedCriticalWronskian_common_ae σ u v I hI hmod χ1 hAB hABI
  have hlim : ∀ᵐ t ∂timeMeasure A B,
      Tendsto (fun s : ℝ => neumannHsIntegrand ψ U V s t)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    filter_upwards [hw] with t ht
    have hz := ht (normalTestSection ψ t 0) (hflat t).1 (hflat t).2
    have hbase := neumannHsIntegrand_tendsto ψ U V t
    rw [hz, mul_zero] at hbase
    exact hbase
  have hHs : Tendsto (fun s : ℝ => ∫ t,
      neumannHsIntegrand ψ U V s t ∂timeMeasure A B)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa using
      (tendsto_integral_filter_of_dominated_convergence
      (l := nhdsWithin (0 : ℝ) {0}ᶜ) (μ := timeMeasure A B)
      (F := fun s t => neumannHsIntegrand ψ U V s t) (f := fun _ => 0)
      (fun t => K * ‖U t‖ * ‖V t‖) hmeas
      (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        filter_upwards with t
        exact hbound U V s t (by simpa using hs))
      hdom hlim)
  have hintEq : ∀ᶠ s : ℝ in nhdsWithin 0 {0}ᶜ,
      (∫ t, neumannHsIntegrand ψ U V s t ∂timeMeasure A B) =
        ∫ t, neumannPhysicalIntegrand σ u v ψ s t ∂timeMeasure A B := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs1 hs
    exact integral_congr_ae (heqPhysical s (by simpa using hs) hs1)
  refine ⟨χ1, ?_, hHs.congr' hintEq⟩
  simpa [U, V] using hHs

/-- Scalarization with time restricted to one compact interval. -/
def measurableNormalScalarizationOn {σ : ℝ} (u v : GlobalSolution σ)
    (ψ : ℝ × ℝ → ℂ) (A B s : ℝ) : ℂ :=
  ∫ t, (∫ r : ℝ,
    measurableNormalExterior u v (t, (s, r)) * ψ (t, r)) ∂timeMeasure A B

lemma measurableNormalScalarizationOn_div_eq
    (σ : ℝ) (u v : GlobalSolution σ) (ψ : 𝓢(ℝ × ℝ, ℂ))
    (A B s : ℝ) (hs : s ≠ 0) :
    (s : ℂ)⁻¹ * measurableNormalScalarizationOn u v ψ A B s =
      (Real.sqrt 2 : ℂ) *
        ∫ t, neumannPhysicalIntegrand σ u v ψ s t ∂timeMeasure A B := by
  unfold measurableNormalScalarizationOn
  calc
    (s : ℂ)⁻¹ * (∫ t, (∫ r : ℝ,
        measurableNormalExterior u v (t, (s, r)) * ψ (t, r))
        ∂timeMeasure A B) =
        ∫ t, (s : ℂ)⁻¹ * (∫ r : ℝ,
          measurableNormalExterior u v (t, (s, r)) * ψ (t, r))
          ∂timeMeasure A B := (integral_const_mul _ _).symm
    _ = ∫ t, (Real.sqrt 2 : ℂ) *
          neumannPhysicalIntegrand σ u v ψ s t ∂timeMeasure A B := by
      apply integral_congr_ae
      filter_upwards with t
      exact (sqrt_two_mul_neumannPhysicalIntegrand σ u v ψ s t hs).symm
    _ = (Real.sqrt 2 : ℂ) *
        ∫ t, neumannPhysicalIntegrand σ u v ψ s t ∂timeMeasure A B :=
      integral_const_mul _ _

/-- The compact-time scalarized exterior has zero normal trace in the
difference-quotient sense. -/
theorem measurableNormalScalarizationOn_div_tendsto_zero
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (ψ : 𝓢(ℝ × ℝ, ℂ)) (hψ : HasCompactSupport (ψ : ℝ × ℝ → ℂ))
    (A B : ℝ) (hAB : A < B) (hABI : Set.Icc A B ⊆ I) :
    Tendsto (fun s : ℝ =>
        (s : ℂ)⁻¹ * measurableNormalScalarizationOn u v ψ A B s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  obtain ⟨χ, hHs, hphys⟩ := neumannHsIntegral_tendsto_zero
    σ u v I hI hmod ψ hψ A B hAB hABI
  have hout := hphys.const_mul (Real.sqrt 2 : ℂ)
  have hout' : Tendsto (fun s => (Real.sqrt 2 : ℂ) *
      ∫ t, neumannPhysicalIntegrand σ u v ψ s t ∂timeMeasure A B)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by simpa using hout
  apply hout'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (measurableNormalScalarizationOn_div_eq σ u v ψ A B s
    (by simpa using hs)).symm

/-- A compact spacetime support whose time projection lies in an open
interval is contained in a smaller closed time interval. -/
lemma exists_compact_time_interval
    (a b : ℝ) (hab : a < b) (Ψ : ℝ × (ℝ × ℝ) → ℂ)
    (hΨc : HasCompactSupport Ψ)
    (hΨI : ∀ p ∈ tsupport Ψ, p.1 ∈ Set.Ioo a b) :
    ∃ A B : ℝ, A < B ∧ Set.Icc A B ⊆ Set.Ioo a b ∧
      ∀ p ∈ tsupport Ψ, p.1 ∈ Set.Icc A B := by
  by_cases hne : (tsupport Ψ).Nonempty
  · obtain ⟨pmin, hpmin, hmin⟩ := hΨc.isCompact.exists_isMinOn hne
      continuous_fst.continuousOn
    obtain ⟨pmax, hpmax, hmax⟩ := hΨc.isCompact.exists_isMaxOn hne
      continuous_fst.continuousOn
    let A : ℝ := (a + pmin.1) / 2
    let B : ℝ := (pmax.1 + b) / 2
    have hpminI := hΨI pmin hpmin
    have hpmaxI := hΨI pmax hpmax
    rcases hpminI with ⟨hamin, hminb⟩
    rcases hpmaxI with ⟨hamax, hmaxb⟩
    have hminmax : pmin.1 ≤ pmax.1 := hmin hpmax
    have hAB : A < B := by dsimp [A, B]; linarith
    refine ⟨A, B, hAB, ?_, ?_⟩
    · intro t ht
      dsimp [A, B] at ht
      rcases ht with ⟨htA, htB⟩
      constructor <;> linarith
    · intro p hp
      have hlo := hmin hp
      have hhi := hmax hp
      change pmin.1 ≤ p.1 at hlo
      change p.1 ≤ pmax.1 at hhi
      dsimp [A, B]
      constructor <;> linarith
  · let A : ℝ := (3 * a + b) / 4
    let B : ℝ := (a + 3 * b) / 4
    have hAB : A < B := by dsimp [A, B]; linarith
    refine ⟨A, B, hAB, ?_, ?_⟩
    · intro t ht
      dsimp [A, B] at ht
      rcases ht with ⟨htA, htB⟩
      constructor <;> linarith
    · intro p hp
      exact False.elim (hne ⟨p, hp⟩)

private def lowerHalfCutoff (n : ℕ) (s : ℝ) : ℂ :=
  (Real.smoothTransition (-((n : ℝ) + 1) * s) : ℂ)

private def lowerHalfCutoffDeriv (n : ℕ) (s : ℝ) : ℂ :=
  (-((n : ℝ) + 1) : ℂ) *
    (deriv Real.smoothTransition (-((n : ℝ) + 1) * s) : ℝ)

private def lowerHalfCutoffSecond (n : ℕ) (s : ℝ) : ℂ :=
  (((n : ℝ) + 1) ^ 2 : ℂ) *
    (iteratedDeriv 2 Real.smoothTransition (-((n : ℝ) + 1) * s) : ℝ)

private lemma lowerHalfCutoff_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lowerHalfCutoff n) := by
  exact Complex.ofRealCLM.contDiff.comp
    ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
      (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => -((n : ℝ) + 1) * s)))

private lemma lowerHalfCutoff_deriv (n : ℕ) (s : ℝ) :
    deriv (lowerHalfCutoff n) s = lowerHalfCutoffDeriv n s := by
  have hinner : HasDerivAt (fun y : ℝ => -((n : ℝ) + 1) * y)
      (-((n : ℝ) + 1)) s := by exact hasDerivAt_const_mul (-((n : ℝ) + 1))
  have hout := ((@Real.smoothTransition.contDiff 1).differentiable
    (by simp) _).hasDerivAt.comp s hinner
  have houtC := hout.ofReal_comp
  change deriv (fun y : ℝ =>
    (Real.smoothTransition (-((n : ℝ) + 1) * y) : ℂ)) s = _
  have heq : deriv (fun y : ℝ =>
      (Real.smoothTransition (-((n : ℝ) + 1) * y) : ℂ)) s =
      ((deriv Real.smoothTransition (-((n : ℝ) + 1) * s) *
        (-((n : ℝ) + 1)) : ℝ) : ℂ) := by
    simpa only [Function.comp_apply] using houtC.deriv
  rw [heq]
  simp only [lowerHalfCutoffDeriv]
  push_cast
  ring

private lemma lowerHalfCutoff_second (n : ℕ) (s : ℝ) :
    iteratedDeriv 2 (lowerHalfCutoff n) s = lowerHalfCutoffSecond n s := by
  rw [show iteratedDeriv 2 (lowerHalfCutoff n) =
      deriv (deriv (lowerHalfCutoff n)) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  rw [show deriv (lowerHalfCutoff n) = lowerHalfCutoffDeriv n by
    funext x; exact lowerHalfCutoff_deriv n x]
  unfold lowerHalfCutoffDeriv lowerHalfCutoffSecond
  have hs1diff : Differentiable ℝ (iteratedDeriv 1 Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).differentiable_iteratedDeriv 1
      (by
        change ((1 : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 1))
  have hinner : HasDerivAt (fun y : ℝ => -((n : ℝ) + 1) * y)
      (-((n : ℝ) + 1)) s := by exact hasDerivAt_const_mul (-((n : ℝ) + 1))
  have houter := (hs1diff _).hasDerivAt.comp s hinner
  rw [show iteratedDeriv 2 Real.smoothTransition =
      deriv (iteratedDeriv 1 Real.smoothTransition) by
    simpa using (iteratedDeriv_succ (n := 1) (f := Real.smoothTransition))]
  have houterC := houter.ofReal_comp
  have houterC' : HasDerivAt
      (fun y : ℝ => ((deriv Real.smoothTransition
        (-((n : ℝ) + 1) * y) : ℝ) : ℂ))
      (((deriv (iteratedDeriv 1 Real.smoothTransition)
        (-((n : ℝ) + 1) * s) * (-((n : ℝ) + 1)) : ℝ) : ℂ)) s := by
    simpa only [Function.comp_apply, iteratedDeriv_one] using houterC
  have hconst : HasDerivAt (fun _ : ℝ => (-((n : ℝ) + 1) : ℂ)) 0 s :=
    hasDerivAt_const s _
  change deriv ((fun _ : ℝ => (-((n : ℝ) + 1) : ℂ)) *
    fun y : ℝ => ((deriv Real.smoothTransition
      (-((n : ℝ) + 1) * y) : ℝ) : ℂ)) s = _
  rw [(hconst.mul houterC').deriv]
  simp only [zero_mul, zero_add]
  push_cast
  ring

private lemma lowerHalfCutoff_eq_one {n : ℕ} {s : ℝ}
    (hs : s ≤ -(((n : ℝ) + 1)⁻¹)) : lowerHalfCutoff n s = 1 := by
  unfold lowerHalfCutoff
  norm_cast
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hs hn.le
  have hprod : ((n : ℝ) + 1) * -(((n : ℝ) + 1)⁻¹) = -1 := by
    field_simp
  rw [hprod] at this
  apply Real.smoothTransition.one_of_one_le
  have ht : 1 ≤ -((n : ℝ) + 1) * s := by linarith
  convert ht using 1 <;> norm_num

private lemma lowerHalfCutoff_eq_zero {n : ℕ} {s : ℝ}
    (hs : 0 ≤ s) : lowerHalfCutoff n s = 0 := by
  unfold lowerHalfCutoff
  norm_cast
  apply Real.smoothTransition.zero_of_nonpos
  have ht : -((n : ℝ) + 1) * s ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (show 0 ≤ (n : ℝ) + 1 by positivity)) hs
  convert ht using 1 <;> norm_num

private lemma lowerHalfCutoff_tendsto_indicator (s : ℝ) :
    Tendsto (fun n : ℕ => lowerHalfCutoff n s) atTop
      (nhds (if s < 0 then 1 else 0)) := by
  by_cases hs : s < 0
  · have hev : ∀ᶠ n : ℕ in atTop,
        s ≤ -(((n : ℝ) + 1)⁻¹) := by
      have hpos : 0 < -s := neg_pos.mpr hs
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((-s)⁻¹)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hNpos : 0 < (N : ℝ) + 1 := by positivity
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
      have hlarge : (-s)⁻¹ < (n : ℝ) + 1 := by
        calc
          (-s)⁻¹ < (N : ℝ) := hN
          _ < (N : ℝ) + 1 := by linarith
          _ ≤ (n : ℝ) + 1 := by linarith
      have hinv : ((n : ℝ) + 1)⁻¹ < -s :=
        (inv_lt_comm₀ hnpos hpos).2 hlarge
      linarith
    rw [if_pos hs]
    exact tendsto_const_nhds.congr'
      (hev.mono fun n hn => (lowerHalfCutoff_eq_one hn).symm)
  · rw [if_neg hs]
    have hs0 : 0 ≤ s := le_of_not_gt hs
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n =>
      (lowerHalfCutoff_eq_zero hs0).symm)

private def lowerHalfCutoffTest (n : ℕ)
    (Ψ : ℝ × (ℝ × ℝ) → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  lowerHalfCutoff n p.2.1 * Ψ p

private lemma lowerHalfCutoffTest_contDiff (n : ℕ)
    {Ψ : ℝ × (ℝ × ℝ) → ℂ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (lowerHalfCutoffTest n Ψ) := by
  unfold lowerHalfCutoffTest
  exact ((lowerHalfCutoff_contDiff n).comp (by fun_prop)).mul hΨ

private lemma lowerHalfCutoffTest_hasCompactSupport (n : ℕ)
    {Ψ : ℝ × (ℝ × ℝ) → ℂ} (hΨ : HasCompactSupport Ψ) :
    HasCompactSupport (lowerHalfCutoffTest n Ψ) := by
  change HasCompactSupport
    ((fun p : ℝ × (ℝ × ℝ) => lowerHalfCutoff n p.2.1) * Ψ)
  exact hΨ.mul_left

private lemma lowerHalfCutoffTest_tsupport_subset (n : ℕ)
    (Ψ : ℝ × (ℝ × ℝ) → ℂ) :
    tsupport (lowerHalfCutoffTest n Ψ) ⊆ tsupport Ψ := by
  change tsupport
    ((fun p : ℝ × (ℝ × ℝ) => lowerHalfCutoff n p.2.1) * Ψ) ⊆ _
  exact tsupport_mul_subset_right

private lemma lowerHalfCutoffTest_adjoint (n : ℕ)
    (Ψ : ℝ × (ℝ × ℝ) → ℂ)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (p : ℝ × (ℝ × ℝ)) :
    -Complex.I * deriv (fun t => lowerHalfCutoffTest n Ψ (t, p.2)) p.1 +
        iteratedDeriv 2
          (fun s => lowerHalfCutoffTest n Ψ (p.1, (s, p.2.2))) p.2.1 +
        iteratedDeriv 2
          (fun r => lowerHalfCutoffTest n Ψ (p.1, (p.2.1, r))) p.2.2 =
      lowerHalfCutoff n p.2.1 *
        (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
          iteratedDeriv 2 (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
          iteratedDeriv 2 (fun r => Ψ (p.1, (p.2.1, r))) p.2.2) +
      2 * lowerHalfCutoffDeriv n p.2.1 *
        deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
      lowerHalfCutoffSecond n p.2.1 * Ψ p := by
  have h2top : ((2 : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have ht : ContDiffAt ℝ 2 (fun t : ℝ => Ψ (t, p.2)) p.1 :=
    (hΨ.comp (by fun_prop)).contDiffAt.of_le h2top
  have hs : ContDiffAt ℝ 2 (fun s : ℝ => Ψ (p.1, (s, p.2.2))) p.2.1 :=
    (hΨ.comp (by fun_prop)).contDiffAt.of_le h2top
  have hr : ContDiffAt ℝ 2 (fun r : ℝ => Ψ (p.1, (p.2.1, r))) p.2.2 :=
    (hΨ.comp (by fun_prop)).contDiffAt.of_le h2top
  have hcut : ContDiffAt ℝ 2 (lowerHalfCutoff n) p.2.1 :=
    (lowerHalfCutoff_contDiff n).contDiffAt.of_le h2top
  simp only [lowerHalfCutoffTest]
  rw [deriv_const_mul_field,
    show (fun s => lowerHalfCutoff n s * Ψ (p.1, (s, p.2.2))) =
        lowerHalfCutoff n * (fun s => Ψ (p.1, (s, p.2.2))) by rfl,
    iteratedDeriv_mul hcut hs,
    iteratedDeriv_const_mul_field]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.choose_one_right,
    Nat.cast_ofNat, iteratedDeriv_one, Nat.choose_self, Nat.sub_self]
  rw [lowerHalfCutoff_deriv, lowerHalfCutoff_second]
  rw [show iteratedDeriv 1 (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 =
      deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 by
    exact congrFun iteratedDeriv_one p.2.1]
  ring

private def normalBoundaryRestriction
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun z : ℝ × ℝ => (z.1, (0, z.2))) (by
    let L : (ℝ × ℝ) →L[ℝ] ℝ × (ℝ × ℝ) :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
          (ContinuousLinearMap.snd ℝ ℝ ℝ))
    have hL := L.hasTemperateGrowth
    convert hL using 1 <;> ext z <;> simp [L]) (by
    refine ⟨1, 1, fun z => ?_⟩
    simp only [pow_one, one_mul, Prod.norm_def]
    rw [norm_zero, max_eq_right (norm_nonneg _)]
    exact le_add_of_nonneg_left (by norm_num)) Φ

@[simp] private lemma normalBoundaryRestriction_apply
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (z : ℝ × ℝ) :
    normalBoundaryRestriction Φ z = Φ (z.1, (0, z.2)) := rfl

private def spacetimeNormalPartial
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) : 𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  ∂_{((0, (1, 0)) : ℝ × (ℝ × ℝ))} Φ

private lemma normalBoundaryRestriction_hasCompactSupport
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport
      (normalBoundaryRestriction Φ : ℝ × ℝ → ℂ) := by
  let π : (ℝ × (ℝ × ℝ)) → ℝ × ℝ := fun p => (p.1, p.2.2)
  have hK : IsCompact (π '' tsupport (Φ : ℝ × (ℝ × ℝ) → ℂ)) :=
    hΦ.isCompact.image (by fun_prop)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  refine ⟨(z.1, (0, z.2)), ?_, rfl⟩
  exact subset_tsupport _ hz

private lemma spacetimeNormalPartial_hasCompactSupport
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport
      (spacetimeNormalPartial Φ : ℝ × (ℝ × ℝ) → ℂ) := by
  exact hΦ.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (SchwartzMap.tsupport_lineDerivOp_subset _ Φ)

private lemma normalBoundaryNormalPartial_hasCompactSupport
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport
      (normalBoundaryRestriction (spacetimeNormalPartial Φ) : ℝ × ℝ → ℂ) :=
  normalBoundaryRestriction_hasCompactSupport _
    (spacetimeNormalPartial_hasCompactSupport Φ hΦ)

private lemma spacetimeNormalPartial_apply
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) :
    spacetimeNormalPartial Φ p =
      deriv (fun s : ℝ => Φ (p.1, (s, p.2.2))) p.2.1 := by
  have hg : HasDerivAt (fun s : ℝ => (p.1, (s, p.2.2)))
      ((0, (1, 0)) : ℝ × (ℝ × ℝ)) p.2.1 := by
    exact (hasDerivAt_const _ _).prodMk
      ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  have hc := (Φ.hasFDerivAt p).comp_hasDerivAt p.2.1 hg
  rw [show spacetimeNormalPartial Φ p =
      fderiv ℝ (Φ : ℝ × (ℝ × ℝ) → ℂ) p
        ((0, (1, 0)) : ℝ × (ℝ × ℝ)) by
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _]
  exact hc.deriv.symm

private lemma smoothTransition_deriv_hasCompactSupport' :
    HasCompactSupport (deriv Real.smoothTransition) := by
  refine HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  by_cases hleft : x < 0
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
      filter_upwards [isOpen_Iio.mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq, deriv_const]
  · have hright : 1 < x := by
      by_contra hn
      exact hx ⟨le_of_not_gt hleft, le_of_not_gt hn⟩
    have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq, deriv_const]

private lemma smoothTransition_second_hasCompactSupport' :
    HasCompactSupport (iteratedDeriv 2 Real.smoothTransition) := by
  rw [show iteratedDeriv 2 Real.smoothTransition =
      deriv (deriv Real.smoothTransition) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  exact smoothTransition_deriv_hasCompactSupport'.deriv

private lemma exists_smoothTransition_deriv_bounds' :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x, ‖deriv Real.smoothTransition x‖ ≤ M) ∧
      ∀ x, ‖iteratedDeriv 2 Real.smoothTransition x‖ ≤ M := by
  have h1c : Continuous (deriv Real.smoothTransition) := by
    simpa only [iteratedDeriv_one] using
      ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).continuous_iteratedDeriv 1
        (by norm_num))
  have h2c : Continuous (iteratedDeriv 2 Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).continuous_iteratedDeriv 2
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨x1, hx1⟩ := h1c.norm.exists_forall_ge_of_hasCompactSupport
    smoothTransition_deriv_hasCompactSupport'.norm
  obtain ⟨x2, hx2⟩ := h2c.norm.exists_forall_ge_of_hasCompactSupport
    smoothTransition_second_hasCompactSupport'.norm
  refine ⟨max ‖deriv Real.smoothTransition x1‖
      ‖iteratedDeriv 2 Real.smoothTransition x2‖,
    (norm_nonneg _).trans (le_max_left _ _), ?_, ?_⟩
  · intro x
    exact (hx1 x).trans (le_max_left _ _)
  · intro x
    exact (hx2 x).trans (le_max_right _ _)

private lemma smoothTransition_deriv_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [heq.deriv_eq, deriv_const]

private lemma smoothTransition_deriv_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 1 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [heq.deriv_eq, deriv_const]

private lemma smoothTransition_second_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    iteratedDeriv 2 Real.smoothTransition x = 0 := by
  rw [show iteratedDeriv 2 Real.smoothTransition =
      deriv (deriv Real.smoothTransition) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  have heq : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact smoothTransition_deriv_eq_zero_of_neg hy
  rw [heq.deriv_eq, deriv_const]

private lemma smoothTransition_second_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    iteratedDeriv 2 Real.smoothTransition x = 0 := by
  rw [show iteratedDeriv 2 Real.smoothTransition =
      deriv (deriv Real.smoothTransition) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  have heq : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact smoothTransition_deriv_eq_zero_of_one_lt hy
  rw [heq.deriv_eq, deriv_const]

private lemma lowerHalfCutoffDeriv_eq_zero_of_pos (n : ℕ) {s : ℝ}
    (hs : 0 < s) : lowerHalfCutoffDeriv n s = 0 := by
  unfold lowerHalfCutoffDeriv
  rw [smoothTransition_deriv_eq_zero_of_neg]
  · simp
  · have hn : 0 < (n : ℝ) + 1 := by positivity
    nlinarith

private lemma lowerHalfCutoffSecond_eq_zero_of_pos (n : ℕ) {s : ℝ}
    (hs : 0 < s) : lowerHalfCutoffSecond n s = 0 := by
  unfold lowerHalfCutoffSecond
  rw [smoothTransition_second_eq_zero_of_neg]
  · simp
  · have hn : 0 < (n : ℝ) + 1 := by positivity
    nlinarith

private lemma lowerHalfCutoffDeriv_eventually_zero_of_neg {s : ℝ} (hs : s < 0) :
    ∀ᶠ n : ℕ in atTop, lowerHalfCutoffDeriv n s = 0 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((-s)⁻¹)
  filter_upwards [eventually_ge_atTop N] with n hn
  unfold lowerHalfCutoffDeriv
  rw [smoothTransition_deriv_eq_zero_of_one_lt]
  · simp
  · have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hspos : 0 < -s := neg_pos.mpr hs
    have hlarge : (-s)⁻¹ < (n : ℝ) + 1 := by
      calc
        (-s)⁻¹ < (N : ℝ) := hN
        _ ≤ (n : ℝ) := hnR
        _ < (n : ℝ) + 1 := by linarith
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hinv := (inv_lt_comm₀ hnpos hspos).2 hlarge
    have hprod := mul_lt_mul_of_pos_left hinv hnpos
    rw [mul_inv_cancel₀ hnpos.ne'] at hprod
    nlinarith

private lemma lowerHalfCutoffSecond_eventually_zero_of_neg {s : ℝ} (hs : s < 0) :
    ∀ᶠ n : ℕ in atTop, lowerHalfCutoffSecond n s = 0 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((-s)⁻¹)
  filter_upwards [eventually_ge_atTop N] with n hn
  unfold lowerHalfCutoffSecond
  rw [smoothTransition_second_eq_zero_of_one_lt]
  · simp
  · have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hspos : 0 < -s := neg_pos.mpr hs
    have hlarge : (-s)⁻¹ < (n : ℝ) + 1 := by
      calc
        (-s)⁻¹ < (N : ℝ) := hN
        _ ≤ (n : ℝ) := hnR
        _ < (n : ℝ) + 1 := by linarith
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hinv := (inv_lt_comm₀ hnpos hspos).2 hlarge
    have hprod := mul_lt_mul_of_pos_left hinv hnpos
    rw [mul_inv_cancel₀ hnpos.ne'] at hprod
    nlinarith

private lemma measurableNormalScalarizationOn_stronglyMeasurable
    {σ : ℝ} (u v : GlobalSolution σ) (ψ : ℝ × ℝ → ℂ)
    (hψ : Measurable ψ) (A B : ℝ) :
    StronglyMeasurable (measurableNormalScalarizationOn u v ψ A B) := by
  let G : (ℝ × ℝ) × ℝ → ℂ := fun q =>
    measurableNormalExterior u v (q.1.2, (q.1.1, q.2)) * ψ (q.1.2, q.2)
  have hG : Measurable G := by
    dsimp [G]
    exact ((measurableNormalExterior_measurable u v).comp (by fun_prop)).mul
      (hψ.comp (by fun_prop))
  have hinner : StronglyMeasurable
      (fun q : ℝ × ℝ => ∫ r : ℝ,
        measurableNormalExterior u v (q.2, (q.1, r)) * ψ (q.2, r)) := by
    simpa [G] using hG.stronglyMeasurable.integral_prod_right'
  change StronglyMeasurable (fun s => ∫ t, (∫ r : ℝ,
    measurableNormalExterior u v (t, (s, r)) * ψ (t, r)) ∂timeMeasure A B)
  exact hinner.integral_prod_right'

@[simp] private lemma measurableNormalScalarizationOn_zero
    {σ : ℝ} (u v : GlobalSolution σ) (ψ : ℝ × ℝ → ℂ) (A B : ℝ) :
    measurableNormalScalarizationOn u v ψ A B 0 = 0 := by
  unfold measurableNormalScalarizationOn
  calc
    (∫ t, (∫ r : ℝ,
      measurableNormalExterior u v (t, (0, r)) * ψ (t, r))
      ∂timeMeasure A B) = ∫ _t : ℝ, (0 : ℂ) ∂timeMeasure A B := by
        apply integral_congr_ae
        filter_upwards with t
        calc
          (∫ r : ℝ, measurableNormalExterior u v (t, (0, r)) * ψ (t, r)) =
              ∫ _r : ℝ, (0 : ℂ) := by
            apply integral_congr_ae
            filter_upwards with r
            simp only [measurableNormalExterior, measurableExterior,
              fromNormalCoordinates]
            ring
          _ = 0 := by simp
    _ = 0 := by simp

private lemma scaled_to_zero (x : ℝ) :
    Tendsto (fun n : ℕ => -x / ((n : ℝ) + 1)) atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-x : ℝ)) atTop (nhds (-x))).mul
      hn.inv_tendsto_atTop

private lemma scaled_to_zero_within (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => -x / ((n : ℝ) + 1)) atTop
      (nhdsWithin 0 {0}ᶜ) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨scaled_to_zero x, ?_⟩
  filter_upwards with n
  simp [hx, show (n : ℝ) + 1 ≠ 0 by positivity]

private lemma scaled_quotient_tendsto_zero
    (h : ℝ → ℂ)
    (hq : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ * h s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) (x : ℝ) :
    Tendsto (fun n : ℕ =>
      ((-x / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
        h (-x / ((n : ℝ) + 1))) atTop (nhds 0) := by
  by_cases hx : x = 0
  · subst x
    simp
  · exact hq.comp (scaled_to_zero_within x hx)

private theorem lowerHalfCutoffSecond_scalar_tendsto_zero
    (h : ℝ → ℂ) (hsm : StronglyMeasurable h) (h0 : h 0 = 0)
    (hq : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ * h s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    Tendsto (fun n : ℕ => ∫ s : ℝ, lowerHalfCutoffSecond n s * h s)
      atTop (nhds 0) := by
  let q : ℝ → ℂ := fun s => (s : ℂ)⁻¹ * h s
  let D : ℕ → ℝ → ℂ := fun n x =>
    ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) *
      (lowerHalfCutoffSecond n
        (-x / ((n : ℝ) + 1)) * h (-x / ((n : ℝ) + 1)))
  have hDmeas (n : ℕ) : AEStronglyMeasurable (D n) volume := by
    have hcut2 : Continuous (lowerHalfCutoffSecond n) := by
      have hc := (lowerHalfCutoff_contDiff n).continuous_iteratedDeriv 2
          (by
            change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
            exact WithTop.coe_le_coe.mpr le_top)
      convert hc using 1
      funext x
      exact (lowerHalfCutoff_second n x).symm
    apply Measurable.aestronglyMeasurable
    dsimp [D]
    exact measurable_const.mul ((hcut2.measurable.comp
      (by fun_prop : Measurable fun x : ℝ => -x / ((n : ℝ) + 1))).mul
        (hsm.measurable.comp
          (by fun_prop : Measurable fun x : ℝ => -x / ((n : ℝ) + 1))))
  have hpoint (x : ℝ) : Tendsto (fun n => D n x) atTop (nhds 0) := by
    have hqs := scaled_quotient_tendsto_zero h hq x
    have hfac : Tendsto (fun _ : ℕ =>
        (-(x : ℂ)) *
          (iteratedDeriv 2 Real.smoothTransition x : ℝ)) atTop
        (nhds ((-(x : ℂ)) *
          (iteratedDeriv 2 Real.smoothTransition x : ℝ))) := tendsto_const_nhds
    have hmul := hfac.mul hqs
    simpa only [mul_zero] using hmul.congr' (Filter.Eventually.of_forall fun n => by
      dsimp [D, q, lowerHalfCutoffSecond]
      by_cases hx : x = 0
      · subst x
        simp [h0]
      · have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
        push_cast
        field_simp [hxC] <;> ring)
  have hevq : ∀ᶠ s : ℝ in nhdsWithin 0 {0}ᶜ, ‖q s‖ < 1 := by
    have := hq.eventually (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    simpa [q, Metric.mem_ball] using this
  have hevq' : ∀ᶠ s : ℝ in nhds 0,
      s ∈ (({0} : Set ℝ)ᶜ) → ‖q s‖ < 1 := by
    rw [eventually_nhdsWithin_iff] at hevq
    exact hevq
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.mp hevq'
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt δ⁻¹
  have hdomEventually : ∀ᶠ n : ℕ in atTop,
      ∀ᵐ x : ℝ ∂volume,
        ‖D n x‖ ≤ ‖x‖ * ‖iteratedDeriv 2 Real.smoothTransition x‖ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    filter_upwards with x
    by_cases hxsupp : x ∈ Set.Icc (0 : ℝ) 1
    · rcases hxsupp with ⟨hx0, hx1⟩
      by_cases hxz : x = 0
      · subst x
        simp [D, h0]
      · have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hnpos : 0 < (n : ℝ) + 1 := by positivity
        have hδinv : ((n : ℝ) + 1)⁻¹ < δ := by
          have hlarge : δ⁻¹ < (n : ℝ) + 1 := by
            calc
              δ⁻¹ < (N : ℝ) := hN
              _ ≤ (n : ℝ) := hnR
              _ < (n : ℝ) + 1 := by linarith
          exact (inv_lt_comm₀ hnpos hδ).2 hlarge
        have hsne : -x / ((n : ℝ) + 1) ∈ ({0}ᶜ : Set ℝ) := by
          simp [hxz, hnpos.ne']
        have hsdist : dist (-x / ((n : ℝ) + 1)) 0 < δ := by
          rw [Real.dist_eq, sub_zero, abs_div, abs_neg,
            abs_of_nonneg hx0, abs_of_pos hnpos]
          calc
            x / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by gcongr
            _ = ((n : ℝ) + 1)⁻¹ := by rw [one_div]
            _ < δ := hδinv
        have hqbd := hδq hsdist hsne
        have hid : D n x =
            (-(x : ℂ)) * (iteratedDeriv 2 Real.smoothTransition x : ℝ) *
              q (-x / ((n : ℝ) + 1)) := by
          dsimp [D, q, lowerHalfCutoffSecond]
          push_cast
          field_simp [hnpos.ne', hxz] <;> ring
        rw [hid, norm_mul, norm_mul]
        simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hx0]
        have hqle : ‖q (-x / ((n : ℝ) + 1))‖ ≤ 1 := hqbd.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hqle
          (mul_nonneg hx0 (abs_nonneg _))
    · have hxout : x < 0 ∨ 1 < x := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hxsupp
      rcases hxout with hx | hx
      · have hDzero : D n x = 0 := by
          dsimp [D, lowerHalfCutoffSecond]
          rw [show -((n : ℝ) + 1) * (-x / ((n : ℝ) + 1)) = x by
            field_simp]
          rw [smoothTransition_second_eq_zero_of_neg hx]
          simp
        rw [hDzero, norm_zero, smoothTransition_second_eq_zero_of_neg hx,
          norm_zero, mul_zero]
      · have hDzero : D n x = 0 := by
          dsimp [D, lowerHalfCutoffSecond]
          rw [show -((n : ℝ) + 1) * (-x / ((n : ℝ) + 1)) = x by
            field_simp]
          rw [smoothTransition_second_eq_zero_of_one_lt hx]
          simp
        rw [hDzero, norm_zero, smoothTransition_second_eq_zero_of_one_lt hx,
          norm_zero, mul_zero]
  have hdomInt : Integrable
      (fun x : ℝ => ‖x‖ * ‖iteratedDeriv 2 Real.smoothTransition x‖) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact smoothTransition_second_hasCompactSupport'.norm.mul_left
  have hlim : Tendsto (fun n => ∫ x : ℝ, D n x) atTop (nhds 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (μ := volume) (F := D) (f := fun _ => 0)
      (fun x => ‖x‖ * ‖iteratedDeriv 2 Real.smoothTransition x‖)
      (Filter.Eventually.of_forall hDmeas) hdomEventually hdomInt
      (Filter.Eventually.of_forall hpoint)
  apply hlim.congr'
  filter_upwards with n
  let g : ℝ → ℂ := fun s => lowerHalfCutoffSecond n s * h s
  have hscl := Measure.integral_comp_mul_left g
    (-(((n : ℝ) + 1)⁻¹))
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hfac : |(-(((n : ℝ) + 1)⁻¹))⁻¹| = (n : ℝ) + 1 := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hnpos]
  change (∫ x : ℝ, D n x) = ∫ s : ℝ, g s
  calc
    (∫ x : ℝ, D n x) = (((n : ℝ) + 1)⁻¹ : ℂ) *
        ∫ x : ℝ, g (-(((n : ℝ) + 1)⁻¹) * x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      have harg : -x / ((n : ℝ) + 1) =
          -(((n : ℝ) + 1)⁻¹) * x := by
        field_simp
      simp only [D, g]
      rw [harg]
      rw [Complex.ofReal_inv]
      have hcast : ((((n : ℝ) + 1) : ℝ) : ℂ) = (n : ℂ) + 1 := by
        norm_cast
      rw [hcast]
      norm_cast
      rw [Complex.ofReal_inv]
      norm_cast
      have hnr : (((n + 1 : ℕ) : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by
        norm_cast
      rw [Complex.ofReal_inv, hnr]
    _ = (((n : ℝ) + 1)⁻¹ : ℂ) *
        (((n : ℝ) + 1) : ℝ) • ∫ s : ℝ, g s := by rw [hscl, hfac]
    _ = ∫ s : ℝ, g s := by
      rw [RCLike.real_smul_eq_coe_mul]
      norm_cast
      have hnr : (((n + 1 : ℕ) : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by
        norm_cast
      rw [Complex.ofReal_inv, hnr]
      field_simp

private theorem lowerHalfCutoffDeriv_scalar_tendsto_zero
    (h : ℝ → ℂ) (hsm : StronglyMeasurable h) (h0 : h 0 = 0)
    (hq : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ * h s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    Tendsto (fun n : ℕ => ∫ s : ℝ, lowerHalfCutoffDeriv n s * h s)
      atTop (nhds 0) := by
  let q : ℝ → ℂ := fun s => (s : ℂ)⁻¹ * h s
  let D : ℕ → ℝ → ℂ := fun n x =>
    ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) *
      (lowerHalfCutoffDeriv n
        (-x / ((n : ℝ) + 1)) * h (-x / ((n : ℝ) + 1)))
  have hDmeas (n : ℕ) : AEStronglyMeasurable (D n) volume := by
    have hcut1 : Continuous (lowerHalfCutoffDeriv n) := by
      have hc : Continuous (deriv (lowerHalfCutoff n)) := by
        simpa only [iteratedDeriv_one] using
          (lowerHalfCutoff_contDiff n).continuous_iteratedDeriv 1
            (by norm_num)
      convert hc using 1
      funext x
      exact (lowerHalfCutoff_deriv n x).symm
    apply Measurable.aestronglyMeasurable
    dsimp [D]
    exact measurable_const.mul ((hcut1.measurable.comp
      (by fun_prop : Measurable fun x : ℝ => -x / ((n : ℝ) + 1))).mul
        (hsm.measurable.comp
          (by fun_prop : Measurable fun x : ℝ => -x / ((n : ℝ) + 1))))
  have hscaled (x : ℝ) : Tendsto (fun n : ℕ =>
      h (-x / ((n : ℝ) + 1))) atTop (nhds 0) := by
    have hqs := scaled_quotient_tendsto_zero h hq x
    have hs := (scaled_to_zero x).ofReal
    have hmul := hs.mul hqs
    have hmul0 : Tendsto (fun n : ℕ =>
        ((-x / ((n : ℝ) + 1) : ℝ) : ℂ) *
          (((-x / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
            h (-x / ((n : ℝ) + 1)))) atTop (nhds 0) := by
      simpa using hmul
    apply hmul0.congr'
    filter_upwards with n
    by_cases hx : x = 0
    · subst x
      simp [h0]
    · have hsne : (-x / ((n : ℝ) + 1) : ℝ) ≠ 0 := by
        simp [hx, show (n : ℝ) + 1 ≠ 0 by positivity]
      have hsneC : ((-x / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hsne
      exact mul_inv_cancel_left₀ hsneC (h (-x / ((n : ℝ) + 1)))
  have hpoint (x : ℝ) : Tendsto (fun n => D n x) atTop (nhds 0) := by
    have hfac : Tendsto (fun _ : ℕ =>
        -((deriv Real.smoothTransition x : ℝ) : ℂ)) atTop
        (nhds (-((deriv Real.smoothTransition x : ℝ) : ℂ))) :=
      tendsto_const_nhds
    have hmul := hfac.mul (hscaled x)
    simpa only [mul_zero] using hmul.congr' (Filter.Eventually.of_forall fun n => by
      dsimp [D, lowerHalfCutoffDeriv]
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp <;> ring)
  have hevq : ∀ᶠ s : ℝ in nhdsWithin 0 {0}ᶜ, ‖q s‖ < 1 := by
    have := hq.eventually (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    simpa [q, Metric.mem_ball] using this
  have hevq' : ∀ᶠ s : ℝ in nhds 0,
      s ∈ (({0} : Set ℝ)ᶜ) → ‖q s‖ < 1 := by
    rw [eventually_nhdsWithin_iff] at hevq
    exact hevq
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.mp hevq'
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt δ⁻¹
  have hdomEventually : ∀ᶠ n : ℕ in atTop,
      ∀ᵐ x : ℝ ∂volume, ‖D n x‖ ≤ ‖deriv Real.smoothTransition x‖ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    filter_upwards with x
    by_cases hxsupp : x ∈ Set.Icc (0 : ℝ) 1
    · rcases hxsupp with ⟨hx0, hx1⟩
      by_cases hxz : x = 0
      · subst x
        simp [D, h0]
      · have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hnpos : 0 < (n : ℝ) + 1 := by positivity
        have hδinv : ((n : ℝ) + 1)⁻¹ < δ := by
          have hlarge : δ⁻¹ < (n : ℝ) + 1 := by
            calc
              δ⁻¹ < (N : ℝ) := hN
              _ ≤ (n : ℝ) := hnR
              _ < (n : ℝ) + 1 := by linarith
          exact (inv_lt_comm₀ hnpos hδ).2 hlarge
        have hsne : -x / ((n : ℝ) + 1) ∈ ({0}ᶜ : Set ℝ) := by
          simp [hxz, hnpos.ne']
        have hsdist : dist (-x / ((n : ℝ) + 1)) 0 < δ := by
          rw [Real.dist_eq, sub_zero, abs_div, abs_neg,
            abs_of_nonneg hx0, abs_of_pos hnpos]
          calc
            x / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by gcongr
            _ = ((n : ℝ) + 1)⁻¹ := by rw [one_div]
            _ < δ := hδinv
        have hqbd := hδq hsdist hsne
        have hid : D n x =
            -((deriv Real.smoothTransition x : ℝ) : ℂ) *
              h (-x / ((n : ℝ) + 1)) := by
          dsimp [D, lowerHalfCutoffDeriv]
          push_cast
          field_simp <;> ring
        have hh : h (-x / ((n : ℝ) + 1)) =
            ((-x / ((n : ℝ) + 1) : ℝ) : ℂ) *
              q (-x / ((n : ℝ) + 1)) := by
          dsimp [q]
          have hsne' : ((-x / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
            exact Complex.ofReal_ne_zero.mpr (by
              simp [hxz, hnpos.ne'])
          exact (mul_inv_cancel_left₀ hsne'
            (h (-x / ((n : ℝ) + 1)))).symm
        rw [hid, hh, norm_mul, norm_mul]
        have hsabs : ‖((-x / ((n : ℝ) + 1) : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hx0,
            abs_of_pos hnpos]
          exact (div_le_one hnpos).2 (hx1.trans (by
            have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
            have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
            exact this))
        have hprod : ‖((-x / ((n : ℝ) + 1) : ℝ) : ℂ)‖ *
            ‖q (-x / ((n : ℝ) + 1))‖ ≤ 1 := by
          calc
            _ ≤ 1 * 1 := mul_le_mul hsabs hqbd.le (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        have hprod' : |-x / ((n : ℝ) + 1)| *
            ‖q (-x / ((n : ℝ) + 1))‖ ≤ 1 := by
          simpa only [Complex.norm_real, Real.norm_eq_abs] using hprod
        simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hprod'
            (abs_nonneg (deriv Real.smoothTransition x))
    · have hxout : x < 0 ∨ 1 < x := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hxsupp
      rcases hxout with hx | hx
      · have hDzero : D n x = 0 := by
          dsimp [D, lowerHalfCutoffDeriv]
          rw [show -((n : ℝ) + 1) * (-x / ((n : ℝ) + 1)) = x by
            field_simp]
          rw [smoothTransition_deriv_eq_zero_of_neg hx]
          simp
        rw [hDzero, norm_zero, smoothTransition_deriv_eq_zero_of_neg hx,
          norm_zero]
      · have hDzero : D n x = 0 := by
          dsimp [D, lowerHalfCutoffDeriv]
          rw [show -((n : ℝ) + 1) * (-x / ((n : ℝ) + 1)) = x by
            field_simp]
          rw [smoothTransition_deriv_eq_zero_of_one_lt hx]
          simp
        rw [hDzero, norm_zero, smoothTransition_deriv_eq_zero_of_one_lt hx,
          norm_zero]
  have hdomInt : Integrable (fun x : ℝ => ‖deriv Real.smoothTransition x‖) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have hc : Continuous (deriv Real.smoothTransition) := by
        simpa only [iteratedDeriv_one] using
          ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).continuous_iteratedDeriv 1
            (by norm_num))
      exact hc.norm
    · exact smoothTransition_deriv_hasCompactSupport'.norm
  have hlim : Tendsto (fun n => ∫ x : ℝ, D n x) atTop (nhds 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (μ := volume) (F := D) (f := fun _ => 0)
      (fun x => ‖deriv Real.smoothTransition x‖)
      (Filter.Eventually.of_forall hDmeas) hdomEventually hdomInt
      (Filter.Eventually.of_forall hpoint)
  apply hlim.congr'
  filter_upwards with n
  let g : ℝ → ℂ := fun s => lowerHalfCutoffDeriv n s * h s
  have hscl := Measure.integral_comp_mul_left g
    (-(((n : ℝ) + 1)⁻¹))
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hfac : |(-(((n : ℝ) + 1)⁻¹))⁻¹| = (n : ℝ) + 1 := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hnpos]
  change (∫ x : ℝ, D n x) = ∫ s : ℝ, g s
  calc
    (∫ x : ℝ, D n x) = (((n : ℝ) + 1)⁻¹ : ℂ) *
        ∫ x : ℝ, g (-(((n : ℝ) + 1)⁻¹) * x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      have harg : -x / ((n : ℝ) + 1) =
          -(((n : ℝ) + 1)⁻¹) * x := by field_simp
      simp only [D, g]
      rw [harg, Complex.ofReal_inv]
      norm_cast
    _ = (((n : ℝ) + 1)⁻¹ : ℂ) *
        (((n : ℝ) + 1) : ℝ) • ∫ s : ℝ, g s := by rw [hscl, hfac]
    _ = ∫ s : ℝ, g s := by
      rw [RCLike.real_smul_eq_coe_mul]
      norm_cast
      have hnr : (((n + 1 : ℕ) : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by
        norm_cast
      rw [Complex.ofReal_inv, hnr]
      field_simp

private lemma spacetimeNormalPartial_difference_bound
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (t s r : ℝ) :
    ‖spacetimeNormalPartial Φ (t, (s, r)) -
        spacetimeNormalPartial Φ (t, (0, r))‖ ≤
      SchwartzMap.seminorm ℂ 0 0
        (spacetimeNormalPartial (spacetimeNormalPartial Φ)) * |s| := by
  let Θ := spacetimeNormalPartial (spacetimeNormalPartial Φ)
  let q : ℝ → ℂ := fun x => spacetimeNormalPartial Φ (t, (x, r))
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ q x := by
    intro x hx
    exact (spacetimeNormalPartial Φ).differentiableAt.comp x
      ((differentiableAt_const t).prodMk
        (differentiableAt_id.prodMk (differentiableAt_const r)))
  have hderiv (x : ℝ) : deriv q x = Θ (t, (x, r)) := by
    exact (spacetimeNormalPartial_apply (spacetimeNormalPartial Φ)
      (t, (x, r))).symm
  have hbound (x : ℝ) : ‖deriv q x‖ ≤
      SchwartzMap.seminorm ℂ 0 0 Θ := by
    rw [hderiv]
    simpa using
      (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ Θ 0 (t, (x, r)))
  simpa [q, Θ, Real.norm_eq_abs] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff
      (fun x _ => hbound x) (Set.mem_univ _) (Set.mem_univ _) :
        ‖q s - q 0‖ ≤
          SchwartzMap.seminorm ℂ 0 0 Θ * ‖s - 0‖)

private lemma spacetimeNormal_second_remainder_bound
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (t s r : ℝ) (hs : s ≤ 0) :
    ‖Φ (t, (s, r)) - Φ (t, (0, r)) -
        (s : ℂ) * spacetimeNormalPartial Φ (t, (0, r))‖ ≤
      SchwartzMap.seminorm ℂ 0 0
          (spacetimeNormalPartial (spacetimeNormalPartial Φ)) * |s| ^ 2 := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0
    (spacetimeNormalPartial (spacetimeNormalPartial Φ))
  let d0 : ℂ := spacetimeNormalPartial Φ (t, (0, r))
  let g : ℝ → ℂ := fun x => Φ (t, (x, r)) - (x : ℂ) * d0
  have hgderiv (x : ℝ) : HasDerivAt g
      (spacetimeNormalPartial Φ (t, (x, r)) - d0) x := by
    have hΦx : HasDerivAt (fun y : ℝ => Φ (t, (y, r)))
        (spacetimeNormalPartial Φ (t, (x, r))) x := by
      have hd := (Φ.differentiableAt.comp x
        ((differentiableAt_const t).prodMk
          (differentiableAt_id.prodMk (differentiableAt_const r)))).hasDerivAt
      rw [spacetimeNormalPartial_apply Φ (t, (x, r))]
      exact hd
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * d0) d0 x := by
      simpa only [id_eq, Complex.ofReal_one, one_mul] using
        ((hasDerivAt_id x).ofReal_comp.mul_const d0)
    exact hΦx.sub hlin
  have hsegDeriv : ∀ x ∈ Set.Icc s 0,
      HasDerivWithinAt g
        (spacetimeNormalPartial Φ (t, (x, r)) - d0) (Set.Icc s 0) x := by
    intro x hx
    exact (hgderiv x).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico s 0,
      ‖spacetimeNormalPartial Φ (t, (x, r)) - d0‖ ≤ C * |s| := by
    intro x hx
    have hxabs : |x| ≤ |s| := by
      rw [abs_of_nonpos hx.2.le, abs_of_nonpos hs]
      linarith [hx.1]
    have hC0 : 0 ≤ C := by
      have hle := SchwartzMap.le_seminorm ℂ 0 0
        (spacetimeNormalPartial (spacetimeNormalPartial Φ)) (0, (0, 0))
      exact (norm_nonneg
        (spacetimeNormalPartial (spacetimeNormalPartial Φ) (0, (0, 0)))).trans
          (by simpa [C] using hle)
    exact (spacetimeNormalPartial_difference_bound Φ t x r).trans
      (mul_le_mul_of_nonneg_left hxabs hC0)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    hsegDeriv hbound 0 (by exact ⟨hs, le_rfl⟩)
  have hnorm : ‖g s - g 0‖ ≤ C * |s| ^ 2 := by
    have hrev : ‖g s - g 0‖ = ‖g 0 - g s‖ := norm_sub_rev _ _
    rw [hrev]
    calc
      ‖g 0 - g s‖ ≤ (C * |s|) * (0 - s) := hmv
      _ = C * |s| ^ 2 := by rw [abs_of_nonpos hs]; ring
  change ‖Φ (t, (s, r)) - Φ (t, (0, r)) -
      (s : ℂ) * spacetimeNormalPartial Φ (t, (0, r))‖ ≤ C * |s| ^ 2
  calc
    _ = ‖g s - g 0‖ := by
      congr 1
      simp only [g, d0, Complex.ofReal_zero, zero_mul]
      ring
    _ ≤ C * |s| ^ 2 := hnorm

private lemma measurableNormalExterior_mul_continuous_compact_integrable
    (σ : ℝ) (u v : GlobalSolution σ)
    (c : ℝ × (ℝ × ℝ) → ℂ) (hc : Continuous c)
    (hcc : HasCompactSupport c) :
    Integrable (fun p => measurableNormalExterior u v p * c p)
      (volume.prod (volume.prod volume)) := by
  obtain ⟨T, hTpos, hT⟩ :=
    hcc.isCompact.isBounded.subset_closedBall_lt 0
      (0 : ℝ × (ℝ × ℝ))
  let S : Set (ℝ × (ℝ × ℝ)) := Set.Icc (-T) T ×ˢ Set.univ
  let μ : Measure (ℝ × (ℝ × ℝ)) := volume.prod (volume.prod volume)
  let μT : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)
  have hF : MemLp (measurableNormalExterior u v) 2 μT := by
    simpa [μT] using measurableNormalExterior_memLp_two_Icc σ u v T
  have hcLp : MemLp c 2 μT :=
    hc.memLp_of_hasCompactSupport hcc
  have hprod : Integrable
      (fun p => measurableNormalExterior u v p * c p) μT := by
    exact memLp_one_iff_integrable.mp (hcLp.mul' hF)
  have hSmeas : MeasurableSet S :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hrest : μ.restrict S = μT := by
    dsimp [μ, μT, S]
    rw [← Measure.restrict_prod_eq_prod_univ]
  have hprodOn : IntegrableOn
      (fun p => measurableNormalExterior u v p * c p) S μ := by
    rw [IntegrableOn, hrest]
    exact hprod
  have hind := (integrable_indicator_iff hSmeas).2 hprodOn
  have hzero : ∀ p, p ∉ S → c p = 0 := by
    intro p hp
    by_contra hcp
    have hpsupp : p ∈ tsupport c := subset_tsupport _ hcp
    have hpball := hT hpsupp
    have htnorm : ‖p.1‖ ≤ ‖p‖ := by
      simp only [Prod.norm_def]
      exact le_max_left _ _
    have hpball' : ‖p‖ ≤ T := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hpball
    have ht : p.1 ∈ Set.Icc (-T) T := by
      have habs : |p.1| ≤ T := by
        simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using
          htnorm.trans hpball'
      exact (abs_le.mp habs)
    exact hp ⟨ht, Set.mem_univ _⟩
  have heq : S.indicator
      (fun p => measurableNormalExterior u v p * c p) =
      (fun p => measurableNormalExterior u v p * c p) := by
    funext p
    by_cases hp : p ∈ S
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp, hzero p hp]
  rw [heq] at hind
  simpa [μ] using hind

private lemma measurableNormalExterior_norm_closedBall_integrable
    (σ : ℝ) (u v : GlobalSolution σ) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      (Metric.closedBall (0 : ℝ × (ℝ × ℝ)) R).indicator
        (fun q => ‖measurableNormalExterior u v q‖) p)
      (volume.prod (volume.prod volume)) := by
  let K : Set (ℝ × (ℝ × ℝ)) := Metric.closedBall 0 R
  let S : Set (ℝ × (ℝ × ℝ)) := Set.Icc (-R) R ×ˢ Set.univ
  let μ : Measure (ℝ × (ℝ × ℝ)) := volume.prod (volume.prod volume)
  let μR : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict (Set.Icc (-R) R)).prod (volume.prod volume)
  have hKmeas : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hF : MemLp (measurableNormalExterior u v) 2 μR := by
    simpa [μR] using measurableNormalExterior_memLp_two_Icc σ u v R
  have hFK2 : MemLp (K.indicator (measurableNormalExterior u v)) 2 μR :=
    hF.indicator hKmeas
  have hKfinite : μR K ≠ ∞ := by
    exact (isCompact_closedBall (0 : ℝ × (ℝ × ℝ)) R).measure_lt_top.ne
  have hFK1 : MemLp (K.indicator (measurableNormalExterior u v)) 1 μR :=
    hFK2.mono_exponent_of_measure_support_ne_top (s := K)
      (by intro p hp; simp [Set.indicator_of_notMem hp]) hKfinite (by norm_num)
  have hIntR : Integrable (K.indicator (measurableNormalExterior u v)) μR :=
    memLp_one_iff_integrable.mp hFK1
  have hKS : K ⊆ S := by
    intro p hp
    have hpnorm : ‖p‖ ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hp
    have ht : ‖p.1‖ ≤ R := by
      exact (by simp [Prod.norm_def] : ‖p.1‖ ≤ ‖p‖).trans hpnorm
    have habs : |p.1| ≤ R := by simpa [Real.norm_eq_abs] using ht
    exact ⟨abs_le.mp habs, Set.mem_univ _⟩
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hrest : μ.restrict S = μR := by
    dsimp [μ, μR, S]
    rw [← Measure.restrict_prod_eq_prod_univ]
  have hIntOn : IntegrableOn (K.indicator (measurableNormalExterior u v)) S μ := by
    rw [IntegrableOn, hrest]
    exact hIntR
  have hind := (integrable_indicator_iff hSmeas).2 hIntOn
  have heq : S.indicator (K.indicator (measurableNormalExterior u v)) =
      K.indicator (measurableNormalExterior u v) := by
    rw [Set.indicator_indicator, Set.inter_eq_right.mpr hKS]
  rw [heq] at hind
  have hnorm := hind.norm
  simpa only [μ, K, norm_indicator_eq_indicator_norm] using hnorm

private def normalFirstRemainder
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  spacetimeNormalPartial Φ p -
    spacetimeNormalPartial Φ (p.1, (0, p.2.2))

private def normalSecondRemainder
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  Φ p - Φ (p.1, (0, p.2.2)) -
    (p.2.1 : ℂ) * spacetimeNormalPartial Φ (p.1, (0, p.2.2))

private def normalBoundaryRemainder
    (n : ℕ) (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  2 * lowerHalfCutoffDeriv n p.2.1 * normalFirstRemainder Φ p +
    lowerHalfCutoffSecond n p.2.1 * normalSecondRemainder Φ p

private lemma normalBoundaryRemainder_continuous (n : ℕ)
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    Continuous (normalBoundaryRemainder n Φ) := by
  have hcut1 : Continuous (lowerHalfCutoffDeriv n) := by
    have hc : Continuous (deriv (lowerHalfCutoff n)) := by
      simpa only [iteratedDeriv_one] using
        (lowerHalfCutoff_contDiff n).continuous_iteratedDeriv 1 (by norm_num)
    convert hc using 1
    funext x
    exact (lowerHalfCutoff_deriv n x).symm
  have hcut2 : Continuous (lowerHalfCutoffSecond n) := by
    have hc := (lowerHalfCutoff_contDiff n).continuous_iteratedDeriv 2
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    convert hc using 1
    funext x
    exact (lowerHalfCutoff_second n x).symm
  unfold normalBoundaryRemainder normalFirstRemainder normalSecondRemainder
  fun_prop

private lemma norm_le_max_radius_of_normal_projection
    {R s a t r : ℝ} (hR : ‖(t, (a, r))‖ ≤ R) (hs : |s| ≤ 1) :
    ‖(t, (s, r))‖ ≤ max R 1 := by
  simp only [Prod.norm_def, Real.norm_eq_abs] at hR ⊢
  have ht : |t| ≤ R := (le_max_left _ _).trans hR
  have hr : |r| ≤ R :=
    (le_max_right |a| |r|).trans ((le_max_right |t| _).trans hR)
  exact max_le (ht.trans (le_max_left _ _))
    (max_le (hs.trans (le_max_right _ _)) (hr.trans (le_max_left _ _)))

private theorem normalBoundaryRemainder_integral_tendsto_zero
    (σ : ℝ) (u v : GlobalSolution σ)
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hΦc : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ)) :
    Tendsto (fun n : ℕ => ∫ p,
        measurableNormalExterior u v p * normalBoundaryRemainder n Φ p
        ∂(volume.prod (volume.prod volume))) atTop (nhds 0) := by
  obtain ⟨R, hRpos, hR⟩ :=
    hΦc.isCompact.isBounded.subset_closedBall_lt 0
      (0 : ℝ × (ℝ × ℝ))
  let L : ℝ := max R 1
  let K : Set (ℝ × (ℝ × ℝ)) := Metric.closedBall 0 L
  obtain ⟨M, hM0, hM1, hM2⟩ := exists_smoothTransition_deriv_bounds'
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0
    (spacetimeNormalPartial (spacetimeNormalPartial Φ))
  have hC0 : 0 ≤ C := by
    have hle := SchwartzMap.le_seminorm ℂ 0 0
      (spacetimeNormalPartial (spacetimeNormalPartial Φ)) (0, (0, 0))
    exact (norm_nonneg
      (spacetimeNormalPartial (spacetimeNormalPartial Φ) (0, (0, 0)))).trans
        (by simpa [C] using hle)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun p => measurableNormalExterior u v p *
        normalBoundaryRemainder n Φ p)
      (volume.prod (volume.prod volume)) :=
    (measurableNormalExterior_measurable u v).aestronglyMeasurable.mul
      (normalBoundaryRemainder_continuous n Φ).stronglyMeasurable.aestronglyMeasurable
  have hpoint (p : ℝ × (ℝ × ℝ)) : Tendsto (fun n : ℕ =>
      measurableNormalExterior u v p * normalBoundaryRemainder n Φ p)
      atTop (nhds 0) := by
    by_cases hsneg : p.2.1 < 0
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [lowerHalfCutoffDeriv_eventually_zero_of_neg hsneg,
          lowerHalfCutoffSecond_eventually_zero_of_neg hsneg] with n h1 h2
        simp [normalBoundaryRemainder, h1, h2])
    · by_cases hspos : 0 < p.2.1
      · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => by
          simp [normalBoundaryRemainder,
            lowerHalfCutoffDeriv_eq_zero_of_pos n hspos,
            lowerHalfCutoffSecond_eq_zero_of_pos n hspos])
      · have hs0 : p.2.1 = 0 := le_antisymm (le_of_not_gt hspos)
          (le_of_not_gt hsneg)
        exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => by
          have hpEq : p = (p.1, (0, p.2.2)) := by
            ext <;> simp [hs0]
          have hr : normalBoundaryRemainder n Φ p = 0 := by
            rw [hpEq]
            unfold normalBoundaryRemainder normalFirstRemainder normalSecondRemainder
            simp
          change (0 : ℂ) = measurableNormalExterior u v p *
            normalBoundaryRemainder n Φ p
          rw [hr, mul_zero])
  have hsupport (n : ℕ) (p : ℝ × (ℝ × ℝ))
      (hpK : p ∉ K) : normalBoundaryRemainder n Φ p = 0 := by
    let N : ℝ := (n : ℝ) + 1
    have hNpos : 0 < N := by dsimp [N]; positivity
    by_cases hx : -N * p.2.1 ∈ Set.Icc (0 : ℝ) 1
    · have hsle : p.2.1 ≤ 0 := by rcases hx with ⟨hx0, hx1⟩; nlinarith
      have hsabs : |p.2.1| ≤ 1 := by
        rw [abs_of_nonpos hsle]
        rcases hx with ⟨hx0, hx1⟩
        have hN1 : 1 ≤ N := by
          dsimp [N]
          have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        nlinarith
      have hpnot : ¬ ‖p‖ ≤ L := by
        simpa [K, Metric.mem_closedBall, dist_zero_right] using hpK
      have hval (a : ℝ) (ha : Φ (p.1, (a, p.2.2)) ≠ 0) : False := by
        have hmem := hR (subset_tsupport _ ha)
        have hnorm : ‖(p.1, (a, p.2.2))‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hmem
        exact hpnot (norm_le_max_radius_of_normal_projection hnorm hsabs)
      have hdval (a : ℝ)
          (ha : spacetimeNormalPartial Φ (p.1, (a, p.2.2)) ≠ 0) : False := by
        have hsuppD : (p.1, (a, p.2.2)) ∈ tsupport
            (Φ : ℝ × (ℝ × ℝ) → ℂ) :=
          (SchwartzMap.tsupport_lineDerivOp_subset _ Φ)
            (subset_tsupport _ ha)
        have hmem := hR hsuppD
        have hnorm : ‖(p.1, (a, p.2.2))‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hmem
        exact hpnot (norm_le_max_radius_of_normal_projection hnorm hsabs)
      have hΦp : Φ p = 0 := by
        by_contra hne
        exact hval p.2.1 hne
      have hΦ0 : Φ (p.1, (0, p.2.2)) = 0 := by
        by_contra hne
        exact hval 0 hne
      have hDp : spacetimeNormalPartial Φ p = 0 := by
        by_contra hne
        exact hdval p.2.1 hne
      have hD0 : spacetimeNormalPartial Φ (p.1, (0, p.2.2)) = 0 := by
        by_contra hne
        exact hdval 0 hne
      simp [normalBoundaryRemainder, normalFirstRemainder,
        normalSecondRemainder, hΦp, hΦ0, hDp, hD0]
    · have hxout : -N * p.2.1 < 0 ∨ 1 < -N * p.2.1 := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hx
      rcases hxout with hxneg | hxone
      · have hspos : 0 < p.2.1 := by nlinarith
        simp [normalBoundaryRemainder,
          lowerHalfCutoffDeriv_eq_zero_of_pos n hspos,
          lowerHalfCutoffSecond_eq_zero_of_pos n hspos]
      · unfold normalBoundaryRemainder lowerHalfCutoffDeriv lowerHalfCutoffSecond
        have harg : -((n : ℝ) + 1) * p.2.1 = -N * p.2.1 := by rfl
        rw [smoothTransition_deriv_eq_zero_of_one_lt (harg ▸ hxone),
          smoothTransition_second_eq_zero_of_one_lt (harg ▸ hxone)]
        simp
  have hbound (n : ℕ) (p : ℝ × (ℝ × ℝ)) :
      ‖normalBoundaryRemainder n Φ p‖ ≤
        3 * M * C * K.indicator (fun _ => (1 : ℝ)) p := by
    by_cases hpK : p ∈ K
    · rw [Set.indicator_of_mem hpK]
      let N : ℝ := (n : ℝ) + 1
      have hNpos : 0 < N := by dsimp [N]; positivity
      by_cases hx : -N * p.2.1 ∈ Set.Icc (0 : ℝ) 1
      · rcases hx with ⟨hx0, hx1⟩
        have hsle : p.2.1 ≤ 0 := by nlinarith
        have hNs : N * |p.2.1| ≤ 1 := by
          rw [abs_of_nonpos hsle]
          nlinarith
        have hcut1 : ‖lowerHalfCutoffDeriv n p.2.1‖ ≤ N * M := by
          unfold lowerHalfCutoffDeriv
          simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
          have hnpos : 0 < (n : ℝ) + 1 := by positivity
          have hcast : ((n : ℝ) : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by
            norm_cast
          rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
          simpa [N] using
            mul_le_mul_of_nonneg_left (hM1 (-((n : ℝ) + 1) * p.2.1))
              hnpos.le
        have hcut2 : ‖lowerHalfCutoffSecond n p.2.1‖ ≤ N ^ 2 * M := by
          unfold lowerHalfCutoffSecond
          simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          have hnpos : 0 < (n : ℝ) + 1 := by positivity
          have hcast : ((n : ℝ) : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by
            norm_cast
          rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
          simpa [N] using
            mul_le_mul_of_nonneg_left (hM2 (-((n : ℝ) + 1) * p.2.1))
              (sq_nonneg ((n : ℝ) + 1))
        have hrem1 : ‖normalFirstRemainder Φ p‖ ≤ C * |p.2.1| := by
          exact spacetimeNormalPartial_difference_bound Φ p.1 p.2.1 p.2.2
        have hrem2 : ‖normalSecondRemainder Φ p‖ ≤ C * |p.2.1| ^ 2 := by
          exact spacetimeNormal_second_remainder_bound Φ p.1 p.2.1 p.2.2 hsle
        calc
          ‖normalBoundaryRemainder n Φ p‖ ≤
              2 * ‖lowerHalfCutoffDeriv n p.2.1‖ * ‖normalFirstRemainder Φ p‖ +
                ‖lowerHalfCutoffSecond n p.2.1‖ * ‖normalSecondRemainder Φ p‖ := by
            unfold normalBoundaryRemainder
            calc
              ‖2 * lowerHalfCutoffDeriv n p.2.1 * normalFirstRemainder Φ p +
                  lowerHalfCutoffSecond n p.2.1 * normalSecondRemainder Φ p‖ ≤
                  ‖2 * lowerHalfCutoffDeriv n p.2.1 * normalFirstRemainder Φ p‖ +
                    ‖lowerHalfCutoffSecond n p.2.1 * normalSecondRemainder Φ p‖ :=
                norm_add_le _ _
              _ = _ := by simp [norm_mul]
          _ ≤ 2 * (N * M) * (C * |p.2.1|) +
                (N ^ 2 * M) * (C * |p.2.1| ^ 2) := by gcongr
          _ = 2 * (M * C) * (N * |p.2.1|) +
                (M * C) * (N * |p.2.1|) ^ 2 := by ring
          _ ≤ 2 * (M * C) * 1 + (M * C) * 1 ^ 2 := by gcongr
          _ = 3 * M * C * 1 := by ring
      · have hxout : -N * p.2.1 < 0 ∨ 1 < -N * p.2.1 := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hx
        rcases hxout with hxneg | hxone
        · have hspos : 0 < p.2.1 := by nlinarith
          simp only [normalBoundaryRemainder,
            lowerHalfCutoffDeriv_eq_zero_of_pos n hspos,
            lowerHalfCutoffSecond_eq_zero_of_pos n hspos,
            mul_zero, zero_mul, zero_add, norm_zero]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hM0) hC0) zero_le_one
        · unfold normalBoundaryRemainder lowerHalfCutoffDeriv lowerHalfCutoffSecond
          have harg : -((n : ℝ) + 1) * p.2.1 = -N * p.2.1 := by rfl
          rw [smoothTransition_deriv_eq_zero_of_one_lt (harg ▸ hxone),
            smoothTransition_second_eq_zero_of_one_lt (harg ▸ hxone)]
          simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_add, norm_zero]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hM0) hC0) zero_le_one
    · rw [Set.indicator_of_notMem hpK, mul_zero, hsupport n p hpK, norm_zero]
  have hdomInt : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      3 * M * C * K.indicator
        (fun q => ‖measurableNormalExterior u v q‖) p)
      (volume.prod (volume.prod volume)) := by
    have hL0 : 0 ≤ L := zero_le_one.trans (le_max_right R 1)
    exact (measurableNormalExterior_norm_closedBall_integrable
      σ u v L hL0).const_mul (3 * M * C)
  have hdom : ∀ n p,
      ‖measurableNormalExterior u v p * normalBoundaryRemainder n Φ p‖ ≤
        3 * M * C * K.indicator
          (fun q => ‖measurableNormalExterior u v q‖) p := by
    intro n p
    rw [norm_mul]
    by_cases hpK : p ∈ K
    · rw [Set.indicator_of_mem hpK]
      have hb : ‖normalBoundaryRemainder n Φ p‖ ≤ 3 * M * C := by
        simpa [Set.indicator_of_mem hpK] using hbound n p
      calc
        ‖measurableNormalExterior u v p‖ * ‖normalBoundaryRemainder n Φ p‖ ≤
            ‖measurableNormalExterior u v p‖ * (3 * M * C) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = 3 * M * C * ‖measurableNormalExterior u v p‖ := by ring
    · rw [Set.indicator_of_notMem hpK, mul_zero, hsupport n p hpK,
        norm_zero, mul_zero]
  simpa using tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume.prod (volume.prod volume))
    (F := fun n p => measurableNormalExterior u v p *
      normalBoundaryRemainder n Φ p) (f := fun _ => 0)
    (fun p => 3 * M * C * K.indicator
      (fun q => ‖measurableNormalExterior u v q‖) p)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall (hdom n))
    hdomInt (Filter.Eventually.of_forall hpoint)

private def normalSeparatedTest (w : ℝ → ℂ) (ψ : ℝ × ℝ → ℂ)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  w p.2.1 * ψ (p.1, p.2.2)

private lemma normalSeparatedTest_continuous
    {w : ℝ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (hw : Continuous w) (hψ : Continuous ψ) :
    Continuous (normalSeparatedTest w ψ) := by
  unfold normalSeparatedTest
  fun_prop

private lemma normalSeparatedTest_hasCompactSupport
    {w : ℝ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (hw : HasCompactSupport w) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (normalSeparatedTest w ψ) := by
  let e : (ℝ × (ℝ × ℝ)) ≃ₜ ((ℝ × ℝ) × ℝ) :=
    { toFun := fun p => ((p.1, p.2.2), p.2.1)
      invFun := fun q => (q.1.1, (q.2, q.1.2))
      left_inv := by intro p; rfl
      right_inv := by intro q; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let c : ((ℝ × ℝ) × ℝ) → ℂ := fun q => w q.2 * ψ q.1
  have hc : HasCompactSupport c := by
    refine HasCompactSupport.intro
      (K := tsupport ψ ×ˢ tsupport w)
      (hψ.isCompact.prod hw.isCompact) ?_
    intro q hq
    by_contra hn
    apply hq
    exact ⟨subset_tsupport _ (right_ne_zero_of_mul hn),
      subset_tsupport _ (left_ne_zero_of_mul hn)⟩
  have he := hc.comp_homeomorph e
  convert he using 1
  ext p
  rfl

private lemma measurableNormalExterior_normalSeparatedTest_integrable
    (σ : ℝ) (u v : GlobalSolution σ)
    {w : ℝ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p => measurableNormalExterior u v p *
      normalSeparatedTest w ψ p) (volume.prod (volume.prod volume)) := by
  exact measurableNormalExterior_mul_continuous_compact_integrable
    σ u v _ (normalSeparatedTest_continuous hw hψ)
      (normalSeparatedTest_hasCompactSupport hwc hψc)

private lemma normalSeparatedTest_integral_eq_scalarization
    (σ : ℝ) (u v : GlobalSolution σ)
    {w : ℝ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (A B : ℝ)
    (hψtime : ∀ z ∈ tsupport ψ, z.1 ∈ Set.Icc A B) :
    (∫ p, measurableNormalExterior u v p * normalSeparatedTest w ψ p
        ∂(volume.prod (volume.prod volume))) =
      ∫ s : ℝ, w s * measurableNormalScalarizationOn u v ψ A B s := by
  let f : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    measurableNormalExterior u v p * normalSeparatedTest w ψ p
  have hf : Integrable f (volume.prod (volume.prod volume)) :=
    measurableNormalExterior_normalSeparatedTest_integrable
      σ u v hw hwc hψ hψc
  let g : (ℝ × ℝ) × ℝ → ℂ := fun q => f (q.1.1, (q.1.2, q.2))
  have hg : Integrable g ((volume.prod volume).prod volume) := by
    exact ((measurePreserving_prodAssoc (volume : Measure ℝ)
      (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding (g := f)).mpr hf
  have hassoc :
      (∫ q : (ℝ × ℝ) × ℝ, g q ∂((volume.prod volume).prod volume)) =
        ∫ p : ℝ × (ℝ × ℝ), f p ∂(volume.prod (volume.prod volume)) := by
    exact (measurePreserving_prodAssoc (volume : Measure ℝ)
      (volume : Measure ℝ) (volume : Measure ℝ)).integral_comp
      MeasurableEquiv.prodAssoc.measurableEmbedding f
  have hψzero (t : ℝ) (ht : t ∉ Set.Icc A B) (r : ℝ) : ψ (t, r) = 0 := by
    by_contra hn
    exact ht (hψtime (t, r) (subset_tsupport _ hn))
  have htime (s : ℝ) :
      measurableNormalScalarizationOn u v ψ A B s =
        ∫ t : ℝ, ∫ r : ℝ,
          measurableNormalExterior u v (t, (s, r)) * ψ (t, r) := by
    unfold measurableNormalScalarizationOn timeMeasure
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Icc A B
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      simp [hψzero t ht]
  rw [← hassoc, integral_prod _ hg]
  have hinner := hg.integral_prod_left
  rw [integral_prod_symm _ hinner]
  apply integral_congr_ae
  filter_upwards with s
  rw [htime]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  dsimp [g, f, normalSeparatedTest]
  ring

private lemma lowerHalfCutoffDeriv_continuous (n : ℕ) :
    Continuous (lowerHalfCutoffDeriv n) := by
  have hc : Continuous (deriv (lowerHalfCutoff n)) := by
    simpa only [iteratedDeriv_one] using
      (lowerHalfCutoff_contDiff n).continuous_iteratedDeriv 1 (by norm_num)
  convert hc using 1
  ext s
  exact (lowerHalfCutoff_deriv n s).symm

private lemma lowerHalfCutoffSecond_continuous (n : ℕ) :
    Continuous (lowerHalfCutoffSecond n) := by
  have hc := (lowerHalfCutoff_contDiff n).continuous_iteratedDeriv 2
    (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  convert hc using 1
  ext s
  exact (lowerHalfCutoff_second n s).symm

private lemma lowerHalfCutoffDeriv_hasCompactSupport (n : ℕ) :
    HasCompactSupport (lowerHalfCutoffDeriv n) := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 0) isCompact_Icc ?_
  intro s hs
  have hout : s < -1 ∨ 0 < s := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hs
  rcases hout with hs | hs
  · unfold lowerHalfCutoffDeriv
    rw [smoothTransition_deriv_eq_zero_of_one_lt]
    · simp
    · have hn : 1 ≤ (n : ℝ) + 1 := by
        linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      nlinarith
  · exact lowerHalfCutoffDeriv_eq_zero_of_pos n hs

private lemma lowerHalfCutoffSecond_hasCompactSupport (n : ℕ) :
    HasCompactSupport (lowerHalfCutoffSecond n) := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 0) isCompact_Icc ?_
  intro s hs
  have hout : s < -1 ∨ 0 < s := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hs
  rcases hout with hs | hs
  · unfold lowerHalfCutoffSecond
    rw [smoothTransition_second_eq_zero_of_one_lt]
    · simp
    · have hn : 1 ≤ (n : ℝ) + 1 := by
        linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      nlinarith
  · exact lowerHalfCutoffSecond_eq_zero_of_pos n hs

private lemma normalBoundaryRemainder_hasCompactSupport (n : ℕ)
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport (normalBoundaryRemainder n Φ) := by
  let ψ₁ : ℝ × ℝ → ℂ := fun z => spacetimeNormalPartial Φ (z.1, (0, z.2))
  let ψ₀ : ℝ × ℝ → ℂ := fun z => Φ (z.1, (0, z.2))
  have hD : HasCompactSupport
      (spacetimeNormalPartial Φ : ℝ × (ℝ × ℝ) → ℂ) :=
    spacetimeNormalPartial_hasCompactSupport Φ hΦ
  have hψ₁ : HasCompactSupport ψ₁ := by
    convert normalBoundaryNormalPartial_hasCompactSupport Φ hΦ using 1
    ext z
    rfl
  have hψ₀ : HasCompactSupport ψ₀ := by
    convert normalBoundaryRestriction_hasCompactSupport Φ hΦ using 1
    ext z
    rfl
  have h1a : HasCompactSupport (fun p : ℝ × (ℝ × ℝ) =>
      lowerHalfCutoffDeriv n p.2.1 * spacetimeNormalPartial Φ p) := by
    exact hD.mul_left
  have h1b : HasCompactSupport (normalSeparatedTest
      (lowerHalfCutoffDeriv n) ψ₁) :=
    normalSeparatedTest_hasCompactSupport
      (lowerHalfCutoffDeriv_hasCompactSupport n) hψ₁
  have h2a : HasCompactSupport (fun p : ℝ × (ℝ × ℝ) =>
      lowerHalfCutoffSecond n p.2.1 * Φ p) := hΦ.mul_left
  have h2b : HasCompactSupport (normalSeparatedTest
      (lowerHalfCutoffSecond n) ψ₀) :=
    normalSeparatedTest_hasCompactSupport
      (lowerHalfCutoffSecond_hasCompactSupport n) hψ₀
  have h2c : HasCompactSupport (normalSeparatedTest
      (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁) := by
    exact normalSeparatedTest_hasCompactSupport
      ((lowerHalfCutoffSecond_hasCompactSupport n).mul_right) hψ₁
  have h1 : HasCompactSupport (fun p : ℝ × (ℝ × ℝ) =>
      (2 : ℂ) * ((lowerHalfCutoffDeriv n p.2.1 * spacetimeNormalPartial Φ p) -
        normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁ p)) := by
    change HasCompactSupport ((fun _ : ℝ × (ℝ × ℝ) => (2 : ℂ)) *
      ((fun p => lowerHalfCutoffDeriv n p.2.1 * spacetimeNormalPartial Φ p) -
        normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁))
    exact (h1a.sub h1b).mul_left
  have hsum := h1.add ((h2a.sub h2b).sub h2c)
  have heq : normalBoundaryRemainder n Φ = fun p =>
      (2 : ℂ) * ((lowerHalfCutoffDeriv n p.2.1 * spacetimeNormalPartial Φ p) -
        normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁ p) +
      ((lowerHalfCutoffSecond n p.2.1 * Φ p -
        normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p) -
        normalSeparatedTest
          (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p) := by
    funext p
    simp only [normalBoundaryRemainder, normalFirstRemainder,
      normalSecondRemainder, normalSeparatedTest, ψ₀, ψ₁]
    ring
  rw [heq]
  exact hsum

private theorem normalBoundaryIntegral_tendsto_zero
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hΦc : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ))
    (A B : ℝ) (hAB : A < B) (hABI : Set.Icc A B ⊆ I)
    (hΦtime : ∀ p ∈ tsupport (Φ : ℝ × (ℝ × ℝ) → ℂ),
      p.1 ∈ Set.Icc A B) :
    Tendsto (fun n : ℕ => ∫ p, measurableNormalExterior u v p *
        (2 * lowerHalfCutoffDeriv n p.2.1 *
            spacetimeNormalPartial Φ p +
          lowerHalfCutoffSecond n p.2.1 * Φ p)
        ∂(volume.prod (volume.prod volume))) atTop (nhds 0) := by
  let ψ₀ : 𝓢(ℝ × ℝ, ℂ) := normalBoundaryRestriction Φ
  let ψ₁ : 𝓢(ℝ × ℝ, ℂ) :=
    normalBoundaryRestriction (spacetimeNormalPartial Φ)
  have hψ₀c : HasCompactSupport (ψ₀ : ℝ × ℝ → ℂ) := by
    exact normalBoundaryRestriction_hasCompactSupport Φ hΦc
  have hψ₁c : HasCompactSupport (ψ₁ : ℝ × ℝ → ℂ) := by
    exact normalBoundaryNormalPartial_hasCompactSupport Φ hΦc
  have hψ₀time : ∀ z ∈ tsupport (ψ₀ : ℝ × ℝ → ℂ),
      z.1 ∈ Set.Icc A B := by
    apply closure_minimal
    · intro z hz
      exact hΦtime (z.1, (0, z.2)) (subset_tsupport _ hz)
    · exact isClosed_Icc.preimage continuous_fst
  have hψ₁time : ∀ z ∈ tsupport (ψ₁ : ℝ × ℝ → ℂ),
      z.1 ∈ Set.Icc A B := by
    apply closure_minimal
    · intro z hz
      have hpD : (z.1, (0, z.2)) ∈ tsupport
          (spacetimeNormalPartial Φ : ℝ × (ℝ × ℝ) → ℂ) :=
        subset_tsupport _ hz
      exact hΦtime _ (SchwartzMap.tsupport_lineDerivOp_subset _ Φ hpD)
    · exact isClosed_Icc.preimage continuous_fst
  let h₀ : ℝ → ℂ := measurableNormalScalarizationOn u v ψ₀ A B
  let h₁ : ℝ → ℂ := measurableNormalScalarizationOn u v ψ₁ A B
  have h₀sm : StronglyMeasurable h₀ :=
    measurableNormalScalarizationOn_stronglyMeasurable u v ψ₀
      ψ₀.continuous.measurable A B
  have h₁sm : StronglyMeasurable h₁ :=
    measurableNormalScalarizationOn_stronglyMeasurable u v ψ₁
      ψ₁.continuous.measurable A B
  have h₀zero : h₀ 0 = 0 := measurableNormalScalarizationOn_zero u v ψ₀ A B
  have h₁zero : h₁ 0 = 0 := measurableNormalScalarizationOn_zero u v ψ₁ A B
  have hq₀ : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ * h₀ s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    measurableNormalScalarizationOn_div_tendsto_zero
      σ u v I hI hmod ψ₀ hψ₀c A B hAB hABI
  have hq₁ : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ * h₁ s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    measurableNormalScalarizationOn_div_tendsto_zero
      σ u v I hI hmod ψ₁ hψ₁c A B hAB hABI
  have hh₁zero : Tendsto h₁ (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hs : Tendsto (fun s : ℝ => (s : ℂ))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
      Complex.continuous_ofReal.tendsto 0 |>.mono_left inf_le_left
    have hm := hs.mul hq₁
    simpa only [mul_zero] using hm.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs0
      have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hs0)
      exact mul_inv_cancel_left₀ hsne (h₁ s))
  let k : ℝ → ℂ := fun s => (s : ℂ) * h₁ s
  have hksm : StronglyMeasurable k := by
    exact ((Complex.continuous_ofReal.measurable).mul h₁sm.measurable).stronglyMeasurable
  have hkzero : k 0 = 0 := by simp [k]
  have hqk : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ * k s)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    apply hh₁zero.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs0
    have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hs0)
    dsimp [k]
    field_simp
  have hs₀ := lowerHalfCutoffSecond_scalar_tendsto_zero h₀ h₀sm h₀zero hq₀
  have hs₁ := lowerHalfCutoffDeriv_scalar_tendsto_zero h₁ h₁sm h₁zero hq₁
  have hsk := lowerHalfCutoffSecond_scalar_tendsto_zero k hksm hkzero hqk
  have hfull₀ : Tendsto (fun n : ℕ => ∫ p,
      measurableNormalExterior u v p *
        normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p
      ∂(volume.prod (volume.prod volume))) atTop (nhds 0) := by
    apply hs₀.congr'
    filter_upwards with n
    exact (normalSeparatedTest_integral_eq_scalarization σ u v
      (lowerHalfCutoffSecond_continuous n)
      (lowerHalfCutoffSecond_hasCompactSupport n)
      ψ₀.continuous hψ₀c A B hψ₀time).symm
  have hfull₁ : Tendsto (fun n : ℕ => ∫ p,
      measurableNormalExterior u v p *
        normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁ p
      ∂(volume.prod (volume.prod volume))) atTop (nhds 0) := by
    apply hs₁.congr'
    filter_upwards with n
    exact (normalSeparatedTest_integral_eq_scalarization σ u v
      (lowerHalfCutoffDeriv_continuous n)
      (lowerHalfCutoffDeriv_hasCompactSupport n)
      ψ₁.continuous hψ₁c A B hψ₁time).symm
  have hfullk : Tendsto (fun n : ℕ => ∫ p,
      measurableNormalExterior u v p * normalSeparatedTest
        (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p
      ∂(volume.prod (volume.prod volume))) atTop (nhds 0) := by
    apply hsk.congr'
    filter_upwards with n
    calc
      (∫ s : ℝ, lowerHalfCutoffSecond n s * k s) =
          ∫ s : ℝ, (lowerHalfCutoffSecond n s * (s : ℂ)) * h₁ s := by
        apply integral_congr_ae
        filter_upwards with s
        dsimp [k]
        ring
      _ = _ := (normalSeparatedTest_integral_eq_scalarization σ u v
        ((lowerHalfCutoffSecond_continuous n).mul Complex.continuous_ofReal)
        ((lowerHalfCutoffSecond_hasCompactSupport n).mul_right)
        ψ₁.continuous hψ₁c A B hψ₁time).symm
  have hrem := normalBoundaryRemainder_integral_tendsto_zero
    σ u v Φ hΦc
  have hsum := hrem.add ((hfull₁.const_mul (2 : ℂ)).add (hfull₀.add hfullk))
  have hsum0 : Tendsto (fun x =>
      (∫ p, measurableNormalExterior u v p * normalBoundaryRemainder x Φ p
        ∂(volume.prod (volume.prod volume))) +
      (2 * (∫ p, measurableNormalExterior u v p *
        normalSeparatedTest (lowerHalfCutoffDeriv x) ψ₁ p
        ∂(volume.prod (volume.prod volume))) +
      ((∫ p, measurableNormalExterior u v p *
        normalSeparatedTest (lowerHalfCutoffSecond x) ψ₀ p
        ∂(volume.prod (volume.prod volume))) +
      (∫ p, measurableNormalExterior u v p * normalSeparatedTest
        (fun s => lowerHalfCutoffSecond x s * (s : ℂ)) ψ₁ p
        ∂(volume.prod (volume.prod volume)))))) atTop (nhds 0) := by
    simpa using hsum
  apply hsum0.congr'
  filter_upwards with n
  have hremInt : Integrable (fun p => measurableNormalExterior u v p *
      normalBoundaryRemainder n Φ p) (volume.prod (volume.prod volume)) :=
    measurableNormalExterior_mul_continuous_compact_integrable σ u v _
      (normalBoundaryRemainder_continuous n Φ)
      (normalBoundaryRemainder_hasCompactSupport n Φ hΦc)
  have h1Int := measurableNormalExterior_normalSeparatedTest_integrable σ u v
    (lowerHalfCutoffDeriv_continuous n)
    (lowerHalfCutoffDeriv_hasCompactSupport n) ψ₁.continuous hψ₁c
  have h0Int := measurableNormalExterior_normalSeparatedTest_integrable σ u v
    (lowerHalfCutoffSecond_continuous n)
    (lowerHalfCutoffSecond_hasCompactSupport n) ψ₀.continuous hψ₀c
  have hwk : Continuous (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) :=
    (lowerHalfCutoffSecond_continuous n).mul Complex.continuous_ofReal
  have hwkc : HasCompactSupport
      (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) :=
    (lowerHalfCutoffSecond_hasCompactSupport n).mul_right
  have hkInt' : Integrable (fun p => measurableNormalExterior u v p *
      normalSeparatedTest
        (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p)
      (volume.prod (volume.prod volume)) := by
    exact measurableNormalExterior_normalSeparatedTest_integrable σ u v
      hwk hwkc ψ₁.continuous hψ₁c
  symm
  calc
    (∫ p, measurableNormalExterior u v p *
        (2 * lowerHalfCutoffDeriv n p.2.1 * spacetimeNormalPartial Φ p +
          lowerHalfCutoffSecond n p.2.1 * Φ p)
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, (measurableNormalExterior u v p * normalBoundaryRemainder n Φ p) +
        (2 * (measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁ p) +
        ((measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p) +
        (measurableNormalExterior u v p * normalSeparatedTest
          (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p)))
        ∂(volume.prod (volume.prod volume)) := by
          apply integral_congr_ae
          filter_upwards with p
          simp only [normalBoundaryRemainder, normalFirstRemainder,
            normalSecondRemainder, normalSeparatedTest, ψ₀, ψ₁,
            normalBoundaryRestriction_apply]
          ring
    _ = (∫ p, measurableNormalExterior u v p * normalBoundaryRemainder n Φ p
          ∂(volume.prod (volume.prod volume))) +
        ∫ p, 2 * (measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁ p) +
        ((measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p) +
        (measurableNormalExterior u v p * normalSeparatedTest
          (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p))
          ∂(volume.prod (volume.prod volume)) := by
      simpa only [Pi.add_apply] using integral_add hremInt
        ((h1Int.const_mul (2 : ℂ)).add (h0Int.add hkInt'))
    _ = (∫ p, measurableNormalExterior u v p * normalBoundaryRemainder n Φ p
          ∂(volume.prod (volume.prod volume))) +
        ((∫ p, 2 * (measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffDeriv n) ψ₁ p)
          ∂(volume.prod (volume.prod volume))) +
        ∫ p, (measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p) +
        (measurableNormalExterior u v p * normalSeparatedTest
          (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p)
          ∂(volume.prod (volume.prod volume))) := by
      congr 1
      simpa only [Pi.add_apply] using
        integral_add (h1Int.const_mul (2 : ℂ)) (h0Int.add hkInt')
    _ = _ := by
      rw [show (∫ p, (measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p) +
          (measurableNormalExterior u v p * normalSeparatedTest
            (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p)
          ∂(volume.prod (volume.prod volume))) =
        (∫ p, measurableNormalExterior u v p *
          normalSeparatedTest (lowerHalfCutoffSecond n) ψ₀ p
          ∂(volume.prod (volume.prod volume))) +
        ∫ p, measurableNormalExterior u v p * normalSeparatedTest
          (fun s => lowerHalfCutoffSecond n s * (s : ℂ)) ψ₁ p
          ∂(volume.prod (volume.prod volume)) by
            simpa only [Pi.add_apply] using integral_add h0Int hkInt']
      rw [integral_const_mul]

private def lowerHalfRestriction (g : ℝ × (ℝ × ℝ) → ℂ)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  if p.2.1 < 0 then g p else 0

private lemma lowerHalfRestriction_integrable
    {g : ℝ × (ℝ × ℝ) → ℂ}
    (hg : Integrable g (volume.prod (volume.prod volume))) :
    Integrable (lowerHalfRestriction g) (volume.prod (volume.prod volume)) := by
  let S : Set (ℝ × (ℝ × ℝ)) := {p | p.2.1 < 0}
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const
  have hi := hg.indicator hS
  have heq : lowerHalfRestriction g = S.indicator g := by
    funext p
    by_cases hp : p.2.1 < 0 <;>
      simp [lowerHalfRestriction, S, Set.indicator, hp]
  rw [heq]
  exact hi

private theorem lowerHalfCutoff_integral_tendsto
    (g : ℝ × (ℝ × ℝ) → ℂ)
    (hg : Integrable g (volume.prod (volume.prod volume))) :
    Tendsto (fun n : ℕ => ∫ p, lowerHalfCutoff n p.2.1 * g p
        ∂(volume.prod (volume.prod volume))) atTop
      (nhds (∫ p, lowerHalfRestriction g p
        ∂(volume.prod (volume.prod volume)))) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) => lowerHalfCutoff n p.2.1 * g p)
      (volume.prod (volume.prod volume)) := by
    exact ((((lowerHalfCutoff_contDiff n).continuous.measurable.comp
      (measurable_fst.comp measurable_snd)).aemeasurable.mul
        hg.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
  have hbound (n : ℕ) (p : ℝ × (ℝ × ℝ)) :
      ‖lowerHalfCutoff n p.2.1 * g p‖ ≤ ‖g p‖ := by
    rw [norm_mul]
    have hnonneg := Real.smoothTransition.nonneg
      (-((n : ℝ) + 1) * p.2.1)
    have hle := Real.smoothTransition.le_one
      (-((n : ℝ) + 1) * p.2.1)
    have hcut : ‖lowerHalfCutoff n p.2.1‖ ≤ 1 := by
      unfold lowerHalfCutoff
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hcut (norm_nonneg (g p))
  have hpoint (p : ℝ × (ℝ × ℝ)) : Tendsto
      (fun n : ℕ => lowerHalfCutoff n p.2.1 * g p) atTop
      (nhds (lowerHalfRestriction g p)) := by
    simpa [lowerHalfRestriction] using
      (lowerHalfCutoff_tendsto_indicator p.2.1).mul_const (g p)
  simpa using tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume.prod (volume.prod volume))
    (F := fun n p => lowerHalfCutoff n p.2.1 * g p)
    (f := lowerHalfRestriction g) (fun p => ‖g p‖)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall (hbound n))
    hg.norm (Filter.Eventually.of_forall hpoint)

private lemma lowerHalfCutoff_mul_integrable
    (n : ℕ) {g : ℝ × (ℝ × ℝ) → ℂ}
    (hg : Integrable g (volume.prod (volume.prod volume))) :
    Integrable (fun p => lowerHalfCutoff n p.2.1 * g p)
      (volume.prod (volume.prod volume)) := by
  refine hg.mono ?_ ?_
  · exact ((((lowerHalfCutoff_contDiff n).continuous.measurable.comp
      (measurable_fst.comp measurable_snd)).aemeasurable.mul
        hg.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
  · filter_upwards with p
    rw [norm_mul]
    have hnonneg := Real.smoothTransition.nonneg
      (-((n : ℝ) + 1) * p.2.1)
    have hle := Real.smoothTransition.le_one
      (-((n : ℝ) + 1) * p.2.1)
    have hcut : ‖lowerHalfCutoff n p.2.1‖ ≤ 1 := by
      unfold lowerHalfCutoff
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hcut (norm_nonneg (g p))


/-- Extend a normal-coordinate field by zero from the upper half-space. -/
def zeroExtendNormal (F : ℝ × (ℝ × ℝ) → ℂ)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  if p.2.1 < 0 then F p else 0

/-- The correspondingly zero-extended forcing. -/
def zeroExtendForcing (Q F : ℝ × (ℝ × ℝ) → ℂ)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  if p.2.1 < 0 then Q p * F p else 0

lemma zeroExtendNormal_measurable {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF : Measurable F) : Measurable (zeroExtendNormal F) := by
  unfold zeroExtendNormal
  exact Measurable.ite
    (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
    hF measurable_const

/-- Cutting a normal-coordinate field to the lower half-space cannot increase
its local spacetime `L²` norm. -/
theorem zeroExtendNormal_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) :
    MemLp (zeroExtendNormal (measurableNormalExterior u v)) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)) := by
  have hF := measurableNormalExterior_memLp_two_Icc sigma u v T
  refine hF.mono
    (zeroExtendNormal_measurable
      (measurableNormalExterior_measurable u v)).aestronglyMeasurable ?_
  filter_upwards with p
  unfold zeroExtendNormal
  split_ifs <;> simp

/-- On an equal-modulus time set, the zero-extended forcing is locally `L²`.
The representative identity is used only after restriction to that set. -/
theorem zeroExtendForcing_memLp_two_Icc_of_sameModulus (sigma : ℝ)
    (u v : GlobalSolution sigma) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp
      (zeroExtendForcing (measurableRidgePotential sigma u)
        (measurableNormalExterior u v)) 2
      (((volume : Measure ℝ).restrict (Set.Icc (-T) T ∩ I)).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
  let S := measurableNormalExteriorSource sigma u v
  have hSfull := measurableNormalExteriorSource_memLp_two_Icc sigma u v T hT
  have htime : (volume : Measure ℝ).restrict (Set.Icc (-T) T ∩ I) ≤
      (volume : Measure ℝ).restrict (Set.Icc (-T) T) :=
    Measure.restrict_mono (Set.inter_subset_left) le_rfl
  have hmeasure :
      ((volume : Measure ℝ).restrict (Set.Icc (-T) T ∩ I)).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) ≤
        ((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.prod_mono htime le_rfl
  have hS := hSfull.mono_measure hmeasure
  have hmeasQF : Measurable
      (zeroExtendForcing (measurableRidgePotential sigma u)
        (measurableNormalExterior u v)) := by
    unfold zeroExtendForcing
    exact Measurable.ite
      (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
      ((measurableRidgePotential_measurable sigma u).mul
        (measurableNormalExterior_measurable u v)) measurable_const
  refine hS.mono
    hmeasQF.aestronglyMeasurable ?_
  have heq := measurableNormalExteriorSource_eq_ridge_mul sigma u v I hI hmod
  have hsubtime : (volume : Measure ℝ).restrict (Set.Icc (-T) T ∩ I) ≤
      (volume : Measure ℝ).restrict I :=
    Measure.restrict_mono (Set.inter_subset_right) le_rfl
  have hsubprod :
      ((volume : Measure ℝ).restrict (Set.Icc (-T) T ∩ I)).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) ≤
        ((volume : Measure ℝ).restrict I).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.prod_mono hsubtime le_rfl
  filter_upwards [ae_mono hsubprod heq] with p hp
  unfold zeroExtendForcing
  split_ifs with hs
  · rw [← hp]
  · simp

/-- `prop:zero-extension-jump`: zero Cauchy traces remove both boundary deltas. -/
theorem zero_extension_jump (σ : ℝ) (u v : GlobalSolution σ)
    (a b : ℝ) (hab : a < b)
    (hmod : SameModulusOnSet (Set.Ioo a b) u.u v.u) :
  IsWeakTwoParticleEquationOn (Set.Ioo a b)
    (zeroExtendNormal (measurableNormalExterior u v))
    (zeroExtendForcing (measurableRidgePotential σ u)
      (measurableNormalExterior u v)) := by
  intro Ψ hΨ hΨc hΨI
  let Φ : 𝓢(ℝ × (ℝ × ℝ), ℂ) := hΨc.toSchwartzMap hΨ
  have hΦeq : (Φ : ℝ × (ℝ × ℝ) → ℂ) = Ψ := rfl
  have hΦc : HasCompactSupport (Φ : ℝ × (ℝ × ℝ) → ℂ) := by
    rw [hΦeq]
    exact hΨc
  obtain ⟨A, B, hAB, hABI, hΦtime⟩ :=
    exists_compact_time_interval a b hab Ψ hΨc hΨI
  let P : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    -Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
      iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
      iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2
  let F : ℝ × (ℝ × ℝ) → ℂ := measurableNormalExterior u v
  let Q : ℝ × (ℝ × ℝ) → ℂ := measurableRidgePotential σ u
  have hbase := normal_exterior_weak_equation_on_sameModulus
    σ u v (Set.Ioo a b) isOpen_Ioo hmod Ψ hΨ hΨc hΨI
  have hFP : Integrable (fun p => F p * P p)
      (volume.prod (volume.prod volume)) := by
    simpa [F, P] using hbase.2.1
  have hQF : Integrable (fun p => (Q p * F p) * Ψ p)
      (volume.prod (volume.prod volume)) := by
    simpa [Q, F] using hbase.2.2.1
  have hboundary := normalBoundaryIntegral_tendsto_zero
    σ u v (Set.Ioo a b) isOpen_Ioo hmod Φ hΦc A B hAB hABI (by
      rw [hΦeq]
      exact hΦtime)
  have hboundary' : Tendsto (fun n : ℕ => ∫ p, F p *
        (2 * lowerHalfCutoffDeriv n p.2.1 *
            deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
          lowerHalfCutoffSecond n p.2.1 * Ψ p)
        ∂(volume.prod (volume.prod volume))) atTop (nhds 0) := by
    simpa [F, Φ, spacetimeNormalPartial_apply] using hboundary
  have hmain0 := lowerHalfCutoff_integral_tendsto (fun p => F p * P p) hFP
  have hmain : Tendsto (fun n : ℕ => ∫ p,
      F p * (lowerHalfCutoff n p.2.1 * P p)
      ∂(volume.prod (volume.prod volume))) atTop
      (nhds (∫ p, lowerHalfRestriction (fun q => F q * P q) p
        ∂(volume.prod (volume.prod volume)))) := by
    apply hmain0.congr'
    filter_upwards with n
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hright0 := lowerHalfCutoff_integral_tendsto
    (fun p => (Q p * F p) * Ψ p) hQF
  have hright : Tendsto (fun n : ℕ => ∫ p,
      (Q p * F p) * (lowerHalfCutoff n p.2.1 * Ψ p)
      ∂(volume.prod (volume.prod volume))) atTop
      (nhds (∫ p, lowerHalfRestriction (fun q => (Q q * F q) * Ψ q) p
        ∂(volume.prod (volume.prod volume)))) := by
    apply hright0.congr'
    filter_upwards with n
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hseqeq (n : ℕ) :
      (∫ p, F p * (lowerHalfCutoff n p.2.1 * P p)
          ∂(volume.prod (volume.prod volume))) +
        (∫ p, F p *
          (2 * lowerHalfCutoffDeriv n p.2.1 *
              deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
            lowerHalfCutoffSecond n p.2.1 * Ψ p)
          ∂(volume.prod (volume.prod volume))) =
        ∫ p, (Q p * F p) * (lowerHalfCutoff n p.2.1 * Ψ p)
          ∂(volume.prod (volume.prod volume)) := by
    have hn := normal_exterior_weak_equation_on_sameModulus
      σ u v (Set.Ioo a b) isOpen_Ioo hmod
      (lowerHalfCutoffTest n Ψ)
      (lowerHalfCutoffTest_contDiff n hΨ)
      (lowerHalfCutoffTest_hasCompactSupport n hΨc) (by
        intro p hp
        exact hΨI p (lowerHalfCutoffTest_tsupport_subset n Ψ hp))
    have hmainInt0 := lowerHalfCutoff_mul_integrable n hFP
    have hmainInt : Integrable (fun p =>
        F p * (lowerHalfCutoff n p.2.1 * P p))
        (volume.prod (volume.prod volume)) := by
      apply hmainInt0.congr
      filter_upwards with p
      ring
    have hadjInt : Integrable (fun p => F p *
        (lowerHalfCutoff n p.2.1 * P p +
          2 * lowerHalfCutoffDeriv n p.2.1 *
            deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
          lowerHalfCutoffSecond n p.2.1 * Ψ p))
        (volume.prod (volume.prod volume)) := by
      apply hn.2.1.congr
      filter_upwards with p
      congr 1
      exact lowerHalfCutoffTest_adjoint n Ψ hΨ p
    have hboundInt : Integrable (fun p => F p *
        (2 * lowerHalfCutoffDeriv n p.2.1 *
            deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
          lowerHalfCutoffSecond n p.2.1 * Ψ p))
        (volume.prod (volume.prod volume)) := by
      have hd := hadjInt.sub hmainInt
      apply hd.congr
      filter_upwards with p
      change F p *
          (lowerHalfCutoff n p.2.1 * P p +
            2 * lowerHalfCutoffDeriv n p.2.1 *
              deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
            lowerHalfCutoffSecond n p.2.1 * Ψ p) -
          F p * (lowerHalfCutoff n p.2.1 * P p) =
        F p *
          (2 * lowerHalfCutoffDeriv n p.2.1 *
              deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
            lowerHalfCutoffSecond n p.2.1 * Ψ p)
      ring
    calc
      _ = ∫ p, (F p * (lowerHalfCutoff n p.2.1 * P p)) +
          F p *
          (2 * lowerHalfCutoffDeriv n p.2.1 *
              deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
            lowerHalfCutoffSecond n p.2.1 * Ψ p)
          ∂(volume.prod (volume.prod volume)) := by
        symm
        simpa only [Pi.add_apply] using integral_add hmainInt hboundInt
      _ = ∫ p, F p *
          (lowerHalfCutoff n p.2.1 * P p +
            2 * lowerHalfCutoffDeriv n p.2.1 *
              deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
            lowerHalfCutoffSecond n p.2.1 * Ψ p)
          ∂(volume.prod (volume.prod volume)) := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = ∫ p, F p *
          (-Complex.I * deriv
              (fun t => lowerHalfCutoffTest n Ψ (t, p.2)) p.1 +
            iteratedDeriv 2
              (fun s => lowerHalfCutoffTest n Ψ (p.1, (s, p.2.2))) p.2.1 +
            iteratedDeriv 2
              (fun r => lowerHalfCutoffTest n Ψ (p.1, (p.2.1, r))) p.2.2)
          ∂(volume.prod (volume.prod volume)) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [lowerHalfCutoffTest_adjoint n Ψ hΨ p]
      _ = ∫ p, (Q p * F p) * lowerHalfCutoffTest n Ψ p
          ∂(volume.prod (volume.prod volume)) := by
        simpa [F, Q] using hn.2.2.2
      _ = _ := by rfl
  have hleft : Tendsto (fun n : ℕ =>
      (∫ p, F p * (lowerHalfCutoff n p.2.1 * P p)
          ∂(volume.prod (volume.prod volume))) +
        ∫ p, F p *
          (2 * lowerHalfCutoffDeriv n p.2.1 *
              deriv (fun s => Ψ (p.1, (s, p.2.2))) p.2.1 +
            lowerHalfCutoffSecond n p.2.1 * Ψ p)
          ∂(volume.prod (volume.prod volume))) atTop
      (nhds (∫ p, lowerHalfRestriction (fun q => F q * P q) p
        ∂(volume.prod (volume.prod volume)))) := by
    simpa using hmain.add hboundary'
  have hlim :
      (∫ p, lowerHalfRestriction (fun q => F q * P q) p
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, lowerHalfRestriction (fun q => (Q q * F q) * Ψ q) p
        ∂(volume.prod (volume.prod volume)) :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright
      (Filter.Eventually.of_forall hseqeq)
  have htestInt : Integrable (fun p =>
      zeroExtendNormal F p * Ψ p) (volume.prod (volume.prod volume)) := by
    have hFtest : Integrable (fun p => F p * Ψ p)
        (volume.prod (volume.prod volume)) := by
      simpa [F] using hbase.1
    apply (lowerHalfRestriction_integrable hFtest).congr
    filter_upwards with p
    by_cases hs : p.2.1 < 0 <;>
      simp [lowerHalfRestriction, zeroExtendNormal, hs]
  have hadjInt : Integrable (fun p =>
      zeroExtendNormal F p * P p) (volume.prod (volume.prod volume)) := by
    apply (lowerHalfRestriction_integrable hFP).congr
    filter_upwards with p
    by_cases hs : p.2.1 < 0 <;>
      simp [F, lowerHalfRestriction, zeroExtendNormal, hs]
  have hforceInt : Integrable (fun p =>
      zeroExtendForcing Q F p * Ψ p)
      (volume.prod (volume.prod volume)) := by
    apply (lowerHalfRestriction_integrable hQF).congr
    filter_upwards with p
    by_cases hs : p.2.1 < 0 <;>
      simp [F, Q, lowerHalfRestriction, zeroExtendForcing, hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [F] using htestInt
  · simpa [F, P] using hadjInt
  · simpa [F, Q] using hforceInt
  · calc
      (∫ p, zeroExtendNormal (measurableNormalExterior u v) p *
          (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
            iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
            iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2)
          ∂(volume.prod (volume.prod volume))) =
        ∫ p, lowerHalfRestriction (fun q => F q * P q) p
          ∂(volume.prod (volume.prod volume)) := by
            apply integral_congr_ae
            filter_upwards with p
            by_cases hs : p.2.1 < 0 <;>
              simp [F, P, lowerHalfRestriction, zeroExtendNormal, hs]
      _ = ∫ p, lowerHalfRestriction (fun q => (Q q * F q) * Ψ q) p
          ∂(volume.prod (volume.prod volume)) := hlim
      _ = ∫ p, zeroExtendForcing (measurableRidgePotential σ u)
          (measurableNormalExterior u v) p * Ψ p
          ∂(volume.prod (volume.prod volume)) := by
            apply integral_congr_ae
            filter_upwards with p
            by_cases hs : p.2.1 < 0 <;>
              simp [F, Q, lowerHalfRestriction, zeroExtendForcing, hs]

end CubicNLSPhaseRetrieval
