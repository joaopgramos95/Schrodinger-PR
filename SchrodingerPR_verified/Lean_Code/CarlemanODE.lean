import Mathlib

/-!
# Scalar selected-branch ODE estimates for the Carleman argument

These lemmas isolate the one-dimensional integrating-factor calculation used
after taking the spatial Fourier transform of the conjugated Schrödinger
equation.  The sign of the real part determines which time endpoint supplies
the zero boundary value.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

private def odeIntegratingFactor (lam : ℂ) (y : ℝ → ℂ) (s : ℝ) : ℂ :=
  Complex.exp (-lam * (s : ℂ)) * y s

private lemma hasDerivAt_odeIntegratingFactor (lam : ℂ) (y g : ℝ → ℂ)
    (hy : ContDiff ℝ 1 y) (heq : ∀ s, deriv y s = lam * y s + g s) (s : ℝ) :
    HasDerivAt (odeIntegratingFactor lam y)
      (Complex.exp (-lam * (s : ℂ)) * g s) s := by
  have hlin : HasDerivAt (fun r : ℝ => -lam * (r : ℂ)) (-lam) s := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using!
      (hasDerivAt_id s).ofReal_comp.const_mul (-lam)
  have hexp := hlin.cexp
  have hy' : HasDerivAt y (deriv y s) s :=
    (hy.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) s).hasDerivAt
  have hmul := HasDerivAt.mul (𝕜 := ℝ) hexp hy'
  have hmul' : HasDerivAt
      (fun r : ℝ => Complex.exp (-lam * (r : ℂ)) * y r)
      (Complex.exp (-lam * (s : ℂ)) * -lam * y s +
        Complex.exp (-lam * (s : ℂ)) * deriv y s) s := by
    simpa only [Pi.mul_apply] using! hmul
  apply hmul'.congr_deriv
  rw [heq s]
  ring

private lemma ode_integrating_factor_interval (lam : ℂ) (y g : ℝ → ℂ)
    (hy : ContDiff ℝ 1 y) (hg : Continuous g)
    (heq : ∀ s, deriv y s = lam * y s + g s) (a b : ℝ) :
    (∫ s in a..b, Complex.exp (-lam * (s : ℂ)) * g s) =
      odeIntegratingFactor lam y b - odeIntegratingFactor lam y a := by
  have hdiff : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt ℝ (odeIntegratingFactor lam y) s := by
    intro s hs
    exact (hasDerivAt_odeIntegratingFactor lam y g hy heq s).differentiableAt
  have hderiv : deriv (odeIntegratingFactor lam y) =
      fun s : ℝ => Complex.exp (-lam * (s : ℂ)) * g s := by
    funext s
    exact (hasDerivAt_odeIntegratingFactor lam y g hy heq s).deriv
  have hint : IntervalIntegrable (deriv (odeIntegratingFactor lam y)) volume a b := by
    rw [hderiv]
    exact (by fun_prop : Continuous
      (fun s : ℝ => Complex.exp (-lam * (s : ℂ)) * g s)).intervalIntegrable _ _
  rw [← hderiv]
  exact intervalIntegral.integral_deriv_eq_sub hdiff hint

/-- Forward selected-branch representation when the left endpoint vanishes. -/
theorem firstOrderODE_forward_formula (lam : ℂ) (y g : ℝ → ℂ)
    (hy : ContDiff ℝ 1 y) (hg : Continuous g)
    (heq : ∀ s, deriv y s = lam * y s + g s) (a t : ℝ)
    (hya : y a = 0) :
    y t = ∫ s in a..t, Complex.exp (lam * ((t - s : ℝ) : ℂ)) * g s := by
  have hid := ode_integrating_factor_interval lam y g hy hg heq a t
  rw [show odeIntegratingFactor lam y a = 0 by simp [odeIntegratingFactor, hya],
    sub_zero] at hid
  calc
    y t = Complex.exp (lam * (t : ℂ)) * odeIntegratingFactor lam y t := by
      simp only [odeIntegratingFactor]
      rw [← mul_assoc, ← Complex.exp_add]
      ring_nf
      simp
    _ = Complex.exp (lam * (t : ℂ)) *
        (∫ s in a..t, Complex.exp (-lam * (s : ℂ)) * g s) := by rw [hid]
    _ = ∫ s in a..t, Complex.exp (lam * (t : ℂ)) *
        (Complex.exp (-lam * (s : ℂ)) * g s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in a..t, Complex.exp (lam * ((t - s : ℝ) : ℂ)) * g s := by
      apply intervalIntegral.integral_congr
      intro s hs
      change Complex.exp (lam * (t : ℂ)) *
          (Complex.exp (-lam * (s : ℂ)) * g s) =
        Complex.exp (lam * ((t - s : ℝ) : ℂ)) * g s
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- Forward damping estimate for a coefficient with nonpositive real part. -/
theorem firstOrderODE_forward_estimate (lam : ℂ) (y g : ℝ → ℂ)
    (hy : ContDiff ℝ 1 y) (hg : Continuous g)
    (heq : ∀ s, deriv y s = lam * y s + g s) (a t : ℝ)
    (hat : a ≤ t) (hya : y a = 0) (hlam : lam.re ≤ 0) :
    ‖y t‖ ≤ ∫ s in a..t, ‖g s‖ := by
  rw [firstOrderODE_forward_formula lam y g hy hg heq a t hya]
  apply intervalIntegral.norm_integral_le_of_norm_le hat
  · filter_upwards with s hst
    rw [norm_mul, Complex.norm_exp]
    have hnonneg : 0 ≤ t - s := sub_nonneg.mpr hst.2
    have hre : (lam * ((t - s : ℝ) : ℂ)).re = lam.re * (t - s) := by simp
    have hexp : Real.exp (lam * ((t - s : ℝ) : ℂ)).re ≤ 1 := by
      rw [hre, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg hlam hnonneg
    exact mul_le_of_le_one_left (norm_nonneg _) hexp
  · exact hg.norm.intervalIntegrable _ _

/-- Backward selected-branch representation when the right endpoint vanishes. -/
theorem firstOrderODE_backward_formula (lam : ℂ) (y g : ℝ → ℂ)
    (hy : ContDiff ℝ 1 y) (hg : Continuous g)
    (heq : ∀ s, deriv y s = lam * y s + g s) (t b : ℝ)
    (hyb : y b = 0) :
    y t = -(∫ s in t..b, Complex.exp (lam * ((t - s : ℝ) : ℂ)) * g s) := by
  have hid := ode_integrating_factor_interval lam y g hy hg heq t b
  rw [show odeIntegratingFactor lam y b = 0 by simp [odeIntegratingFactor, hyb],
    zero_sub] at hid
  have hfactor : odeIntegratingFactor lam y t =
      -(∫ s in t..b, Complex.exp (-lam * (s : ℂ)) * g s) := by
    rw [hid]
    simp
  calc
    y t = Complex.exp (lam * (t : ℂ)) * odeIntegratingFactor lam y t := by
      simp only [odeIntegratingFactor]
      rw [← mul_assoc, ← Complex.exp_add]
      ring_nf
      simp
    _ = - (Complex.exp (lam * (t : ℂ)) *
        (∫ s in t..b, Complex.exp (-lam * (s : ℂ)) * g s)) := by
      rw [hfactor]
      ring
    _ = -(∫ s in t..b, Complex.exp (lam * (t : ℂ)) *
        (Complex.exp (-lam * (s : ℂ)) * g s)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = -(∫ s in t..b, Complex.exp (lam * ((t - s : ℝ) : ℂ)) * g s) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      change Complex.exp (lam * (t : ℂ)) *
          (Complex.exp (-lam * (s : ℂ)) * g s) =
        Complex.exp (lam * ((t - s : ℝ) : ℂ)) * g s
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- Backward damping estimate for a coefficient with nonnegative real part. -/
theorem firstOrderODE_backward_estimate (lam : ℂ) (y g : ℝ → ℂ)
    (hy : ContDiff ℝ 1 y) (hg : Continuous g)
    (heq : ∀ s, deriv y s = lam * y s + g s) (t b : ℝ)
    (htb : t ≤ b) (hyb : y b = 0) (hlam : 0 ≤ lam.re) :
    ‖y t‖ ≤ ∫ s in t..b, ‖g s‖ := by
  rw [firstOrderODE_backward_formula lam y g hy hg heq t b hyb, norm_neg]
  apply intervalIntegral.norm_integral_le_of_norm_le htb
  · filter_upwards with s hst
    rw [norm_mul, Complex.norm_exp]
    have hnonpos : t - s ≤ 0 := sub_nonpos.mpr hst.1.le
    have hre : (lam * ((t - s : ℝ) : ℂ)).re = lam.re * (t - s) := by simp
    have hexp : Real.exp (lam * ((t - s : ℝ) : ℂ)).re ≤ 1 := by
      rw [hre, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos hlam hnonpos
    exact mul_le_of_le_one_left (norm_nonneg _) hexp
  · exact hg.norm.intervalIntegrable _ _

end CubicNLSPhaseRetrieval
