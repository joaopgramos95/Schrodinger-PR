import Lean_Code.CurrentRecovery
import Lean_Code.RegularizedLocalSmoothing

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology ComplexConjugate

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- A compactly supported Schwartz test admits a Schwartz cutoff which is
identically one on a neighborhood of its support. -/
lemma exists_schwartz_cutoff_for_test (φ : SchwartzMap ℝ ℂ)
    (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    ∃ χ : SchwartzMap ℝ ℂ,
      HasCompactSupport (χ : ℝ → ℂ) ∧
      ∀ x : ℝ, φ x ≠ 0 →
        χ x = 1 ∧ deriv (χ : ℝ → ℂ) x = 0 := by
  obtain ⟨R, hR⟩ := hφ.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let L : ℝ := |R| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  let b : ContDiffBump (0 : ℝ) := ⟨L, L + 1, hL, by linarith⟩
  let χfun : ℝ → ℂ := fun x => (b x : ℂ)
  have hχc : HasCompactSupport χfun := by
    have hb := b.hasCompactSupport.comp_left
      (g := fun x : ℝ => (x : ℂ)) (by norm_num)
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ (b : ℝ → ℝ))
    exact hb
  have hχd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χfun :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let χ : SchwartzMap ℝ ℂ := hχc.toSchwartzMap hχd
  refine ⟨χ, hχc, ?_⟩
  intro x hx
  have hxt : x ∈ tsupport (φ : ℝ → ℂ) := subset_tsupport _ hx
  have hxball := hR hxt
  have hxR : |x| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using hxball
  have hxL : |x| < L := by
    dsimp [L]
    exact lt_of_le_of_lt (hxR.trans (le_abs_self R)) (lt_add_one |R|)
  have hxmem : x ∈ Metric.ball (0 : ℝ) b.rIn := by
    simpa [Metric.mem_ball, Real.dist_0_eq_abs, b] using hxL
  have heq : (b : ℝ → ℝ) =ᶠ[nhds x] (1 : ℝ → ℝ) :=
    b.eventuallyEq_one_of_mem_ball hxmem
  have heqC : χfun =ᶠ[nhds x] (1 : ℝ → ℂ) := by
    filter_upwards [heq] with y hy
    change ((b y : ℝ) : ℂ) = 1
    rw [hy]
    norm_num
  have hχx : χ x = 1 := by
    change χfun x = 1
    exact heqC.eq_of_nhds
  have hdχ : deriv (χ : ℝ → ℂ) x = 0 := by
    change deriv χfun x = 0
    rw [heqC.deriv_eq]
    exact (hasDerivAt_const x (1 : ℂ)).deriv
  exact ⟨hχx, hdχ⟩

lemma regularizedForwardCurrent_eq_integral (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) :
    regularizedForwardCurrent n f φ =
      ∫ x : ℝ, (frequencySmoothDerivativeCLM n f : ℝ → ℂ) x *
        φ x * conj ((frequencySmoothCLM n f : ℝ → ℂ) x) := by
  rw [regularizedForwardCurrent, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Complex.conjLIE.toContinuousLinearMap.coeFn_compLpL
      (frequencySmoothDerivativeCLM n f),
    Complex.conjLIE.toContinuousLinearMap.coeFn_compLpL
      (frequencySmoothCLM n f),
    coe_cutoffL2CLM φ (conjL2 (frequencySmoothCLM n f))]
      with x hd hw hcut
  rw [conjL2, hd, hcut, conjL2, hw]
  simp only [RCLike.inner_apply]
  change φ x * conj ((frequencySmoothCLM n f : ℝ → ℂ) x) *
      conj (conj ((frequencySmoothDerivativeCLM n f : ℝ → ℂ) x)) = _
  rw [show conj (conj ((frequencySmoothDerivativeCLM n f : ℝ → ℂ) x)) =
    (frequencySmoothDerivativeCLM n f : ℝ → ℂ) x by simp]
  ring

private lemma coe_cutoffDerivativeL2 (χ : SchwartzMap ℝ ℂ) (w q : L2) :
    (cutoffDerivativeL2 χ w q : ℝ → ℂ) =ᵐ[volume]
      fun x => χ x * (q : ℝ → ℂ) x +
        (SchwartzMap.derivCLM ℂ ℂ χ) x * (w : ℝ → ℂ) x := by
  filter_upwards [Lp.coeFn_add (cutoffL2CLM χ q)
      (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ χ) w),
    coe_cutoffL2CLM χ q,
    coe_cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ χ) w]
      with x hadd hq hw
  rw [cutoffDerivativeL2, hadd]
  simp only [Pi.add_apply]
  rw [hq, hw]

/-- A critical localization of a resolvent-smoothed function has exactly the
classical regularized current on tests supported where the cutoff is one. -/
theorem criticalQuadraticCurrent_localized_frequencySmooth
    (n : ℕ) (f : L2) (χ φ : SchwartzMap ℝ ℂ)
    (hχ : ∀ x : ℝ, φ x ≠ 0 →
      χ x = 1 ∧ deriv (χ : ℝ → ℂ) x = 0)
    (h : Hs (1 / 2 : ℝ))
    (hreal : Hs.toL2 (by norm_num) h =
      cutoffL2CLM χ (frequencySmoothCLM n f)) :
    criticalQuadraticCurrent h φ = regularizedForwardCurrent n f φ := by
  have hder := criticalDerivative_localized_frequencySmooth n f χ h hreal
  rw [criticalQuadraticCurrent, hder]
  change hsNegPairing
      (hsNegOfL2 (cutoffDerivativeL2 χ (frequencySmoothCLM n f)
        (frequencySmoothDerivativeCLM n f)))
      (schwartzHsMultiplier φ (criticalConj h)) = _
  rw [hsNegPairing_hsNegOfL2, regularizedForwardCurrent_eq_integral]
  have hq := coe_cutoffDerivativeL2 χ (frequencySmoothCLM n f)
    (frequencySmoothDerivativeCLM n f)
  have hm := schwartzHsMultiplier_toL2_ae φ (criticalConj h)
  have hc := criticalConj_toL2_ae h
  have hrealPoint :
      (Hs.toL2 (by norm_num) h : ℝ → ℂ) =ᵐ[volume]
        (cutoffL2CLM χ (frequencySmoothCLM n f) : ℝ → ℂ) :=
    Filter.Eventually.of_forall fun x => congrArg
      (fun z : L2 => (z : ℝ → ℂ) x) hreal
  have hw := coe_cutoffL2CLM χ (frequencySmoothCLM n f)
  apply integral_congr_ae
  filter_upwards [hq, hm, hc, hrealPoint, hw]
      with x hq hm hc hrealPoint hw
  rw [hq, hm, hc, hrealPoint, hw]
  by_cases hφx : φ x = 0
  · simp [hφx]
  · obtain ⟨hχx, hdχx⟩ := hχ x hφx
    have hdχx' : (SchwartzMap.derivCLM ℂ ℂ χ) x = 0 := by
      change deriv (χ : ℝ → ℂ) x = 0
      exact hdχx
    rw [hχx, hdχx']
    simp only [one_mul, zero_mul, zero_add, map_mul, map_one]
    ring

end CubicNLSPhaseRetrieval
