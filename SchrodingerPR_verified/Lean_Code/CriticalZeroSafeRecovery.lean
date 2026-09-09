import Lean_Code.CriticalAdmissibleApproximation
import Lean_Code.CommonCurrent

/-!
# Recovering the critical zero-safe Wronskian

This file supplies pointwise bounded measurable representatives for bounded
critical functions and applies compact mollification to the reciprocal tests
in the zero-safe Wronskian argument.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology ComplexConjugate Pointwise

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- The real essential-supremum bound attached to a bounded critical element. -/
def boundedCriticalRepBound (f : BoundedCritical) : ℝ :=
  lpNorm (f.toL2 : ℝ → ℂ) ∞ volume

private def boundedCriticalMeasurableRep (f : BoundedCritical) : ℝ → ℂ :=
  (Lp.aestronglyMeasurable f.toL2).mk (f.toL2 : ℝ → ℂ)

/-- A measurable representative trimmed on the null exceptional set, so its
essential bound becomes a literal pointwise bound. -/
def boundedCriticalRepresentative (f : BoundedCritical) (x : ℝ) : ℂ :=
  if ‖boundedCriticalMeasurableRep f x‖ ≤ boundedCriticalRepBound f then
    boundedCriticalMeasurableRep f x else 0

lemma boundedCriticalRepBound_nonneg (f : BoundedCritical) :
    0 ≤ boundedCriticalRepBound f := lpNorm_nonneg

private lemma boundedCriticalMeasurableRep_measurable (f : BoundedCritical) :
    Measurable (boundedCriticalMeasurableRep f) := by
  unfold boundedCriticalMeasurableRep
  exact (Lp.aestronglyMeasurable f.toL2).stronglyMeasurable_mk.measurable

lemma boundedCriticalRepresentative_measurable (f : BoundedCritical) :
    Measurable (boundedCriticalRepresentative f) := by
  unfold boundedCriticalRepresentative
  apply Measurable.ite
  · exact measurableSet_le
      (boundedCriticalMeasurableRep_measurable f).norm measurable_const
  · exact boundedCriticalMeasurableRep_measurable f
  · exact measurable_const

lemma boundedCriticalRepresentative_norm_le (f : BoundedCritical) (x : ℝ) :
    ‖boundedCriticalRepresentative f x‖ ≤ boundedCriticalRepBound f := by
  unfold boundedCriticalRepresentative
  split_ifs with h
  · exact h
  · simpa using boundedCriticalRepBound_nonneg f

lemma boundedCriticalRepresentative_ae (f : BoundedCritical) :
    boundedCriticalRepresentative f =ᵐ[volume] (f.toL2 : ℝ → ℂ) := by
  let hfTop : MemLp (f.toL2 : ℝ → ℂ) ∞ volume :=
    ⟨Lp.aestronglyMeasurable f.toL2, f.bounded⟩
  filter_upwards [(Lp.aestronglyMeasurable f.toL2).ae_eq_mk,
    ae_le_lpNorm_exponent_top hfTop] with x hx hbound
  unfold boundedCriticalRepresentative boundedCriticalMeasurableRep
  rw [← hx]
  simp [boundedCriticalRepBound, hbound]

/-- Compact measurable representative of a Schwartz coefficient times a
bounded critical coefficient. -/
def compactCoefficientRep (φ : SchwartzMap ℝ ℂ) (a : BoundedCritical)
    (x : ℝ) : ℂ := φ x * boundedCriticalRepresentative a x

lemma compactCoefficientRep_measurable (φ : SchwartzMap ℝ ℂ)
    (a : BoundedCritical) : Measurable (compactCoefficientRep φ a) :=
  φ.continuous.measurable.mul (boundedCriticalRepresentative_measurable a)

lemma compactCoefficientRep_hasCompactSupport (φ : SchwartzMap ℝ ℂ)
    (hφ : HasCompactSupport (φ : ℝ → ℂ)) (a : BoundedCritical) :
    HasCompactSupport (compactCoefficientRep φ a) := by
  exact hφ.mul_right

lemma compactCoefficientRep_ae (φ : SchwartzMap ℝ ℂ)
    (a : BoundedCritical) :
    compactCoefficientRep φ a =ᵐ[volume]
      (((schwartzBoundedCritical φ).mul a).toL2 : ℝ → ℂ) := by
  filter_upwards [boundedCriticalRepresentative_ae a,
    BoundedCritical.mul_toL2_ae (schwartzBoundedCritical φ) a,
    schwartzBoundedCritical_toL2_ae φ] with x ha hout hφ
  rw [compactCoefficientRep, ha, hout, hφ]

lemma compactCoefficientRep_norm_le (φ : SchwartzMap ℝ ℂ)
    (a : BoundedCritical) (x : ℝ) :
    ‖compactCoefficientRep φ a x‖ ≤
      SchwartzMap.seminorm ℂ 0 0 φ * boundedCriticalRepBound a := by
  rw [compactCoefficientRep, norm_mul]
  apply mul_le_mul
  · simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 0 x
  · exact boundedCriticalRepresentative_norm_le a x
  · exact norm_nonneg _
  · exact apply_nonneg (SchwartzMap.seminorm ℂ 0 0) φ

/-- A Schwartz cutoff flat on the unit enlargement of a compact test's
support. -/
lemma exists_flat_cutoff_on_enlarged_tsupport (φ : SchwartzMap ℝ ℂ)
    (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    ∃ chi : SchwartzMap ℝ ℂ,
      HasCompactSupport (chi : ℝ → ℂ) ∧
      ∀ x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport (φ : ℝ → ℂ),
        chi x = 1 ∧ deriv (chi : ℝ → ℂ) x = 0 := by
  let K : Set ℝ := Metric.closedBall (0 : ℝ) 1 + tsupport (φ : ℝ → ℂ)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) 1).add hφ.isCompact
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  let L : ℝ := |R| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  let b : ContDiffBump (0 : ℝ) := ⟨L, L + 1, hL, by linarith⟩
  let chifun : ℝ → ℂ := fun x => (b x : ℂ)
  have hchic : HasCompactSupport chifun := by
    have hb := b.hasCompactSupport.comp_left
      (g := fun x : ℝ => (x : ℂ)) (by norm_num)
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ (b : ℝ → ℝ))
    exact hb
  have hchid : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chifun :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let chi : SchwartzMap ℝ ℂ := hchic.toSchwartzMap hchid
  refine ⟨chi, hchic, ?_⟩
  intro x hx
  have hxball := hR hx
  have hxR : |x| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using hxball
  have hxL : |x| < L := by
    dsimp [L]
    exact lt_of_le_of_lt (hxR.trans (le_abs_self R)) (lt_add_one |R|)
  have hxmem : x ∈ Metric.ball (0 : ℝ) b.rIn := by
    simpa [Metric.mem_ball, Real.dist_0_eq_abs, b] using hxL
  have heq : (b : ℝ → ℝ) =ᶠ[nhds x] (1 : ℝ → ℝ) :=
    b.eventuallyEq_one_of_mem_ball hxmem
  have heqC : chifun =ᶠ[nhds x] (1 : ℝ → ℂ) := by
    filter_upwards [heq] with y hy
    change ((b y : ℝ) : ℂ) = 1
    rw [hy]
    norm_num
  have hchix : chi x = 1 := by
    change chifun x = 1
    exact heqC.eq_of_nhds
  have hdchi : deriv (chi : ℝ → ℂ) x = 0 := by
    change deriv chifun x = 0
    rw [heqC.deriv_eq]
    exact (hasDerivAt_const x (1 : ℂ)).deriv
  exact ⟨hchix, hdchi⟩

set_option maxHeartbeats 1000000 in
/-- Smooth current recovery on one flat cutoff implies the zero-safe
Wronskian identity for the compact test. -/
theorem criticalWronskian_zero_of_smooth_current
    (chi φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hflat : ∀ x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport (φ : ℝ → ℂ),
      chi x = 1 ∧ deriv (chi : ℝ → ℂ) x = 0)
    (f g : BoundedCritical)
    (hmod : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖)
    (hsmooth : ∀ ψ : SchwartzMap ℝ ℂ, IsAdmissibleCurrentTest chi ψ →
      criticalQuadraticCurrent f.val ψ = criticalQuadraticCurrent g.val ψ) :
    criticalWronskianCurrent f.val g.val φ = 0 := by
  apply boundedWronskian_zero_of_zeroSafe_current_eq f g hmod φ
  intro n
  let z : BoundedCritical := f.zeroSafeMultiplier g n
  let a : BoundedCritical := (schwartzBoundedCritical φ).mul z
  let A : ℝ → ℂ := compactCoefficientRep φ z
  let M : ℝ := SchwartzMap.seminorm ℂ 0 0 φ * boundedCriticalRepBound z
  have hM : 0 ≤ M := mul_nonneg (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) φ)
    (boundedCriticalRepBound_nonneg z)
  have hAc : HasCompactSupport A := compactCoefficientRep_hasCompactSupport φ hφ z
  have hArep : A =ᵐ[volume] (a.toL2 : ℝ → ℂ) := compactCoefficientRep_ae φ z
  have hAsupp : tsupport A ⊆ tsupport (φ : ℝ → ℂ) := by
    apply closure_minimal
    · intro x hx
      apply subset_tsupport
      show φ x ≠ 0
      intro hφx
      apply hx
      simp [A, compactCoefficientRep, hφx]
    · exact isClosed_tsupport _
  have hflatA : ∀ x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport A,
      chi x = 1 ∧ deriv (chi : ℝ → ℂ) x = 0 := by
    intro x hx
    apply hflat x
    exact (add_subset_add Subset.rfl hAsupp) hx
  have happ : IsSimultaneousCurrentApproximation chi f g a :=
    simultaneousCurrentApproximation_of_compactRep chi f g a A
      (compactCoefficientRep_measurable φ z) hAc M hM
      (compactCoefficientRep_norm_le φ z) hArep hflatA
  exact boundedQuadraticCurrentAgainst_eq_of_approximation chi f g a hsmooth happ

/-- On one compact time interval, the localized NLS slices have vanishing
critical Wronskian against every compact test on whose unit support
enlargement the localization cutoff is flat. -/
theorem localizedCriticalWronskian_common_ae
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (chi : SchwartzMap ℝ ℂ) {A B : ℝ} (hAB : A < B)
    (hABI : Set.Icc A B ⊆ I) :
    ∀ᵐ t : ℝ ∂timeMeasure A B,
      ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport (φ : ℝ → ℂ) →
        (∀ x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport (φ : ℝ → ℂ),
          chi x = 1 ∧ deriv (chi : ℝ → ℂ) x = 0) →
        criticalWronskianCurrent
          ((localizedSolutionHsCurve chi σ u A B hAB.le :
            ℝ → Hs (1 / 2 : ℝ)) t)
          ((localizedSolutionHsCurve chi σ v A B hAB.le :
            ℝ → Hs (1 / 2 : ℝ)) t) φ = 0 := by
  filter_upwards [localizedCriticalCurrent_common_ae
      σ u v I hI hmod chi hAB hABI] with t ht
  rcases ht with ⟨f, g, hf, hg, hfL2, hgL2, hfgmod, hcur⟩
  intro φ hφ hflat
  have hw := criticalWronskian_zero_of_smooth_current
    chi φ hφ hflat f g hfgmod hcur
  simpa only [hf, hg] using hw

end CubicNLSPhaseRetrieval
