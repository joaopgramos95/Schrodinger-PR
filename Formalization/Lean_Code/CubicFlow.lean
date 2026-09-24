import Lean_Code.Setup
import Lean_Code.FourierSobolev
import Lean_Code.Strichartz1D

/-!
# Global L² well-posedness

Blueprint chapter: `chap:wellposed` (module 5).
Imports: setup and modules 1 and 4.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The fixed-point norm `C_tL² ∩ L⁶_{t,x}` on a measurable time set. -/
def fixedPointNorm (I : Set ℝ) (u : ℝ → L2) : ℝ≥0∞ :=
  scalarMixedENorm (volume.restrict I) volume ⊤ 2 (curveRepresentative u) +
    scalarMixedENorm (volume.restrict I) volume 6 6 (curveRepresentative u)

/-- `def:fixed-point-space`: membership in the nonlinear fixed-point space. -/
def MemFixedPointSpace (I : Set ℝ) (u : ℝ → L2) : Prop :=
  ContinuousOn u I ∧ fixedPointNorm I u < ⊤

/-- Scalar cubic forcing of an L²-valued curve. -/
def cubicForcingFn (u : ℝ → L2) (p : ℝ × ℝ) : ℂ :=
  ((‖(u p.1 : ℝ → ℂ) p.2‖ ^ 2 : ℝ) : ℂ) * (u p.1 : ℝ → ℂ) p.2

/-- The algebraic fixed-point map for a chosen completed retarded operator. -/
def fixedPointMap (σ t0 : ℝ) (u0 : L2)
    (retarded : (ℝ × ℝ → ℂ) → ℝ → L2) (u : ℝ → L2) (t : ℝ) : L2 :=
  freeProp (t - t0) u0 - (Complex.I * (σ : ℂ)) • retarded (cubicForcingFn u) t

/-- `def:mild-solution`: Duhamel solution on a time set with an explicit L² forcing. -/
def IsMildSolutionOn (σ : ℝ) (I : Set ℝ) (u nonlin : ℝ → L2) : Prop :=
  ContinuousOn u I ∧
  (∀ᵐ t ∂(volume.restrict I),
    (nonlin t : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((‖(u t : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) * (u t : ℝ → ℂ) x) ∧
  ∀ t ∈ I, ∀ t0 ∈ I,
    IntervalIntegrable (fun s => freeProp (t - s) (nonlin s)) volume t0 t ∧
    u t = freeProp (t - t0) (u t0) -
      (Complex.I * (σ : ℂ)) • ∫ s in t0..t, freeProp (t - s) (nonlin s)

/-- Local solution package used by the LWP and persistence statements. -/
structure LocalSolution (σ : ℝ) (I : Set ℝ) where
  u : ℝ → L2
  nonlin : ℝ → L2
  memX : MemFixedPointSpace I u
  mild : IsMildSolutionOn σ I u nonlin

/-- Real derivative of the scalar cubic map. -/
def cubicDerivative (u w : ℂ) : ℂ :=
  ((2 * (starRingEnd ℂ u * w).re : ℝ) : ℂ) * u + ((‖u‖ ^ 2 : ℝ) : ℂ) * w

private theorem global_L2_mixed_lt_top (σ : ℝ) (u : GlobalSolution σ)
    (I : Set ℝ) (hI : IsCompact I) :
    scalarMixedENorm (volume.restrict I) volume ⊤ 2 (curveRepresentative u.u) < ⊤ := by
  have hcomp : IsCompact (u.u '' I) :=
    hI.image_of_continuousOn u.continuous.continuousOn
  obtain ⟨R, _hRpos, hR⟩ := hcomp.isBounded.subset_closedBall_lt 0 (0 : L2)
  let C : NNReal := Real.toNNReal R
  rw [scalarMixedENorm, eLpNorm_exponent_top]
  apply eLpNormEssSup_lt_top_of_ae_enorm_bound (C := C)
  filter_upwards [ae_restrict_mem hI.measurableSet] with t ht
  have hut : u.u t ∈ Metric.closedBall (0 : L2) R := hR ⟨t, ht, rfl⟩
  have hnorm : ‖u.u t‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hut
  change ‖eLpNorm (⇑(u.u t)) 2 volume‖ₑ ≤ ↑C
  rw [enorm_eq_self, ← Lp.enorm_def]
  simpa only [C, ofReal_norm, ENNReal.ofNNReal_toNNReal] using
    ENNReal.ofReal_le_ofReal hnorm

private theorem global_L6_mixed_lt_top (σ : ℝ) (u : GlobalSolution σ)
    (I : Set ℝ) (hI : IsCompact I) :
    scalarMixedENorm (volume.restrict I) volume 6 6 (curveRepresentative u.u) < ⊤ := by
  obtain ⟨T, _hTpos, hT⟩ := hI.isBounded.subset_closedBall_lt 0 0
  have hsub : I ⊆ Set.Icc (-T) T := by
    intro t ht
    have hdist := hT ht
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hdist
    exact abs_le.mp hdist
  rw [scalarMixedENorm]
  change eLpNorm (fun t => eLpNorm (⇑(u.u t)) 6 volume) 6 (volume.restrict I) < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num [curveRepresentative, enorm_eq_self]
  have hle :
      (∫⁻ t in I, (eLpNorm (⇑(u.u t)) 6 volume) ^ 6 ∂volume) ≤
        ∫⁻ t in Set.Icc (-T) T, (eLpNorm (⇑(u.u t)) 6 volume) ^ 6 ∂volume :=
    lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (hle.trans_lt (u.memL6_loc T)).ne

/-- A global mild solution restricted to a compact time set is a local solution. -/
def GlobalSolution.toLocalSolution (σ : ℝ) (u : GlobalSolution σ)
    (I : Set ℝ) (hI : IsCompact I) : LocalSolution σ I where
  u := u.u
  nonlin := u.nonlin
  memX := by
    refine ⟨u.continuous.continuousOn, ?_⟩
    rw [fixedPointNorm]
    exact ENNReal.add_lt_top.2
      ⟨global_L2_mixed_lt_top σ u I hI, global_L6_mixed_lt_top σ u I hI⟩
  mild := by
    refine ⟨u.continuous.continuousOn, ae_restrict_of_ae u.nonlin_eq, ?_⟩
    intro t _ht t0 _ht0
    exact ⟨u.forcing_integrable t0 t, u.mild t t0⟩

end CubicNLSPhaseRetrieval
