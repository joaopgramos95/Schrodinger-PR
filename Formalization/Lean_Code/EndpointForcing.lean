import Lean_Code.Setup

/-!
# Bochner integrability of the cubic forcing

This small module isolates the representative-free part of the endpoint
argument so that the larger endpoint estimates can be compiled in separate
artifacts.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Applying the inverse free propagator cancels the propagated forcing. -/
theorem freeProp_cancel_difference (b s : ℝ) (f : L2) :
    freeProp (s - b) (freeProp (b - s) f) = f := by
  rw [propagator_unitary.2.1]
  convert propagator_unitary.2.2.1 f using 2
  ring

set_option maxHeartbeats 1000000 in
/-- Joint continuity turns two measurable component curves into a measurable
curve under the free propagator. -/
theorem freeProp_comp_aestronglyMeasurable {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (a : X → ℝ) (g : X → L2)
    (ha : AEStronglyMeasurable a mu) (hg : AEStronglyMeasurable g mu) :
    AEStronglyMeasurable (fun x => freeProp (a x) (g x)) mu := by
  have hp : AEStronglyMeasurable (fun x => (a x, g x)) mu := ha.prodMk hg
  exact Continuous.comp_aestronglyMeasurable
    (f := fun x => (a x, g x))
    (g := fun p : ℝ × L2 => freeProp p.1 p.2)
    continuous_freeProp_joint hp

/-- Measurability of the nonlinear curve, recovered from the measurable
propagated curve in the mild-solution interface. -/
theorem endpoint_nonlin_aestronglyMeasurable_Icc (σ : ℝ)
    (u : GlobalSolution σ) (a b : ℝ) (hab : a ≤ b) :
    AEStronglyMeasurable u.nonlin (volume.restrict (Set.Icc a b)) := by
  let g : ℝ → L2 := fun s => freeProp (b - s) (u.nonlin s)
  have hg : IntegrableOn g (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (u.forcing_integrable a b)
  have ha : AEStronglyMeasurable (fun s : ℝ => s - b)
      (volume.restrict (Set.Icc a b)) :=
    (continuous_id.sub continuous_const).aestronglyMeasurable
  have hinv : AEStronglyMeasurable (fun s => freeProp (s - b) (g s))
      (volume.restrict (Set.Icc a b)) :=
    freeProp_comp_aestronglyMeasurable _ _ _ ha hg.1
  exact hinv.congr (Filter.Eventually.of_forall fun s => by
    exact freeProp_cancel_difference b s (u.nonlin s))

/-- The explicit nonlinear `L²` curve is Bochner-integrable on compact time
intervals. -/
theorem endpoint_nonlin_integrableOn_Icc (σ : ℝ) (u : GlobalSolution σ)
    (a b : ℝ) (hab : a ≤ b) : IntegrableOn u.nonlin (Set.Icc a b) := by
  let g : ℝ → L2 := fun s => freeProp (b - s) (u.nonlin s)
  have hg : IntegrableOn g (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (u.forcing_integrable a b)
  change Integrable u.nonlin (volume.restrict (Set.Icc a b))
  change Integrable g (volume.restrict (Set.Icc a b)) at hg
  exact MeasureTheory.Integrable.mono hg
    (endpoint_nonlin_aestronglyMeasurable_Icc σ u a b hab)
    (Filter.Eventually.of_forall fun s => by
      change ‖u.nonlin s‖ ≤ ‖g s‖
      dsimp only [g]
      rw [norm_freeProp])

end CubicNLSPhaseRetrieval
