import Lean_Code.ScalarMixedNorms
import Lean_Code.FreeSchrodinger

/-!
# Definitions for one-dimensional Strichartz estimates

This small module separates the endpoint operator notation from the density
and completion arguments, preventing an import cycle between those proofs.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- One-dimensional Schrödinger admissibility. -/
def SchrodingerAdmissible (q r : ℝ≥0∞) : Prop :=
  2 ≤ q ∧ 2 ≤ r ∧ 2 * q⁻¹ + r⁻¹ = (2 : ℝ≥0∞)⁻¹

/-- Full `TT*` operator on an L²-valued test curve. -/
def ttStar (F : ℝ → L2) (t : ℝ) : L2 :=
  ∫ s : ℝ, freeProp (t - s) (F s)

/-- Adjoint time integral on an L²-valued test curve. -/
def tStar (F : ℝ → L2) : L2 :=
  ∫ s : ℝ, freeProp (-s) (F s)

/-- Scalar representative of an L²-valued curve. -/
def curveRepresentative (F : ℝ → L2) (p : ℝ × ℝ) : ℂ :=
  (F p.1 : ℝ → ℂ) p.2

end CubicNLSPhaseRetrieval
