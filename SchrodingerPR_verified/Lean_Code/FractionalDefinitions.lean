import Lean_Code.FreeSchrodinger
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# Basic definitions for fractional integration

These definitions are separated from the maximal-function and Hedberg proofs so
that the two proof modules can be checked independently.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- `def:maximal-function`: centered Hardy–Littlewood maximal function on `ℝ`. -/
def centeredMaximal (F : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R},
    ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
      ∫⁻ s in Set.Icc (t - R) (t + R), ‖F s‖₊ ∂volume

/-- Positive fractional integral with kernel `|t-s|^{-α}`. -/
def fractionalIntegral (α : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ENNReal.ofReal (|t - s| ^ (-α)) * ‖F s‖₊

end CubicNLSPhaseRetrieval
