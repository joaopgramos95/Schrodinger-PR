import Lean_Code.ScalarMixedNorms
import Lean_Code.FourierSobolev

/-!
# Distributional utilities

Blueprint chapter: `chap:utilities` (module 12, built early).
Imports: modules 0 and 1 (`ScalarMixedNorms`, `FourierSobolev`).

`lem:distributional-products` is made generic during scaffolding so this early module
does not import the later exterior-product module; see `Blueprint_order.md`.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Raw separated finite sum used by `lem:tensor-test-density`. -/
def separatedTestSum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (terms : List (𝓢(E, ℂ) × 𝓢(F, ℂ))) (p : E × F) : ℂ :=
  (terms.map fun term => term.1 p.1 * term.2 p.2).sum

/-- Sup norm of a real-line Schwartz test. -/
def testSupNorm (φ : 𝓢(ℝ, ℂ)) : ℝ := ⨆ x : ℝ, ‖φ x‖₊

/-- Derivative sup norm of a real-line Schwartz test. -/
def testDerivSupNorm (φ : 𝓢(ℝ, ℂ)) : ℝ := ⨆ x : ℝ, ‖deriv (φ : ℝ → ℂ) x‖₊

end CubicNLSPhaseRetrieval
