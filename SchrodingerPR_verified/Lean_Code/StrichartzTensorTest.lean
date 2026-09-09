import Lean_Code.StrichartzDuality
import Lean_Code.StrichartzDefinitions

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 3000000

namespace CubicNLSPhaseRetrieval

lemma inner_tensorAdjoint_eq_pairing {n : ℕ}
    (a b : Fin n → SchwartzMap ℝ ℂ) (f : L2) :
    @inner ℂ L2 _ (tensorAdjoint a b) f =
      ∫ t : ℝ, ∫ x : ℝ,
        tensorRaw a b (t, x) * curveRepresentative (fun s => freeProp s f) (t, x) := by
  rw [tensorAdjoint, inner_integral_left _ (tensorAdjointCurve_integrable a b)]
  apply integral_congr_ae
  filter_upwards with t
  unfold tensorAdjointCurve
  rw [inner_freeProp_left]
  simp only [neg_neg]
  rw [MeasureTheory.L2.inner_def]
  have hslice := (tensorConjSlice a b t).coeFn_toLp 2 volume
  apply integral_congr_ae
  filter_upwards [hslice] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, tensorConjSlice_apply, Complex.conj_conj,
    curveRepresentative, mul_comm]

theorem schwartz_tensor_pairing_estimate :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (n : ℕ) (a b : Fin n → SchwartzMap ℝ ℂ) (f : L2),
        ‖∫ t : ℝ, ∫ x : ℝ,
            tensorRaw a b (t, x) *
              curveRepresentative (fun s => freeProp s f) (t, x)‖ₑ ≤
          C * eLpNorm (tensorSliceL1 a b) (4 / 3) volume *
            ENNReal.ofReal ‖f‖ := by
  obtain ⟨C, hCtop, hC⟩ := tensorAdjoint_estimate
  refine ⟨C, hCtop, ?_⟩
  intro n a b f
  rw [← inner_tensorAdjoint_eq_pairing]
  calc
    ‖@inner ℂ L2 _ (tensorAdjoint a b) f‖ₑ ≤
        ‖tensorAdjoint a b‖ₑ * ENNReal.ofReal ‖f‖ := by
      rw [← ofReal_norm]
      calc
        ENNReal.ofReal ‖@inner ℂ L2 _ (tensorAdjoint a b) f‖ ≤
            ENNReal.ofReal (‖tensorAdjoint a b‖ * ‖f‖) :=
          ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)
        _ = ‖tensorAdjoint a b‖ₑ * ENNReal.ofReal ‖f‖ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    _ ≤ (C * eLpNorm (tensorSliceL1 a b) (4 / 3) volume) *
        ENNReal.ofReal ‖f‖ := mul_le_mul_right' (hC n a b) _
    _ = C * eLpNorm (tensorSliceL1 a b) (4 / 3) volume *
        ENNReal.ofReal ‖f‖ := rfl

end CubicNLSPhaseRetrieval
