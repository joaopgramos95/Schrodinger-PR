import Lean_Code.StrichartzSpatialNorming

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators FourierTransform

noncomputable section

set_option maxHeartbeats 3000000

namespace CubicNLSPhaseRetrieval

def schwartzFreeFlow (φ : SchwartzMap ℝ ℂ) (p : ℝ × ℝ) : ℂ :=
  𝓕⁻ (fun ξ : ℝ => schrodingerSymbol p.1 ξ * (𝓕 φ) ξ) p.2

lemma schwartzFreeFlow_continuous (φ : SchwartzMap ℝ ℂ) :
    Continuous (schwartzFreeFlow φ) := by
  unfold schwartzFreeFlow
  simp_rw [Real.fourierInv_eq']
  apply continuous_of_dominated (bound := fun ξ : ℝ => ‖(𝓕 φ) ξ‖)
  · intro p
    have hs : Continuous (schrodingerSymbol p.1) := continuous_schrodingerSymbol p.1
    exact ((by fun_prop : Continuous (fun ξ : ℝ =>
      Complex.exp (((2 * Real.pi * @inner ℝ ℝ _ ξ p.2 : ℝ) : ℂ) * Complex.I))).smul
        (hs.mul (𝓕 φ).continuous)).aestronglyMeasurable
  · intro p
    filter_upwards with ξ
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, norm_mul,
      norm_schrodingerSymbol, one_mul, one_mul]
  · exact (𝓕 φ).integrable.norm
  · filter_upwards with ξ
    have hs : Continuous (fun p : ℝ × ℝ => schrodingerSymbol p.1 ξ) := by
      unfold schrodingerSymbol
      fun_prop
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (((2 * Real.pi * @inner ℝ ℝ _ ξ p.2 : ℝ) : ℂ) * Complex.I))).smul
        (hs.mul continuous_const)

lemma schwartzFreeFlow_measurable (φ : SchwartzMap ℝ ℂ) :
    Measurable (schwartzFreeFlow φ) :=
  (schwartzFreeFlow_continuous φ).measurable

lemma schwartzFreeFlow_slice_ae (φ : SchwartzMap ℝ ℂ) (t : ℝ) :
    (fun x => schwartzFreeFlow φ (t, x)) =ᵐ[volume]
      (freeProp t (φ.toLp 2 volume) : ℝ → ℂ) := by
  exact (schwartz_freeProp_eq_raw_fourierInv t φ).symm

lemma schwartzFreeFlow_uniform_bound (φ : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖schwartzFreeFlow φ (t, x)‖ ≤ ∫ ξ : ℝ, ‖(𝓕 φ) ξ‖ := by
  unfold schwartzFreeFlow
  rw [Real.fourierInv_eq']
  calc
    ‖∫ ξ : ℝ, Complex.exp
        (((2 * Real.pi * @inner ℝ ℝ _ ξ x : ℝ) : ℂ) * Complex.I) •
          (schrodingerSymbol t ξ * (𝓕 φ) ξ)‖ ≤
        ∫ ξ : ℝ, ‖Complex.exp
          (((2 * Real.pi * @inner ℝ ℝ _ ξ x : ℝ) : ℂ) * Complex.I) •
            (schrodingerSymbol t ξ * (𝓕 φ) ξ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖(𝓕 φ) ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, norm_mul,
        norm_schrodingerSymbol, one_mul, one_mul]

lemma schwartzFreeFlow_section_memLp_top (φ : SchwartzMap ℝ ℂ) (t : ℝ) :
    MemLp (fun x => schwartzFreeFlow φ (t, x)) ⊤ volume := by
  refine memLp_top_of_bound
    ((schwartzFreeFlow_measurable φ).comp measurable_prodMk_left).aestronglyMeasurable
    (∫ ξ : ℝ, ‖(𝓕 φ) ξ‖) ?_
  exact Filter.Eventually.of_forall fun x => schwartzFreeFlow_uniform_bound φ t x

lemma curveRepresentative_schwartz_mixed_eq (φ : SchwartzMap ℝ ℂ) :
    scalarMixedENorm volume volume 4 ⊤
        (curveRepresentative fun t => freeProp t (φ.toLp 2 volume)) =
      scalarMixedENorm volume volume 4 ⊤ (schwartzFreeFlow φ) := by
  unfold scalarMixedENorm sectionENorm
  apply eLpNorm_congr_ae
  filter_upwards with t
  exact eLpNorm_congr_ae (schwartzFreeFlow_slice_ae φ t).symm

end CubicNLSPhaseRetrieval
