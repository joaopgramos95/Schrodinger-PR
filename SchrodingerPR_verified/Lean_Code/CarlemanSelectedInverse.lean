import Lean_Code.JointL2Representative

/-!
# The selected inverse on measurable spacetime sources

This module packages the explicit frequency-side inverse and isolates the one
remaining identification statement needed by the graph closure.
-/

open Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

def carlemanFrequencySourceCurve (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume))) :
    ℝ → SpatialL2Two :=
  fun t => fourierL2Two (carlemanSourceCurve f hf t)

theorem carlemanFrequencySourceCurve_integrable (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤) :
    Integrable (carlemanFrequencySourceCurve f hf) := by
  exact (fourierL2Two.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp
    (carlemanSourceCurve_integrable f hf hfinite)

/-- The branch-selected solution curve in spatial frequency. -/
def selectedCarlemanFrequencySolution (β : ℝ) (hβ : 0 < β)
    (g : ℝ → SpatialL2Two) (t : ℝ) : SpatialL2Two :=
  ∫ s, carlemanFrequencyPropagator β (t - s) hβ (g s)

theorem selectedCarlemanFrequencySolution_norm_le (β : ℝ) (hβ : 0 < β)
    (g : ℝ → SpatialL2Two) (hg : Integrable g) (t : ℝ) :
    ‖selectedCarlemanFrequencySolution β hβ g t‖ ≤ ∫ s, ‖g s‖ := by
  exact norm_integral_carlemanFrequencyPropagator_le β t hβ g hg

private theorem ofReal_integral_norm_carlemanFrequencySourceCurve
    (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤) :
    ENNReal.ofReal (∫ t, ‖carlemanFrequencySourceCurve f hf t‖) =
      scalarMixedENorm volume (volume.prod volume) 1 2 f := by
  have hcurve := carlemanSourceCurve_integrable f hf hfinite
  have hfreq := carlemanFrequencySourceCurve_integrable f hf hfinite
  rw [ofReal_integral_norm_eq_lintegral_enorm hfreq]
  have hnorm : (∫⁻ t, ‖carlemanFrequencySourceCurve f hf t‖ₑ ∂volume) =
      ∫⁻ t, ‖carlemanSourceCurve f hf t‖ₑ ∂volume := by
    apply lintegral_congr
    intro t
    rw [carlemanFrequencySourceCurve, LinearIsometryEquiv.enorm_map]
  rw [hnorm, lintegral_congr_ae (enorm_carlemanSourceCurve_ae f hf hfinite)]
  rw [scalarMixedENorm, eLpNorm_one_eq_lintegral_enorm]
  simp only [enorm_eq_self]

/-- Once the weak solution has been identified with the explicit selected
inverse in frequency, the sharp gauge estimate follows with constant one. -/
theorem scalarMixedENorm_top_two_le_of_selected_identification
    (β : ℝ) (hβ : 0 < β) (w f : Spacetime2)
    (hw : AEStronglyMeasurable w (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2 w < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤)
    (hid : ∀ᵐ t ∂volume,
      fourierL2Two (carlemanSourceCurve w hw t) =
        selectedCarlemanFrequencySolution β hβ
          (carlemanFrequencySourceCurve f hf) t) :
    scalarMixedENorm volume (volume.prod volume) ⊤ 2 w ≤
      scalarMixedENorm volume (volume.prod volume) 1 2 f := by
  let B := scalarMixedENorm volume (volume.prod volume) 1 2 f
  have hfreq := carlemanFrequencySourceCurve_integrable f hf hffinite
  have hpoint : ∀ᵐ t ∂volume, ‖carlemanSourceCurve w hw t‖ₑ ≤ B := by
    filter_upwards [hid] with t ht
    rw [← ofReal_norm]
    have hreal : ‖carlemanSourceCurve w hw t‖ ≤
        ∫ s, ‖carlemanFrequencySourceCurve f hf s‖ := by
      calc
        ‖carlemanSourceCurve w hw t‖ =
            ‖fourierL2Two (carlemanSourceCurve w hw t)‖ := by
              rw [LinearIsometryEquiv.norm_map]
        _ = ‖selectedCarlemanFrequencySolution β hβ
              (carlemanFrequencySourceCurve f hf) t‖ := by rw [ht]
        _ ≤ ∫ s, ‖carlemanFrequencySourceCurve f hf s‖ :=
          selectedCarlemanFrequencySolution_norm_le β hβ _ hfreq t
    calc
      ENNReal.ofReal ‖carlemanSourceCurve w hw t‖ ≤
          ENNReal.ofReal (∫ s, ‖carlemanFrequencySourceCurve f hf s‖) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = B := ofReal_integral_norm_carlemanFrequencySourceCurve f hf hffinite
  have hsection : ∀ᵐ t ∂volume,
      sectionENorm (volume.prod volume) 2 w t ≤ B := by
    filter_upwards [enorm_carlemanSolutionCurve_ae w hw hwfinite, hpoint]
      with t hnorm ht
    rwa [hnorm] at ht
  rw [scalarMixedENorm, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  simp only [enorm_eq_self]
  exact essSup_le_of_ae_le B hsection

end CubicNLSPhaseRetrieval
