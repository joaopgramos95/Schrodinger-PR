import Lean_Code.CarlemanSections

/-! Integrable spatial `L²` curves represented by raw spacetime sources. -/

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

def carlemanSourceCurve (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume))) :
    ℝ → SpatialL2Two :=
  spacetimeSectionL2 (hf.mk f) hf.stronglyMeasurable_mk.measurable

theorem carlemanSourceCurve_stronglyMeasurable (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume))) :
    StronglyMeasurable (carlemanSourceCurve f hf) :=
  spacetimeSectionL2_stronglyMeasurable _ _

theorem carlemanSourceCurve_section_ae (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤) :
    ∀ᵐ t ∂volume,
      (carlemanSourceCurve f hf t : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
        fun z => f (t, z) := by
  have hsections := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hnormfinite : ∀ᵐ t ∂volume,
      sectionENorm (volume.prod volume) 2 f t < ⊤ := by
    apply ae_lt_top'
    · exact (by
        unfold sectionENorm
        simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
        exact ((hf.aemeasurable.enorm.pow_const _).lintegral_prod_right').pow_const _)
    · have hg := hfinite
      rw [scalarMixedENorm, eLpNorm_one_eq_lintegral_enorm] at hg
      simpa only [enorm_eq_self] using hg.ne
  filter_upwards [hsections, hnormfinite] with t ht hnt
  have htmk : (fun z => hf.mk f (t, z)) =ᵐ[volume.prod volume]
      fun z => f (t, z) := ht.mono fun z hz => hz.symm
  have hmkfinite : eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) < ⊤ := by
    rw [show eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) =
      sectionENorm (volume.prod volume) 2 f t by
        exact eLpNorm_congr_ae htmk]
    exact hnt
  exact (spacetimeSectionL2_coe_ae _ _ t hmkfinite).trans htmk

theorem enorm_carlemanSourceCurve_ae (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤) :
    ∀ᵐ t ∂volume, ‖carlemanSourceCurve f hf t‖ₑ =
      sectionENorm (volume.prod volume) 2 f t := by
  have hsections := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hnormfinite : ∀ᵐ t ∂volume,
      sectionENorm (volume.prod volume) 2 f t < ⊤ := by
    apply ae_lt_top'
    · exact (by
        unfold sectionENorm
        simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
        exact ((hf.aemeasurable.enorm.pow_const _).lintegral_prod_right').pow_const _)
    · have hg := hfinite
      rw [scalarMixedENorm, eLpNorm_one_eq_lintegral_enorm] at hg
      simpa only [enorm_eq_self] using hg.ne
  filter_upwards [hsections, hnormfinite] with t ht hnt
  have htmk : (fun z => hf.mk f (t, z)) =ᵐ[volume.prod volume]
      fun z => f (t, z) := ht.mono fun z hz => hz.symm
  have hmkfinite : eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) < ⊤ := by
    rw [show eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) =
      sectionENorm (volume.prod volume) 2 f t by
        exact eLpNorm_congr_ae htmk]
    exact hnt
  change ‖spacetimeSectionL2 (hf.mk f) hf.stronglyMeasurable_mk.measurable t‖ₑ = _
  rw [enorm_spacetimeSectionL2 _ _ t hmkfinite]
  exact eLpNorm_congr_ae htmk

theorem carlemanSourceCurve_integrable (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤) :
    Integrable (carlemanSourceCurve f hf) := by
  constructor
  · exact (carlemanSourceCurve_stronglyMeasurable f hf).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    rw [lintegral_congr_ae (enorm_carlemanSourceCurve_ae f hf hfinite)]
    have hg := hfinite
    rw [scalarMixedENorm, eLpNorm_one_eq_lintegral_enorm] at hg
    simpa only [enorm_eq_self] using hg

theorem carlemanSolutionCurve_section_ae (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2 f < ⊤) :
    ∀ᵐ t ∂volume,
      (carlemanSourceCurve f hf t : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
        fun z => f (t, z) := by
  let A : ℝ → ENNReal := fun t => sectionENorm (volume.prod volume) 2 f t
  have hsections := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hAle : ∀ᵐ t ∂volume, A t ≤ essSup A volume := ENNReal.ae_le_essSup A
  have hessfinite : essSup A volume < ⊤ := by
    simpa only [scalarMixedENorm, eLpNorm_exponent_top,
      eLpNormEssSup_eq_essSup_enorm, enorm_eq_self, A] using hfinite
  filter_upwards [hsections, hAle] with t ht hAt
  have hnt : sectionENorm (volume.prod volume) 2 f t < ⊤ :=
    hAt.trans_lt hessfinite
  have htmk : (fun z => hf.mk f (t, z)) =ᵐ[volume.prod volume]
      fun z => f (t, z) := ht.mono fun z hz => hz.symm
  have hmkfinite : eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) < ⊤ := by
    rw [show eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) =
      sectionENorm (volume.prod volume) 2 f t by
        exact eLpNorm_congr_ae htmk]
    exact hnt
  exact (spacetimeSectionL2_coe_ae _ _ t hmkfinite).trans htmk

theorem enorm_carlemanSolutionCurve_ae (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2 f < ⊤) :
    ∀ᵐ t ∂volume, ‖carlemanSourceCurve f hf t‖ₑ =
      sectionENorm (volume.prod volume) 2 f t := by
  let A : ℝ → ENNReal := fun t => sectionENorm (volume.prod volume) 2 f t
  have hsections := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hAle : ∀ᵐ t ∂volume, A t ≤ essSup A volume := ENNReal.ae_le_essSup A
  have hessfinite : essSup A volume < ⊤ := by
    simpa only [scalarMixedENorm, eLpNorm_exponent_top,
      eLpNormEssSup_eq_essSup_enorm, enorm_eq_self, A] using hfinite
  filter_upwards [hsections, hAle] with t ht hAt
  have hnt : sectionENorm (volume.prod volume) 2 f t < ⊤ :=
    hAt.trans_lt hessfinite
  have htmk : (fun z => hf.mk f (t, z)) =ᵐ[volume.prod volume]
      fun z => f (t, z) := ht.mono fun z hz => hz.symm
  have hmkfinite : eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) < ⊤ := by
    rw [show eLpNorm (fun z => hf.mk f (t, z)) 2 (volume.prod volume) =
      sectionENorm (volume.prod volume) 2 f t by
        exact eLpNorm_congr_ae htmk]
    exact hnt
  change ‖spacetimeSectionL2 (hf.mk f) hf.stronglyMeasurable_mk.measurable t‖ₑ = _
  rw [enorm_spacetimeSectionL2 _ _ t hmkfinite]
  exact eLpNorm_congr_ae htmk

theorem enorm_carlemanSolutionCurve_le (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2 f < ⊤) :
    ∀ᵐ t ∂volume, ‖carlemanSourceCurve f hf t‖ₑ ≤
      scalarMixedENorm volume (volume.prod volume) ⊤ 2 f := by
  let A : ℝ → ENNReal := fun t => sectionENorm (volume.prod volume) 2 f t
  have hAle : ∀ᵐ t ∂volume, A t ≤ essSup A volume := ENNReal.ae_le_essSup A
  filter_upwards [enorm_carlemanSolutionCurve_ae f hf hfinite, hAle] with t ht hAt
  rw [ht]
  simpa only [scalarMixedENorm, eLpNorm_exponent_top,
    eLpNormEssSup_eq_essSup_enorm, enorm_eq_self, A] using hAt

end CubicNLSPhaseRetrieval
