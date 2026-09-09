import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import Lean_Code.RetardedEndpoint

/-!
# Constructive endpoint control for global cubic NLS solutions

This module derives the part of the endpoint proposition used by phase
retrieval directly from the mild equation and the scalar endpoint estimate.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

theorem curve_section_aestronglyMeasurable
    (mu : Measure ℝ) (w : ℝ → L2) (hw : AEStronglyMeasurable w mu) :
    AEStronglyMeasurable
      (fun t => sectionENorm volume ⊤ (curveRepresentative w) t) mu := by
  obtain ⟨W, hW, hslice⟩ := joint_representative_L2_measurable mu w hw
  have hnorm : Measurable (fun t => sectionENorm volume ⊤ W t) :=
    measurable_esssup_section mu volume W hW
  exact hnorm.aestronglyMeasurable.congr <|
    hslice.mono fun t ht => by
      unfold sectionENorm curveRepresentative
      simpa only [Prod.fst, Prod.snd] using eLpNorm_congr_ae ht

theorem eLpNorm_four_const_mul_ennreal
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (f : X → ℝ≥0∞) :
    eLpNorm (fun x => c * f x) 4 mu = c * eLpNorm f 4 mu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
  rw [show (1 / (4 : ℝ)) = (4 : ℝ)⁻¹ by norm_num]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  rw [lintegral_const_mul' (c ^ (4 : ℝ)) _
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc),
    ENNReal.mul_rpow_of_nonneg]
  · rw [← ENNReal.rpow_mul]
    norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
    congr 2
    apply lintegral_congr
    intro x
    exact (ENNReal.rpow_natCast (f x) 4).symm
  · positivity

set_option maxHeartbeats 2000000 in
/-- The endpoint information used downstream: finite scalar
`L⁴_tL∞_x`, its real-valued section-norm realization, and finiteness of
almost every section. -/
theorem endpoint_control (σ : ℝ) (u : GlobalSolution σ) (I : Set ℝ)
    (hI : MeasurableSet I) (hIbdd : Bornology.IsBounded I) :
    scalarMixedENorm (volume.restrict I) volume 4 ⊤
        (curveRepresentative u.u) < ⊤ ∧
      MemLp (fun t => (sectionENorm volume ⊤
        (curveRepresentative u.u) t).toReal) 4 (volume.restrict I) ∧
      ∀ᵐ t ∂volume.restrict I,
        sectionENorm volume ⊤ (curveRepresentative u.u) t < ⊤ := by
  obtain ⟨T, hTpos, hT⟩ := hIbdd.subset_closedBall_lt 0 0
  have hsub : I ⊆ Set.Icc (-T) T := by
    intro t ht
    have hdist := hT ht
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hdist
    exact abs_le.mp hdist
  let J : Set ℝ := Set.Icc (-T) T
  let mu_t : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → L2 := fun z => freeProp (z.2 - z.1) (u.nonlin z.1)
  let D : ℝ → L2 := fun t =>
    ∫ s, if -T < s ∧ s ≤ t then K (s, t) else 0 ∂volume.restrict J
  have hTint : -T ≤ T := by linarith
  have hnonlin : Integrable u.nonlin (volume.restrict J) := by
    have h := endpoint_nonlin_integrableOn_Icc σ u (-T) T hTint
    change Integrable u.nonlin (volume.restrict (Set.Icc (-T) T)) at h
    simpa only [J] using h
  have hDend : scalarMixedENorm mu_t volume 4 ⊤
      (curveRepresentative D) < ⊤ := by
    simpa only [D, K, J, mu_t] using
      retarded_endpoint_lt_top (-T) T hTint I hI hsub u.nonlin hnonlin
  have hDmeas : AEStronglyMeasurable D mu_t := by
    have hKmeas : AEStronglyMeasurable K
        ((volume.restrict J).prod mu_t) :=
      freeProp_comp_aestronglyMeasurable _ _ _
        (measurable_snd.sub measurable_fst).aestronglyMeasurable
        hnonlin.1.comp_fst
    have hchron : MeasurableSet {z : ℝ × ℝ | -T < z.1 ∧ z.1 ≤ z.2} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_snd)
    have hchrono : AEStronglyMeasurable
        (fun z : ℝ × ℝ => if -T < z.1 ∧ z.1 ≤ z.2 then K z else 0)
        ((volume.restrict J).prod mu_t) := by
      have heq : (fun z : ℝ × ℝ =>
          if -T < z.1 ∧ z.1 ≤ z.2 then K z else 0) =
          {z : ℝ × ℝ | -T < z.1 ∧ z.1 ≤ z.2}.indicator K := by
        funext z
        by_cases hz : -T < z.1 ∧ z.1 ≤ z.2 <;>
          simp [Set.indicator, hz]
      rw [heq]
      exact hKmeas.indicator hchron
    simpa only [D, Function.comp_apply, Prod.swap_prod_mk] using
      hchrono.prod_swap.integral_prod_right'
  let W : ℝ → L2 := fun t => freeProp (t + T) (u.u (-T))
  have hadm : SchrodingerAdmissible 4 ⊤ := by
    refine ⟨by norm_num, by simp, ?_⟩
    simp only [ENNReal.inv_top, add_zero]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  obtain ⟨C, hCtop, hhom⟩ := hom_strichartz
  have hWend : scalarMixedENorm mu_t volume 4 ⊤
      (curveRepresentative W) < ⊤ := by
    have hgroup : W = fun t => freeProp t (freeProp T (u.u (-T))) := by
      funext t
      dsimp [W]
      rw [propagator_unitary.2.1]
    rw [hgroup]
    apply lt_of_le_of_lt _
      ((hhom (freeProp T (u.u (-T)))).trans_lt
        (ENNReal.mul_lt_top hCtop (by finiteness)))
    unfold scalarMixedENorm
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hWmeas : AEStronglyMeasurable W mu_t := by
    exact freeProp_comp_aestronglyMeasurable _ _ _
      (continuous_id.add continuous_const).aestronglyMeasurable
      aestronglyMeasurable_const
  have hD_interval (t : ℝ) (ht : t ∈ I) :
      D t = ∫ s in (-T)..t, freeProp (t - s) (u.nonlin s) := by
    have htJ := hsub ht
    have hlow : -T ≤ t := htJ.1
    rw [intervalIntegral.integral_of_le hlow]
    let S : Set ℝ := Set.Ioc (-T) t
    have hS : MeasurableSet S := measurableSet_Ioc
    have hSJ : S ⊆ J := by
      intro s hs
      exact ⟨hs.1.le, hs.2.trans htJ.2⟩
    change (∫ s, (if -T < s ∧ s ≤ t then
        freeProp (t - s) (u.nonlin s) else 0) ∂volume.restrict J) = _
    have hindicator : (fun s : ℝ => if -T < s ∧ s ≤ t then
        freeProp (t - s) (u.nonlin s) else 0) =
        S.indicator (fun s => freeProp (t - s) (u.nonlin s)) := by
      funext s
      by_cases hs : -T < s ∧ s ≤ t <;> simp [S, Set.indicator, hs]
    rw [hindicator]
    rw [integral_indicator hS, Measure.restrict_restrict_of_subset hSJ]
  have hmild (t : ℝ) (ht : t ∈ I) :
      u.u t = W t - (Complex.I * (σ : ℂ)) • D t := by
    rw [u.mild t (-T), hD_interval t ht]
    dsimp only [W]
    congr 2
    ring
  let Au : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative u.u) t
  let Aw : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative W) t
  let Ad : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative D) t
  let c : ℂ := Complex.I * (σ : ℂ)
  let Acd : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative fun r => c • D r) t
  have hAumeas : AEStronglyMeasurable Au mu_t := by
    exact curve_section_aestronglyMeasurable mu_t u.u
      u.continuous.aestronglyMeasurable.restrict
  have hAwmeas : AEStronglyMeasurable Aw mu_t := by
    exact curve_section_aestronglyMeasurable mu_t W hWmeas
  have hAdmeas : AEStronglyMeasurable Ad mu_t := by
    exact curve_section_aestronglyMeasurable mu_t D hDmeas
  have hAcdmeas : AEStronglyMeasurable Acd mu_t := by
    exact curve_section_aestronglyMeasurable mu_t (fun r => c • D r)
      (hDmeas.const_smul c)
  have hAcd_eq : ∀ t, Acd t = ‖c‖ₑ * Ad t := by
    intro t
    unfold Acd Ad sectionENorm curveRepresentative
    rw [eLpNorm_congr_ae (Lp.coeFn_smul c (D t))]
    exact eLpNorm_const_smul c (D t : ℝ → ℂ) ⊤ volume
  have hAcdend : eLpNorm Acd 4 mu_t < ⊤ := by
    rw [show Acd = fun t => ‖c‖ₑ * Ad t by funext t; exact hAcd_eq t]
    rw [eLpNorm_four_const_mul_ennreal mu_t ‖c‖ₑ ENNReal.coe_ne_top Ad]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hDend
  have hpoint : ∀ᵐ t : ℝ ∂mu_t, Au t ≤ Aw t + Acd t := by
    filter_upwards [ae_restrict_mem hI] with t ht
    unfold Au Aw Acd sectionENorm curveRepresentative
    simp only [Prod.fst, Prod.snd]
    rw [hmild t ht]
    change eLpNorm (⇑(W t - c • D t)) ⊤ volume ≤ _
    apply le_trans (eLpNorm_congr_ae (Lp.coeFn_sub (W t) (c • D t))).le
    exact eLpNorm_sub_le (Lp.stronglyMeasurable (W t)).aestronglyMeasurable
      (Lp.stronglyMeasurable (c • D t)).aestronglyMeasurable (by norm_num)
  have huend : eLpNorm Au 4 mu_t < ⊤ := by
    have hpoint_enorm : ∀ᵐ t : ℝ ∂mu_t,
        ‖Au t‖ₑ ≤ ‖Aw t + Acd t‖ₑ := by
      filter_upwards [hpoint] with t ht
      simpa only [enorm_eq_self] using ht
    apply lt_of_le_of_lt (eLpNorm_mono_enorm_ae hpoint_enorm)
    apply lt_of_le_of_lt
      (eLpNorm_add_le hAwmeas hAcdmeas (by norm_num))
    exact ENNReal.add_lt_top.2 ⟨hWend, hAcdend⟩
  have hAufin : ∀ᵐ t : ℝ ∂mu_t, Au t < ⊤ := by
    have hlin : (∫⁻ t, Au t ^ (4 : ℝ) ∂mu_t) < ⊤ := by
      rw [← ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      simpa only [scalarMixedENorm, Au, ENNReal.rpow_natCast,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
          (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
        ENNReal.toReal_ofNat, enorm_eq_self] using huend
    have hpow : ∀ᵐ t : ℝ ∂mu_t, Au t ^ (4 : ℝ) < ⊤ :=
      ae_lt_top' (hAumeas.aemeasurable.pow_const 4) hlin.ne
    filter_upwards [hpow] with t ht
    by_contra htop
    have : Au t = ⊤ := top_unique (not_lt.mp htop)
    rw [this, ENNReal.top_rpow_of_pos (by norm_num)] at ht
    exact lt_irrefl ⊤ ht
  refine ⟨?_, ?_, ?_⟩
  · simpa only [scalarMixedENorm, Au, mu_t] using huend
  · refine ⟨?_, ?_⟩
    · exact hAumeas.aemeasurable.ennreal_toReal.aestronglyMeasurable
    · change eLpNorm (fun t => (Au t).toReal) 4 mu_t < ⊤
      apply lt_of_eq_of_lt (eLpNorm_congr_enorm_ae
        (μ := mu_t) (p := (4 : ℝ≥0∞)) (f := fun t => (Au t).toReal)
          (g := Au) ?_) huend
      filter_upwards [hAufin] with t ht
      rw [Real.enorm_toReal ht.ne, enorm_eq_self]
  · simpa only [Au, mu_t] using hAufin

end CubicNLSPhaseRetrieval
