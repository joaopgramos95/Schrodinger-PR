import Mathlib
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Lean_Code.EndpointForcing
import Lean_Code.EndpointMinkowski
import Lean_Code.Strichartz1D

/-!
# Scalar endpoint estimate for chronological Duhamel integrals
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

set_option maxHeartbeats 2000000 in
/-- The chronological Duhamel integral of an `L¹_tL²_x` forcing has the
endpoint scalar mixed norm on a bounded output set.  This is the precise
representative-level form of the endpoint Minkowski argument. -/
theorem retarded_endpoint_lt_top
    (a b : ℝ) (hab : a ≤ b) (I : Set ℝ) (hI : MeasurableSet I)
    (hI_sub : I ⊆ Set.Icc a b) (F : ℝ → L2)
    (hF : Integrable F (volume.restrict (Set.Icc a b))) :
    let D : ℝ → L2 := fun t =>
      ∫ s, if a < s ∧ s ≤ t then freeProp (t - s) (F s) else 0
        ∂volume.restrict (Set.Icc a b)
    scalarMixedENorm (volume.restrict I) volume 4 ⊤
      (curveRepresentative D) < ⊤ := by
  let nu : Measure ℝ := volume.restrict (Set.Icc a b)
  let mu_t : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → L2 := fun z => freeProp (z.2 - z.1) (F z.1)
  have hK : AEStronglyMeasurable K (nu.prod mu_t) :=
    freeProp_comp_aestronglyMeasurable _ _ _
      (measurable_snd.sub measurable_fst).aestronglyMeasurable hF.1.comp_fst
  obtain ⟨U, hUmeas, hUslice⟩ :=
    joint_representative_L2_measurable (nu.prod mu_t) K hK
  let E : Set (ℝ × (ℝ × ℝ)) :=
    {z | a < z.1 ∧ z.1 ≤ z.2.1}
  have hE : MeasurableSet E := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_fst.comp measurable_snd))
  let Phi : ℝ → ℝ → ℝ → ℂ := fun s t x =>
    if a < s ∧ s ≤ t then U ((s, t), x) else 0
  have hPhi_meas : Measurable
      (fun z : ℝ × (ℝ × ℝ) => Phi z.1 z.2.1 z.2.2) := by
    have hbase : Measurable
        (fun z : ℝ × (ℝ × ℝ) => U ((z.1, z.2.1), z.2.2)) :=
      hUmeas.comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))
    exact hbase.ite hE measurable_const
  have hPhi : AEStronglyMeasurable
      (fun z : ℝ × (ℝ × ℝ) => Phi z.1 z.2.1 z.2.2)
      (nu.prod (mu_t.prod volume)) := hPhi_meas.aestronglyMeasurable
  have hadm : SchrodingerAdmissible 4 ⊤ := by
    refine ⟨by norm_num, by simp, ?_⟩
    simp only [ENNReal.inv_top, add_zero]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  obtain ⟨C, hCtop, hhom⟩ := hom_strichartz
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod hUslice
  have hPhi_bound : ∀ᵐ s : ℝ ∂nu,
      scalarMixedENorm mu_t volume 4 ⊤ (fun z => Phi s z.1 z.2) ≤
        C * ‖F s‖ₑ := by
    filter_upwards [hslices] with s hs
    let Es : Set (ℝ × ℝ) := {z | a < s ∧ s ≤ z.1}
    have hPhi_indicator : (fun z => Phi s z.1 z.2) =
        Es.indicator (fun z => U ((s, z.1), z.2)) := by
      funext z
      by_cases hz : a < s ∧ s ≤ z.1 <;> simp [Phi, Es, hz]
    rw [hPhi_indicator]
    calc
      scalarMixedENorm mu_t volume 4 ⊤
          (Es.indicator (fun z => U ((s, z.1), z.2))) ≤
          scalarMixedENorm mu_t volume 4 ⊤
            (fun z => U ((s, z.1), z.2)) :=
        scalarMixedENorm_indicator_le mu_t volume 4 ⊤ Es _
      _ = scalarMixedENorm mu_t volume 4 ⊤
          (curveRepresentative fun t => K (s, t)) := by
        unfold scalarMixedENorm
        apply eLpNorm_congr_ae
        filter_upwards [hs] with t ht
        exact eLpNorm_congr_ae ht
      _ ≤ scalarMixedENorm volume volume 4 ⊤
          (curveRepresentative fun t => K (s, t)) := by
        unfold scalarMixedENorm
        exact eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = scalarMixedENorm volume volume 4 ⊤
          (curveRepresentative fun t => freeProp t (freeProp (-s) (F s))) := by
        apply congrArg (fun w : ℝ → L2 =>
          scalarMixedENorm volume volume 4 ⊤ (curveRepresentative w))
        funext t
        dsimp [K]
        rw [propagator_unitary.2.1]
        congr 1
      _ ≤ C * ENNReal.ofReal ‖freeProp (-s) (F s)‖ := hhom _
      _ = C * ‖F s‖ₑ := by
        rw [norm_freeProp, ofReal_norm]
  have hfinite :
      (∫⁻ s, scalarMixedENorm mu_t volume 4 ⊤
        (fun z => Phi s z.1 z.2) ∂nu) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono_ae hPhi_bound)
    rw [lintegral_const_mul'' C hF.1.enorm]
    exact ENNReal.mul_lt_top hCtop hF.2
  have hmink := scalar_mixed_minkowski_four_top nu mu_t volume Phi hPhi_meas
  have hscalar : scalarMixedENorm mu_t volume 4 ⊤
      (fun z => ∫ s, Phi s z.1 z.2 ∂nu) < ⊤ := hmink.trans_lt hfinite
  let D : ℝ → L2 := fun t =>
    ∫ s, if a < s ∧ s ≤ t then K (s, t) else 0 ∂nu
  have hswap : ∀ᵐ z : ℝ × ℝ ∂mu_t.prod nu,
      (fun x => U ((z.2, z.1), x)) =ᵐ[volume] (K (z.2, z.1) : ℝ → ℂ) :=
    MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae hUslice
  have hts := MeasureTheory.Measure.ae_ae_of_ae_prod hswap
  have hidentify : ∀ᵐ t : ℝ ∂mu_t,
      (D t : ℝ → ℂ) =ᵐ[volume] fun x => ∫ s, Phi s t x ∂nu := by
    filter_upwards [hts] with t ht
    let gt : ℝ → L2 := fun s => if a < s ∧ s ≤ t then K (s, t) else 0
    let Gt : ℝ × ℝ → ℂ := fun z =>
      if a < z.1 ∧ z.1 ≤ t then U ((z.1, t), z.2) else 0
    have hKt : AEStronglyMeasurable (fun s => K (s, t)) nu := by
      exact freeProp_comp_aestronglyMeasurable _ _ _
        (continuous_const.sub continuous_id).aestronglyMeasurable hF.1
    have hgt : Integrable gt nu := by
      have hset : MeasurableSet {s : ℝ | a < s ∧ s ≤ t} :=
        (measurableSet_lt measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const)
      have hgm : AEStronglyMeasurable gt nu := by
        have hgt_indicator : gt = {s : ℝ | a < s ∧ s ≤ t}.indicator
            (fun s => K (s, t)) := by
          funext s
          by_cases hs : a < s ∧ s ≤ t <;> simp [gt, Set.indicator, hs]
        rw [hgt_indicator]
        exact hKt.indicator hset
      exact MeasureTheory.Integrable.mono hF hgm
        (Filter.Eventually.of_forall fun s => by
          by_cases hs : a < s ∧ s ≤ t
          · simp [gt, K, hs, norm_freeProp]
          · simp [gt, hs])
    have hGt : AEStronglyMeasurable Gt (nu.prod volume) := by
      have hbase : Measurable (fun z : ℝ × ℝ => U ((z.1, t), z.2)) :=
        hUmeas.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
      have hset : MeasurableSet {z : ℝ × ℝ | a < z.1 ∧ z.1 ≤ t} :=
        ((measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_le measurable_fst measurable_const))
      exact (hbase.ite hset measurable_const).aestronglyMeasurable
    have hGslice : ∀ᵐ s : ℝ ∂nu,
        (fun x => Gt (s, x)) =ᵐ[volume] (gt s : ℝ → ℂ) := by
      filter_upwards [ht] with s hs
      by_cases hst : a < s ∧ s ≤ t
      · simpa [Gt, gt, hst] using hs
      · exact Filter.Eventually.of_forall fun x => by simp [Gt, gt, hst]
    have hbridge := coeFn_integral_L2_of_joint nu gt Gt hgt hGt hGslice
    simpa only [D, gt, Gt, Phi, E, K, nu] using hbridge
  unfold scalarMixedENorm
  apply lt_of_eq_of_lt _ hscalar
  apply eLpNorm_congr_ae
  filter_upwards [hidentify] with t ht
  exact eLpNorm_congr_ae ht

end CubicNLSPhaseRetrieval
