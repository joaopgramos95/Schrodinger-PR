import Lean_Code.FourierSobolev
import Lean_Code.Strichartz1D
import Lean_Code.CubicFlow
import Lean_Code.EndpointMinkowski

/-!
# Persistence and endpoint regularity

Blueprint chapter: `chap:endpoint` (module 6).
Imports: modules 1, 4, and 5.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- A curve together with all spatial derivatives through order `k` in the fixed-point space. -/
structure HigherFixedPointData (k : ℕ) (I : Set ℝ) (u : ℝ → L2) where
  deriv : Fin (k + 1) → ℝ → L2
  deriv_zero : deriv ⟨0, Nat.zero_lt_succ k⟩ = u
  deriv_toTempered : ∀ j t,
    MeasureTheory.Lp.toTemperedDistribution (deriv j t) =
      LineDeriv.iteratedLineDerivOp (fun _ : Fin j.val => (1 : ℝ))
        (MeasureTheory.Lp.toTemperedDistribution (u t))
  memX : ∀ j, MemFixedPointSpace I (deriv j)

/-- `def:Xk-space`: sum of fixed-point norms of derivatives through order `k`. -/
def higherFixedPointNorm {k : ℕ} {I : Set ℝ} {u : ℝ → L2}
    (d : HigherFixedPointData k I u) : ℝ≥0∞ :=
  ∑ j : Fin (k + 1), fixedPointNorm I (d.deriv j)

/-- Pointwise spatial derivative of a smooth spacetime scalar function. -/
def spatialDeriv (k : ℕ) (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  iteratedDeriv k (fun x => u (p.1, x)) p.2

/-
/-- The cubic forcing is in `L¹_tL²_x` on every bounded measurable time
set.  This is the elementary Hölder part of the endpoint proposition and is
independent of Strichartz. -/
private theorem cubicForcing_L1L2_lt_top (σ : ℝ) (u : GlobalSolution σ)
    (I : Set ℝ) (hI : MeasurableSet I) (hIbdd : Bornology.IsBounded I) :
    scalarMixedENorm (volume.restrict I) volume 1 2 (cubicForcingFn u.u) < ⊤ := by
  obtain ⟨U, hUmeas, hUslice⟩ :=
    joint_representative_L2_measurable volume u.u u.continuous.aestronglyMeasurable
  let A : ℝ → ℝ≥0∞ := fun t => sectionENorm volume 6 U t
  have hAmeas : Measurable A := measurable_section_norm_early 6 U hUmeas
  have hAslice : ∀ᵐ t : ℝ ∂volume,
      A t = eLpNorm (u.u t : ℝ → ℂ) 6 volume := by
    filter_upwards [hUslice] with t ht
    exact eLpNorm_congr_ae ht
  obtain ⟨T, _hTpos, hT⟩ := hIbdd.subset_closedBall_lt 0 0
  have hsub : I ⊆ Set.Icc (-T) T := by
    intro t ht
    have hdist := hT ht
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hdist
    exact abs_le.mp hdist
  have hA6 : eLpNorm A 6 (volume.restrict I) < ⊤ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
    apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
    apply ne_of_lt
    calc
      (∫⁻ t in I, A t ^ (6 : ℝ) ∂volume) ≤
          ∫⁻ t in Set.Icc (-T) T, A t ^ (6 : ℝ) ∂volume :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
      _ = ∫⁻ t in Set.Icc (-T) T,
          eLpNorm (u.u t : ℝ → ℂ) 6 volume ^ (6 : ℝ) ∂volume := by
        apply lintegral_congr_ae
        exact (ae_restrict_of_ae hAslice).mono fun t ht => by
          simpa only using congrArg (fun z : ℝ≥0∞ => z ^ (6 : ℝ)) ht
      _ < ⊤ := by simpa [ENNReal.rpow_natCast] using u.memL6_loc T
  have hA3meas : AEStronglyMeasurable (fun t => A t ^ (3 : ℝ))
      (volume.restrict I) :=
    (hAmeas.pow_const 3).aestronglyMeasurable.restrict
  have hA3two : eLpNorm (fun t => A t ^ (3 : ℝ)) 2
      (volume.restrict I) < ⊤ := by
    calc
      eLpNorm (fun t => A t ^ (3 : ℝ)) 2 (volume.restrict I) =
          eLpNorm A 6 (volume.restrict I) ^ (3 : ℝ) := by
        rw [show (fun t => A t ^ (3 : ℝ)) =
            fun t => ‖A t‖ₑ ^ (3 : ℝ) by funext t; rw [enorm_eq_self]]
        rw [eLpNorm_enorm_rpow A (p := (2 : ℝ≥0∞))
          (q := (3 : ℝ)) (μ := volume.restrict I) (by norm_num)]
        norm_num
      _ < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hA6.ne
  have hA3one : eLpNorm (fun t => A t ^ (3 : ℝ)) 1
      (volume.restrict I) < ⊤ := by
    apply lt_of_le_of_lt
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞))
        (q := (2 : ℝ≥0∞)) (by norm_num) hA3meas)
    apply ENNReal.mul_lt_top hA3two
    apply ENNReal.rpow_lt_top_of_nonneg
    · norm_num
    · simpa [Measure.restrict_apply, hI] using
        (hIbdd.measure_lt_top (μ := volume)).ne
  rw [scalarMixedENorm]
  apply lt_of_eq_of_lt _ hA3one
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_of_ae hAslice] with t ht
  change eLpNorm (fun x => ((‖(u.u t : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) *
      (u.u t : ℝ → ℂ) x) 2 volume = A t ^ (3 : ℝ)
  rw [cubic_section_L2_eq_L6_cubed, ← ht]

/-- The explicit nonlinear `L²` curve is Bochner-integrable on compact time
intervals.  The solution interface records integrability after a unitary free
propagator; joint continuity of the group removes that harmless propagator. -/
set_option maxHeartbeats 2000000 in
theorem nonlin_integrableOn_Icc (σ : ℝ) (u : GlobalSolution σ)
    (a b : ℝ) (hab : a ≤ b) : IntegrableOn u.nonlin (Set.Icc a b) := by
  let g : ℝ → L2 := fun s => freeProp (b - s) (u.nonlin s)
  have hg : IntegrableOn g (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (u.forcing_integrable a b)
  have hpair : AEStronglyMeasurable (fun s => (s - b, g s))
      (volume.restrict (Set.Icc a b)) :=
    (continuous_id.sub continuous_const).aestronglyMeasurable.prodMk hg.1
  have hinv : AEStronglyMeasurable (fun s => freeProp (s - b) (g s))
      (volume.restrict (Set.Icc a b)) :=
    continuous_freeProp_joint.comp_aestronglyMeasurable hpair
  have hrecover (s : ℝ) : freeProp (s - b) (g s) = u.nonlin s := by
    dsimp [g]
    rw [propagator_unitary.2.1]
    convert propagator_unitary.2.2.1 (u.nonlin s) using 2
    ring
  have hnonlin : AEStronglyMeasurable u.nonlin
      (volume.restrict (Set.Icc a b)) :=
    hinv.congr (Filter.Eventually.of_forall hrecover)
  exact MeasureTheory.Integrable.mono' hg hnonlin
    (Filter.Eventually.of_forall fun s => by
      dsimp [g]
      rw [norm_freeProp])
-/

/-
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
  have hpair : AEStronglyMeasurable
      (fun z : ℝ × ℝ => (z.2 - z.1, F z.1)) (nu.prod mu_t) :=
    (measurable_snd.sub measurable_fst).aestronglyMeasurable.prodMk hF.1.comp_fst
  have hK : AEStronglyMeasurable K (nu.prod mu_t) :=
    continuous_freeProp_joint.comp_aestronglyMeasurable hpair
  obtain ⟨U, hUmeas, hUslice⟩ :=
    joint_representative_L2_measurable (nu.prod mu_t) K hK
  let E : Set (ℝ × (ℝ × ℝ)) :=
    {z | a < z.1 ∧ z.1 ≤ z.2.1}
  have hE : MeasurableSet E := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_fst.comp measurable_snd))
  let Phi : ℝ → ℝ → ℝ → ℂ := fun s t x =>
    E.indicator (fun z => U ((z.1, z.2.1), z.2.2)) (s, (t, x))
  have hPhi_meas : Measurable
      (fun z : ℝ × (ℝ × ℝ) => Phi z.1 z.2.1 z.2.2) := by
    have hbase : Measurable
        (fun z : ℝ × (ℝ × ℝ) => U ((z.1, z.2.1), z.2.2)) :=
      hUmeas.comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))
    exact hbase.indicator hE
  have hPhi : AEStronglyMeasurable
      (fun z : ℝ × (ℝ × ℝ) => Phi z.1 z.2.1 z.2.2)
      (nu.prod (mu_t.prod volume)) := hPhi_meas.aestronglyMeasurable
  obtain ⟨C, hCtop, hhom⟩ := hom_strichartz
  have hslices := ae_ae_of_ae_prod hUslice
  have hPhi_bound : ∀ᵐ s : ℝ ∂nu,
      scalarMixedENorm mu_t volume 4 ⊤ (fun z => Phi s z.1 z.2) ≤
        C * ‖F s‖ₑ := by
    filter_upwards [hslices] with s hs
    let Es : Set (ℝ × ℝ) := {z | a < s ∧ s ≤ z.1}
    have hPhi_indicator : (fun z => Phi s z.1 z.2) =
        Es.indicator (fun z => U ((s, z.1), z.2)) := by
      funext z
      rfl
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
        congr 1
        funext t
        congr 1
        dsimp [K]
        rw [propagator_unitary.2.2.1]
        congr 1
        ring
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
  have hKchrono : AEStronglyMeasurable
      (fun z : ℝ × ℝ => if a < z.1 ∧ z.1 ≤ z.2 then K z else 0)
      (nu.prod mu_t) := by
    have hchron : MeasurableSet {z : ℝ × ℝ | a < z.1 ∧ z.1 ≤ z.2} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_snd)
    exact hK.indicator hchron
  have hDmeas : AEStronglyMeasurable D mu_t := by
    exact hKchrono.integral_prod_right'
  have hswap : ∀ᵐ z : ℝ × ℝ ∂mu_t.prod nu,
      (fun x => U ((z.2, z.1), x)) =ᵐ[volume] (K (z.2, z.1) : ℝ → ℂ) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hUslice
  have hts := ae_ae_of_ae_prod hswap
  have hidentify : ∀ᵐ t : ℝ ∂mu_t,
      (D t : ℝ → ℂ) =ᵐ[volume] fun x => ∫ s, Phi s t x ∂nu := by
    filter_upwards [hts] with t ht
    let gt : ℝ → L2 := fun s => if a < s ∧ s ≤ t then K (s, t) else 0
    let Gt : ℝ × ℝ → ℂ := fun z =>
      if a < z.1 ∧ z.1 ≤ t then U ((z.1, t), z.2) else 0
    have hKt : AEStronglyMeasurable (fun s => K (s, t)) nu := by
      have hp : AEStronglyMeasurable (fun s => (t - s, F s)) nu :=
        (continuous_const.sub continuous_id).aestronglyMeasurable.prodMk hF.1
      exact continuous_freeProp_joint.comp_aestronglyMeasurable hp
    have hgt : Integrable gt nu := by
      have hset : MeasurableSet {s : ℝ | a < s ∧ s ≤ t} :=
        (measurableSet_lt measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const)
      have hgm : AEStronglyMeasurable gt nu := hKt.indicator hset
      exact MeasureTheory.Integrable.mono' hF hgm
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
      exact (hbase.indicator hset).aestronglyMeasurable
    have hGslice : ∀ᵐ s : ℝ ∂nu,
        (fun x => Gt (s, x)) =ᵐ[volume] (gt s : ℝ → ℂ) := by
      filter_upwards [ht] with s hs
      by_cases hst : a < s ∧ s ≤ t
      · simpa [Gt, gt, hst] using hs
      · simp [Gt, gt, hst]
    have hbridge := coeFn_integral_L2_of_joint nu gt Gt hgt hGt hGslice
    simpa only [D, gt, Gt, Phi, E, K, nu] using hbridge
  unfold scalarMixedENorm
  apply lt_of_eq_of_lt _ hscalar
  apply eLpNorm_congr_ae
  filter_upwards [hidentify] with t ht
  exact eLpNorm_congr_ae ht

theorem curve_section_aestronglyMeasurable
    (mu : Measure ℝ) (w : ℝ → L2) (hw : AEStronglyMeasurable w mu) :
    AEStronglyMeasurable
      (fun t => sectionENorm volume ⊤ (curveRepresentative w) t) mu := by
  obtain ⟨W, hW, hslice⟩ := joint_representative_L2_measurable mu w hw
  have hnorm : Measurable (fun t => sectionENorm volume ⊤ W t) :=
    measurable_esssup_section mu volume W hW
  exact hnorm.aestronglyMeasurable.congr <|
    hslice.mono fun t ht => (eLpNorm_congr_ae ht).symm

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

/-
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
    simpa only [J] using nonlin_integrableOn_Icc σ u (-T) T hTint
  have hDend : scalarMixedENorm mu_t volume 4 ⊤
      (curveRepresentative D) < ⊤ := by
    simpa only [D, K, J, mu_t] using
      retarded_endpoint_lt_top (-T) T hTint I hI hsub u.nonlin hnonlin
  have hDmeas : AEStronglyMeasurable D mu_t := by
    have hpair : AEStronglyMeasurable
        (fun z : ℝ × ℝ => (z.2 - z.1, u.nonlin z.1))
        ((volume.restrict J).prod mu_t) :=
      (measurable_snd.sub measurable_fst).aestronglyMeasurable.prodMk
        hnonlin.1.comp_fst
    have hKmeas : AEStronglyMeasurable K
        ((volume.restrict J).prod mu_t) :=
      continuous_freeProp_joint.comp_aestronglyMeasurable hpair
    have hchron : MeasurableSet {z : ℝ × ℝ | -T < z.1 ∧ z.1 ≤ z.2} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_snd)
    exact (hKmeas.indicator hchron).integral_prod_right'
  let W : ℝ → L2 := fun t => freeProp (t + T) (u.u (-T))
  obtain ⟨C, hCtop, hhom⟩ := hom_strichartz
  have hWend : scalarMixedENorm mu_t volume 4 ⊤
      (curveRepresentative W) < ⊤ := by
    have hgroup : W = fun t => freeProp t (freeProp T (u.u (-T))) := by
      funext t
      dsimp [W]
      rw [propagator_unitary.2.2.1]
      congr 1
      ring
    rw [hgroup]
    apply lt_of_le_of_lt _
      ((hhom (freeProp T (u.u (-T)))).trans_lt
        (ENNReal.mul_lt_top hCtop ENNReal.ofReal_ne_top))
    unfold scalarMixedENorm
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hWmeas : AEStronglyMeasurable W mu_t := by
    exact (continuous_freeProp_joint.comp
      ((continuous_id.add continuous_const).prodMk continuous_const)).aestronglyMeasurable
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
    change (∫ s, S.indicator (fun s => freeProp (t - s) (u.nonlin s)) s
        ∂volume.restrict J) = _
    rw [integral_indicator hS, Measure.restrict_restrict_of_subset hSJ]
  have hmild (t : ℝ) (ht : t ∈ I) :
      u.u t = W t - (Complex.I * (σ : ℂ)) • D t := by
    rw [u.mild t (-T), hD_interval t ht]
    rfl
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
    rw [hmild t ht]
    unfold Au Aw Acd sectionENorm curveRepresentative
    apply le_trans (eLpNorm_congr_ae (Lp.coeFn_sub (W t) (c • D t)))
    exact eLpNorm_sub_le (Lp.stronglyMeasurable (W t)).aestronglyMeasurable
      (Lp.stronglyMeasurable (c • D t)).aestronglyMeasurable (by norm_num)
  have huend : eLpNorm Au 4 mu_t < ⊤ := by
    apply lt_of_le_of_lt (eLpNorm_mono_enorm_ae hpoint)
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
    · rw [eLpNorm_congr_enorm_ae]
      · exact huend
      · filter_upwards [hAufin] with t ht
        rw [Real.enorm_eq_ofReal, ENNReal.ofReal_toReal ht.ne]
        exact enorm_eq_self
  · simpa only [Au, mu_t] using hAufin
-/
-/

/-- Measurability of a finite spatial section norm for the two exponents used
below.  Keeping this local avoids imposing a stronger, endpoint-valued
measurability interface on the mixed-norm module. -/
private theorem measurable_section_norm_finite (q : ℝ≥0∞) (hq0 : q ≠ 0)
    (hqtop : q ≠ ⊤)
    (u : ℝ × ℝ → ℂ) (hu : Measurable u) :
    Measurable (fun t => sectionENorm volume q u t) := by
  unfold sectionENorm
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop]
  exact ENNReal.continuous_rpow_const.measurable.comp
    ((hu.enorm.pow_const q.toReal).lintegral_prod_right')

/-- The elementary spatial `L⁴` interpolation inequality. -/
private theorem spatial_interp_endpoint (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 4 volume ≤
      eLpNorm f 2 volume ^ (1 / 2 : ℝ) *
        eLpNorm f ⊤ volume ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_exponent_top]
  norm_num only [ENNReal.toReal_ofNat]
  let B : ℝ≥0∞ := eLpNormEssSup f volume
  have hB : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ B := ae_le_eLpNormEssSup
  have hpow : ∀ᵐ x ∂volume,
      ‖f x‖ₑ ^ (4 : ℝ) ≤ B ^ (2 : ℝ) * ‖f x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hB] with x hx
    have hnat : ‖f x‖ₑ ^ (4 : ℕ) ≤ B ^ (2 : ℕ) * ‖f x‖ₑ ^ (2 : ℕ) := by
      calc
        ‖f x‖ₑ ^ (4 : ℕ) = ‖f x‖ₑ ^ 2 * ‖f x‖ₑ ^ 2 := by ring
        _ ≤ B ^ 2 * ‖f x‖ₑ ^ 2 :=
          mul_le_mul_right' (pow_le_pow_left' hx 2) _
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      ENNReal.rpow_natCast, ENNReal.rpow_natCast, ENNReal.rpow_natCast]
    exact hnat
  calc
    (∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂volume) ^ (1 / (4 : ℝ)) ≤
        (∫⁻ x, B ^ (2 : ℝ) * ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (4 : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) (by positivity)
    _ = (B ^ (2 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (4 : ℝ)) := by
      rw [lintegral_const_mul'' _ (hf.enorm.pow_const 2)]
    _ = B ^ (1 / 2 : ℝ) *
        (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 4 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      norm_num
    _ = ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))) ^
          (1 / 2 : ℝ) * eLpNormEssSup f volume ^ (1 / 2 : ℝ) := by
      have hquarter : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 4 : ℝ) =
          ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)) ^
            (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hquarter]
      dsimp only [B]
      ac_rfl

/-- `lem:interp-L8L4`: scalar endpoint interpolation. -/
theorem interp_L8L4 (I : Set ℝ) (u : ℝ × ℝ → ℂ) (hu : Measurable u) :
  scalarMixedENorm (volume.restrict I) volume 8 4 u ≤
    (scalarMixedENorm (volume.restrict I) volume ⊤ 2 u) ^ (1 / 2 : ℝ) *
    (scalarMixedENorm (volume.restrict I) volume 4 ⊤ u) ^ (1 / 2 : ℝ) := by
  let A : ℝ → ℝ≥0∞ := fun t => sectionENorm volume 2 u t
  let B : ℝ → ℝ≥0∞ := fun t => sectionENorm volume ⊤ u t
  let C : ℝ → ℝ≥0∞ := fun t => sectionENorm volume 4 u t
  have hAmeas : Measurable A :=
    measurable_section_norm_finite 2 (by norm_num) (by norm_num) u hu
  have hBmeas : Measurable B := measurable_esssup_section volume volume u hu
  have hCmeas : Measurable C :=
    measurable_section_norm_finite 4 (by norm_num) (by norm_num) u hu
  have hsection : ∀ t, C t ≤ A t ^ (1 / 2 : ℝ) * B t ^ (1 / 2 : ℝ) := by
    intro t
    exact spatial_interp_endpoint (fun x => u (t, x))
      ((hu.comp measurable_prodMk_left).aestronglyMeasurable)
  rw [scalarMixedENorm, scalarMixedENorm, scalarMixedENorm]
  change eLpNorm C 8 (volume.restrict I) ≤
    eLpNorm A ⊤ (volume.restrict I) ^ (1 / 2 : ℝ) *
      eLpNorm B 4 (volume.restrict I) ^ (1 / 2 : ℝ)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (8 : ℝ≥0∞) ≠ 0)
      (by norm_num : (8 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_exponent_top]
  norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
  have hM : ∀ᵐ t ∂volume.restrict I, A t ≤ eLpNormEssSup A (volume.restrict I) :=
    ae_le_eLpNormEssSup
  have hpow : ∀ᵐ t ∂volume.restrict I,
      C t ^ (8 : ℝ) ≤
        eLpNormEssSup A (volume.restrict I) ^ (4 : ℝ) * B t ^ (4 : ℝ) := by
    filter_upwards [hM] with t ht
    calc
      C t ^ (8 : ℝ) ≤ (A t ^ (1 / 2 : ℝ) * B t ^ (1 / 2 : ℝ)) ^ (8 : ℝ) :=
        ENNReal.rpow_le_rpow (hsection t) (by positivity)
      _ = A t ^ (4 : ℝ) * B t ^ (4 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
      _ ≤ eLpNormEssSup A (volume.restrict I) ^ (4 : ℝ) * B t ^ (4 : ℝ) := by
        gcongr
  calc
    (∫⁻ t, C t ^ (8 : ℝ) ∂volume.restrict I) ^ (1 / (8 : ℝ)) ≤
        (∫⁻ t, eLpNormEssSup A (volume.restrict I) ^ (4 : ℝ) *
          B t ^ (4 : ℝ) ∂volume.restrict I) ^ (1 / (8 : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) (by positivity)
    _ = (eLpNormEssSup A (volume.restrict I) ^ (4 : ℝ) *
          ∫⁻ t, B t ^ (4 : ℝ) ∂volume.restrict I) ^ (1 / (8 : ℝ)) := by
      rw [lintegral_const_mul'' _ ((hBmeas.pow_const 4).aemeasurable.restrict)]
    _ = eLpNormEssSup A (volume.restrict I) ^ (1 / 2 : ℝ) *
          ((∫⁻ t, B t ^ (4 : ℝ) ∂volume.restrict I) ^ (1 / (4 : ℝ))) ^
            (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      have hM' : (eLpNormEssSup A (volume.restrict I) ^ (4 : ℝ)) ^
          (1 / 8 : ℝ) = eLpNormEssSup A (volume.restrict I) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      have hB' : ((∫⁻ t, B t ^ (4 : ℝ) ∂volume.restrict I) ^ (1 / (4 : ℝ))) ^
          (1 / 2 : ℝ) =
          (∫⁻ t, B t ^ (4 : ℝ) ∂volume.restrict I) ^ (1 / 8 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hM', hB']

end CubicNLSPhaseRetrieval
