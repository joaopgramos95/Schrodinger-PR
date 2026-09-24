import Lean_Code.EndpointCompleteness
import Lean_Code.StrichartzDefinitions

/-!
# Identification of endpoint mixed-norm limits

The conclusion is deliberately slice-a.e.: it identifies the jointly
measurable limit with the `L²` free-flow class for almost every time, without
asserting joint measurability of Mathlib's independently chosen `Lp.coeFn`
representatives.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

set_option maxHeartbeats 8000000 in
theorem strichartz_endpoint_identification (f : L2) (fn : ℕ → L2)
    (hfn : Tendsto fn atTop (𝓝 f)) (H : ℝ × ℝ → ℂ)
    (hH : MemScalarMixed volume volume 4 ⊤ H)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      scalarMixedENorm volume volume 4 ⊤
        (fun p => curveRepresentative (fun t => freeProp t (fn n)) p - H p) <
          ENNReal.ofReal ε)
    (C : ℝ≥0∞) (hCtop : C < ⊤)
    (hbound : ∀ n, scalarMixedENorm volume volume 4 ⊤
      (curveRepresentative fun t => freeProp t (fn n)) ≤ C * ENNReal.ofReal ‖fn n‖) :
  (∀ᵐ t : ℝ ∂volume,
      (fun x => H (t, x)) =ᵐ[volume]
        (freeProp t f : ℝ → ℂ)) ∧
    scalarMixedENorm volume volume 4 ⊤
      (curveRepresentative fun t => freeProp t f) ≤ C * ENNReal.ofReal ‖f‖ := by
  let Hm : ℝ × ℝ → ℂ := hH.1.mk H
  have hHmmeas : Measurable Hm := hH.1.stronglyMeasurable_mk.measurable
  have hHae : H =ᵐ[volume.prod volume] Hm := hH.1.ae_eq_mk
  have hHslice : ∀ᵐ t : ℝ ∂volume,
      (fun x => H (t, x)) =ᵐ[volume] fun x => Hm (t, x) :=
    Measure.ae_ae_of_ae_prod hHae
  let W : ℕ → ℝ × ℝ → ℂ := fun n =>
    Classical.choose (joint_representative_L2_measurable volume
      (fun t => freeProp t (fn n))
      ((propagator_unitary.2.2.2.1 (fn n))).aestronglyMeasurable)
  have hWmeas (n : ℕ) : Measurable (W n) :=
    (Classical.choose_spec (joint_representative_L2_measurable volume
      (fun t => freeProp t (fn n))
      ((propagator_unitary.2.2.2.1 (fn n))).aestronglyMeasurable)).1
  have hWslice (n : ℕ) : ∀ᵐ t : ℝ ∂volume,
      (fun x => W n (t, x)) =ᵐ[volume]
        (freeProp t (fn n) : ℝ → ℂ) :=
    (Classical.choose_spec (joint_representative_L2_measurable volume
      (fun t => freeProp t (fn n))
      ((propagator_unitary.2.2.2.1 (fn n))).aestronglyMeasurable)).2
  have hsingle (n : ℕ) :
      scalarMixedENorm volume volume 4 ⊤ (W n) =
        scalarMixedENorm volume volume 4 ⊤
          (curveRepresentative fun t => freeProp t (fn n)) := by
    unfold scalarMixedENorm sectionENorm
    apply eLpNorm_congr_ae
    filter_upwards [hWslice n] with t ht
    exact eLpNorm_congr_ae ht
  have hdiff (n : ℕ) :
      scalarMixedENorm volume volume 4 ⊤ (fun z => W n z - Hm z) =
        scalarMixedENorm volume volume 4 ⊤
          (fun p => curveRepresentative (fun t => freeProp t (fn n)) p - H p) := by
    unfold scalarMixedENorm sectionENorm
    apply eLpNorm_congr_ae
    filter_upwards [hWslice n, hHslice] with t hwt hht
    apply eLpNorm_congr_ae
    filter_upwards [hwt, hht] with x hwx hhx
    simp only [curveRepresentative, hwx, hhx]
  let D : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    sectionENorm volume ⊤ (fun z => W n z - Hm z) t
  have hDmeas (n : ℕ) : Measurable (D n) :=
    measurable_esssup_section volume volume _ ((hWmeas n).sub hHmmeas)
  have hDtend : Tendsto (fun n => eLpNorm (D n) 4 volume) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · subst ε
      exact Filter.Eventually.of_forall fun _ => le_top
    · have hδ : 0 < ε.toReal / 2 := half_pos (ENNReal.toReal_pos hε.ne' hεtop)
      obtain ⟨N, hN⟩ := hconv (ε.toReal / 2) hδ
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' := (hN n hn).le
      change eLpNorm (D n) 4 volume ≤ ε
      calc
        eLpNorm (D n) 4 volume =
            scalarMixedENorm volume volume 4 ⊤ (fun z => W n z - Hm z) := rfl
        _ = scalarMixedENorm volume volume 4 ⊤
            (fun p => curveRepresentative (fun t => freeProp t (fn n)) p - H p) := hdiff n
        _ ≤ ENNReal.ofReal (ε.toReal / 2) := hn'
        _ ≤ ε := by
          calc
            ENNReal.ofReal (ε.toReal / 2) ≤ ENNReal.ofReal ε.toReal :=
              ENNReal.ofReal_le_ofReal (half_le_self ENNReal.toReal_nonneg)
            _ = ε := ENNReal.ofReal_toReal hεtop
  have hDnormtop (n : ℕ) : eLpNorm (D n) 4 volume < ⊤ := by
    obtain ⟨N, hN⟩ := hconv 1 (by norm_num)
    by_cases hn : N ≤ n
    · change eLpNorm (D n) 4 volume < ⊤
      rw [show eLpNorm (D n) 4 volume =
        scalarMixedENorm volume volume 4 ⊤ (fun z => W n z - Hm z) by rfl,
        hdiff n]
      exact (hN n hn).trans (by norm_num)
    · have hWtop : scalarMixedENorm volume volume 4 ⊤ (W n) < ⊤ := by
        rw [hsingle n]
        exact (hbound n).trans_lt (ENNReal.mul_lt_top hCtop (by finiteness))
      have hHmtop : scalarMixedENorm volume volume 4 ⊤ Hm < ⊤ := by
        have heq : scalarMixedENorm volume volume 4 ⊤ Hm =
            scalarMixedENorm volume volume 4 ⊤ H := by
          unfold scalarMixedENorm sectionENorm
          apply eLpNorm_congr_ae
          filter_upwards [hHslice] with t ht
          exact eLpNorm_congr_ae ht.symm
        rw [heq]
        exact hH.2
      have htri := scalarMixedENorm_sub_le_add volume volume 4 (by norm_num)
        (W n) Hm 0 (hWmeas n) hHmmeas measurable_zero
      have hneg : scalarMixedENorm volume volume 4 ⊤ (fun z => -Hm z) =
          scalarMixedENorm volume volume 4 ⊤ Hm := by
        unfold scalarMixedENorm sectionENorm
        apply eLpNorm_congr_ae
        filter_upwards with t
        exact eLpNorm_neg _ _ _
      exact (show eLpNorm (D n) 4 volume < ⊤ by
        change scalarMixedENorm volume volume 4 ⊤ (fun z => W n z - Hm z) < ⊤
        exact htri.trans_lt (by
          simpa only [Pi.zero_apply, sub_zero, zero_sub, hneg] using
            ENNReal.add_lt_top.2 ⟨hWtop, hHmtop⟩))
  have hDfinite (n : ℕ) : ∀ᵐ t : ℝ ∂volume, D n t ≠ ⊤ := by
    have hlin : (∫⁻ t, D n t ^ (4 : ℝ) ∂volume) < ⊤ := by
      rw [← ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
        ENNReal.toReal_ofNat, enorm_eq_self] using hDnormtop n
    have hpow : ∀ᵐ t : ℝ ∂volume, D n t ^ (4 : ℝ) < ⊤ :=
      ae_lt_top' ((hDmeas n).pow_const 4).aemeasurable hlin.ne
    filter_upwards [hpow] with t ht
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at ht
    exact lt_irrefl ⊤ ht
  let Dr : ℕ → ℝ → ℝ := fun n t => (D n t).toReal
  have hDrmeas (n : ℕ) : AEStronglyMeasurable (Dr n) volume :=
    (hDmeas n).ennreal_toReal.aestronglyMeasurable
  have hDrnorm (n : ℕ) : eLpNorm (Dr n) 4 volume = eLpNorm (D n) 4 volume := by
    apply eLpNorm_congr_enorm_ae
    filter_upwards [hDfinite n] with t ht
    simpa only [enorm_eq_self] using Real.enorm_toReal ht
  have hDrtend : Tendsto (fun n => eLpNorm (Dr n - 0) 4 volume) atTop (𝓝 0) := by
    convert hDtend using 1
    funext n
    simpa only [Pi.sub_apply, sub_zero] using hDrnorm n
  have hDrMeasure : TendstoInMeasure volume Dr atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (4 : ℝ≥0∞)) (by norm_num)
      hDrmeas aestronglyMeasurable_zero hDrtend
  obtain ⟨ns, hns, hDrAE⟩ := hDrMeasure.exists_seq_tendsto_ae'
  have hsliceHm : ∀ᵐ t : ℝ ∂volume,
      (fun x => Hm (t, x)) =ᵐ[volume] (freeProp t f : ℝ → ℂ) := by
    have hallfinite : ∀ᵐ t : ℝ ∂volume, ∀ n, D n t ≠ ⊤ :=
      ae_all_iff.2 hDfinite
    have hWall : ∀ᵐ t : ℝ ∂volume, ∀ n,
        (fun x => W n (t, x)) =ᵐ[volume]
          (freeProp t (fn n) : ℝ → ℂ) := ae_all_iff.2 hWslice
    filter_upwards [hDrAE, hallfinite, hWall] with t hDt hfin hWt
    have hDto0 : Tendsto (fun k => D (ns k) t) atTop (𝓝 0) := by
      apply (ENNReal.tendsto_toReal_iff (fun k => hfin (ns k)) ENNReal.zero_ne_top).mp
      simpa only [Dr, ENNReal.toReal_zero] using hDt
    have hspaceH : TendstoInMeasure volume
        (fun k x => W (ns k) (t, x)) atTop (fun x => Hm (t, x)) := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := (⊤ : ℝ≥0∞)) (by simp)
      · intro k
        exact ((hWmeas (ns k)).comp measurable_prodMk_left).aestronglyMeasurable
      · exact (hHmmeas.comp measurable_prodMk_left).aestronglyMeasurable
      · change Tendsto (fun k => eLpNorm
            (fun x => W (ns k) (t, x) - Hm (t, x)) ⊤ volume) atTop (𝓝 0)
        simpa only [D, sectionENorm] using hDto0
    have hflow : Tendsto (fun k => freeProp t (fn (ns k))) atTop
        (𝓝 (freeProp t f)) := by
      have hcont : Continuous (fun g : L2 => freeProp t g) :=
        continuous_freeProp_joint.comp (continuous_const.prodMk continuous_id)
      exact hcont.continuousAt.tendsto.comp (hfn.comp hns)
    have hspacef : TendstoInMeasure volume
        (fun k => (freeProp t (fn (ns k)) : ℝ → ℂ)) atTop
        (freeProp t f : ℝ → ℂ) :=
      tendstoInMeasure_of_tendsto_Lp hflow
    have hWcanonical : ∀ k, (fun x => W (ns k) (t, x)) =ᵐ[volume]
        (freeProp t (fn (ns k)) : ℝ → ℂ) := by
      intro k
      exact hWt (ns k)
    have hspacefW : TendstoInMeasure volume
        (fun k x => W (ns k) (t, x)) atTop
        (freeProp t f : ℝ → ℂ) :=
      hspacef.congr (fun k => (hWcanonical k).symm) EventuallyEq.rfl
    exact tendstoInMeasure_ae_unique hspaceH hspacefW
  constructor
  · filter_upwards [hHslice, hsliceHm] with t hHt hmt
    exact hHt.trans hmt
  · have hcanonicalHm : scalarMixedENorm volume volume 4 ⊤
        (curveRepresentative fun t => freeProp t f) =
        scalarMixedENorm volume volume 4 ⊤ Hm := by
      unfold scalarMixedENorm sectionENorm
      apply eLpNorm_congr_ae
      filter_upwards [hsliceHm] with t ht
      exact eLpNorm_congr_ae ht.symm
    rw [hcanonicalHm]
    have hHmH : scalarMixedENorm volume volume 4 ⊤ Hm =
        scalarMixedENorm volume volume 4 ⊤ H := by
      unfold scalarMixedENorm sectionENorm
      apply eLpNorm_congr_ae
      filter_upwards [hHslice] with t ht
      exact eLpNorm_congr_ae ht.symm
    have hdiffneg (n : ℕ) : scalarMixedENorm volume volume 4 ⊤
          (fun z => Hm z - W n z) = eLpNorm (D n) 4 volume := by
      change scalarMixedENorm volume volume 4 ⊤ (fun z => Hm z - W n z) =
        scalarMixedENorm volume volume 4 ⊤ (fun z => W n z - Hm z)
      unfold scalarMixedENorm sectionENorm
      apply eLpNorm_congr_ae
      filter_upwards with t
      rw [show (fun x => Hm (t, x) - W n (t, x)) =
          -(fun x => W n (t, x) - Hm (t, x)) by funext x; simp]
      exact eLpNorm_neg _ _ _
    have htri (n : ℕ) : scalarMixedENorm volume volume 4 ⊤ Hm ≤
        eLpNorm (D n) 4 volume + C * ENNReal.ofReal ‖fn n‖ := by
      have ht := scalarMixedENorm_sub_le_add volume volume 4 (by norm_num)
        Hm 0 (W n) hHmmeas measurable_zero (hWmeas n)
      have ht' : scalarMixedENorm volume volume 4 ⊤ Hm ≤
          eLpNorm (D n) 4 volume +
            scalarMixedENorm volume volume 4 ⊤ (W n) := by
        simpa only [Pi.zero_apply, sub_zero, hdiffneg n] using ht
      have hWbound : scalarMixedENorm volume volume 4 ⊤ (W n) ≤
          C * ENNReal.ofReal ‖fn n‖ := by
        rw [hsingle n]
        exact hbound n
      exact ht'.trans (add_le_add_right hWbound _)
    have hnormtend : Tendsto (fun n => C * ENNReal.ofReal ‖fn n‖) atTop
        (𝓝 (C * ENNReal.ofReal ‖f‖)) := by
      exact (ENNReal.continuous_const_mul hCtop.ne).continuousAt.tendsto.comp
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hfn.norm)
    exact ge_of_tendsto' (by simpa using hDtend.add hnormtend) htri

end CubicNLSPhaseRetrieval
