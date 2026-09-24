import Lean_Code.CarlemanL2

/-! Measurable currying of raw spacetime fields into spatial `L²`. -/

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

private lemma eLpNorm_two_section_measurable (F : Spacetime2)
    (hF : Measurable F) :
    Measurable (fun t => eLpNorm (fun z => F (t, z)) 2
      (volume.prod volume)) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
  exact ((hF.enorm.pow_const _).lintegral_prod_right').pow_const _

private lemma measurable_section_memLp (F : Spacetime2) (hF : Measurable F)
    (t : ℝ) (ht : eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤) :
    MemLp (fun z => F (t, z)) 2 (volume.prod volume) := by
  exact ⟨(hF.comp measurable_prodMk_left).aestronglyMeasurable, ht⟩

def spacetimeSectionL2 (F : Spacetime2) (hF : Measurable F) (t : ℝ) :
    SpatialL2Two :=
  if ht : eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤ then
    MemLp.toLp (fun z => F (t, z)) (measurable_section_memLp F hF t ht)
  else 0

theorem spacetimeSectionL2_coe_ae (F : Spacetime2) (hF : Measurable F)
    (t : ℝ) (ht : eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤) :
    (spacetimeSectionL2 F hF t : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun z => F (t, z) := by
  rw [spacetimeSectionL2, dif_pos ht]
  exact MemLp.coeFn_toLp _

theorem enorm_spacetimeSectionL2 (F : Spacetime2) (hF : Measurable F)
    (t : ℝ) (ht : eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤) :
    ‖spacetimeSectionL2 F hF t‖ₑ =
      eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae (spacetimeSectionL2_coe_ae F hF t ht)

private lemma eLpNorm_two_section_sub_measurable (F : Spacetime2)
    (hF : Measurable F) (q : SpatialL2Two) :
    Measurable (fun t => eLpNorm
      (fun z => F (t, z) - (q : ℝ × ℝ → ℂ) z) 2
      (volume.prod volume)) := by
  have hjoint : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      F p - (q : ℝ × ℝ → ℂ) p.2) :=
    hF.sub ((Lp.stronglyMeasurable q).measurable.comp measurable_snd)
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
  exact ((hjoint.enorm.pow_const _).lintegral_prod_right').pow_const _

private lemma dist_spacetimeSectionL2 (F : Spacetime2) (hF : Measurable F)
    (q : SpatialL2Two) (t : ℝ) :
    dist (spacetimeSectionL2 F hF t) q =
      if eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤ then
        (eLpNorm (fun z => F (t, z) - (q : ℝ × ℝ → ℂ) z) 2
          (volume.prod volume)).toReal
      else dist 0 q := by
  by_cases ht : eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤
  · rw [if_pos ht, dist_eq_norm, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (spacetimeSectionL2 F hF t) q,
      spacetimeSectionL2_coe_ae F hF t ht] with z hsub hsec
    rw [hsub, Pi.sub_apply, hsec]
  · rw [if_neg ht]
    simp [spacetimeSectionL2, ht]

private lemma measurable_dist_spacetimeSectionL2 (F : Spacetime2)
    (hF : Measurable F) (q : SpatialL2Two) :
    Measurable (fun t => dist (spacetimeSectionL2 F hF t) q) := by
  rw [show (fun t => dist (spacetimeSectionL2 F hF t) q) = fun t =>
      if eLpNorm (fun z => F (t, z)) 2 (volume.prod volume) < ⊤ then
        (eLpNorm (fun z => F (t, z) - (q : ℝ × ℝ → ℂ) z) 2
          (volume.prod volume)).toReal
      else dist 0 q by
    funext t
    exact dist_spacetimeSectionL2 F hF q t]
  apply Measurable.ite
  · exact measurableSet_lt (eLpNorm_two_section_measurable F hF) measurable_const
  · exact (eLpNorm_two_section_sub_measurable F hF q).ennreal_toReal
  · exact measurable_const

theorem spacetimeSectionL2_stronglyMeasurable (F : Spacetime2)
    (hF : Measurable F) : StronglyMeasurable (spacetimeSectionL2 F hF) := by
  letI : MeasurableSpace SpatialL2Two := borel SpatialL2Two
  haveI : BorelSpace SpatialL2Two := ⟨rfl⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let d : ℕ → SpatialL2Two := denseSeq SpatialL2Two
  have hd : DenseRange d := by simpa only [d] using denseRange_denseSeq SpatialL2Two
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let P : ℕ → ℝ → ℕ → Prop := fun n t k =>
    dist (spacetimeSectionL2 F hF t) (d k) < ε n
  have hPmeas (n k : ℕ) : MeasurableSet {t | P n t k} := by
    exact measurableSet_lt (measurable_dist_spacetimeSectionL2 F hF (d k)) measurable_const
  have hPexists (n : ℕ) (t : ℝ) : ∃ k, P n t k := by
    exact hd.exists_dist_lt (spacetimeSectionL2 F hF t) (hεpos n)
  let a : ℕ → ℝ → SpatialL2Two := fun n t => d (Nat.find (hPexists n t))
  have hameas (n : ℕ) : Measurable (a n) := by
    exact Measurable.find (fun _ => measurable_const) (hPmeas n) (hPexists n)
  have ha_close (n : ℕ) (t : ℝ) :
      dist (a n t) (spacetimeSectionL2 F hF t) < ε n := by
    rw [dist_comm]
    exact Nat.find_spec (hPexists n t)
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have halim : Tendsto a atTop (𝓝 (spacetimeSectionL2 F hF)) := by
    rw [tendsto_pi_nhds]
    intro t
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (ha_close n t).le) hεzero
  exact (measurable_of_tendsto_metrizable hameas halim).stronglyMeasurable

end CubicNLSPhaseRetrieval
