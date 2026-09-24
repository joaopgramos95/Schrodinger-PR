import Lean_Code.CarlemanFourier2D

/-!
# Joint representatives for measurable `L²` paths

This is the measure-generic version of the one-dimensional construction in
`ScalarMixedNorms`.  It is used for the two-dimensional frequency sections in
the Carleman closure.
-/

open Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

private theorem measurable_simpleFunc_L2_coe_generic
    {I X : Type*} [MeasurableSpace I] [MeasurableSpace X]
    (nu : Measure X)
    (s : SimpleFunc I (Lp ℂ 2 nu)) :
    Measurable (fun p : I × X => (s p.1 : X → ℂ) p.2) := by
  classical
  induction s using SimpleFunc.induction' with
  | const c =>
      exact (Lp.stronglyMeasurable c).measurable.comp measurable_snd
  | @pcw f g A hA hf hg =>
      classical
      have heq : (fun p : I × X =>
          ((SimpleFunc.piecewise A hA f g) p.1 : X → ℂ) p.2) =
          fun p => if p.1 ∈ A then (f p.1 : X → ℂ) p.2
            else (g p.1 : X → ℂ) p.2 := by
        funext p
        by_cases hp : p.1 ∈ A <;>
          simp [SimpleFunc.coe_piecewise, Set.piecewise, hp]
      rw [heq]
      exact hf.ite (hA.preimage measurable_fst) hg

/-- A strongly measurable path in an arbitrary scalar `L²` space has a
jointly measurable representative, with the prescribed slice at every
parameter. -/
theorem joint_representative_L2_measurable_strong_generic
    {I X : Type*} [MeasurableSpace I] [MeasurableSpace X]
    (mu : Measure I) (nu : Measure X) (u : I → Lp ℂ 2 nu)
    (humeas : StronglyMeasurable u) :
    ∃ U : I × X → ℂ,
      Measurable U ∧ ∀ t : I, (fun x => U (t, x)) =ᵐ[nu] (u t : X → ℂ) := by
  let g : I → Lp ℂ 2 nu := u
  have hg : StronglyMeasurable g := by simpa only [g] using humeas
  let s : ℕ → SimpleFunc I (Lp ℂ 2 nu) := hg.approx
  have hs_tendsto (t : I) : Tendsto (fun n => s n t) atTop (𝓝 (g t)) :=
    hg.tendsto_approx t
  let ε : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  let P : ℕ → ℕ → I → Prop := fun k n t => dist (s n t) (g t) < ε k
  have hPmeas (k n : ℕ) : MeasurableSet {t | P k n t} := by
    change MeasurableSet {t | dist (s n t) (g t) < ε k}
    exact measurableSet_lt ((s n).stronglyMeasurable.dist hg).measurable measurable_const
  have hPexists (k : ℕ) (t : I) : ∃ n, P k n t := by
    have hevent : ∀ᶠ n in atTop, dist (s n t) (g t) < ε k :=
      (tendsto_order.1 (tendsto_iff_dist_tendsto_zero.mp (hs_tendsto t))).2
        _ (hεpos k)
    exact hevent.exists
  let pick (k : ℕ) (t : I) : ℕ := Nat.find (hPexists k t)
  let v (k : ℕ) (t : I) : Lp ℂ 2 nu := s (pick k t) t
  have hv_close (k : ℕ) (t : I) : dist (v k t) (g t) < ε k :=
    Nat.find_spec (hPexists k t)
  let V (k : ℕ) (p : I × X) : ℂ := (v k p.1 : X → ℂ) p.2
  have hV_meas (k : ℕ) : Measurable (V k) := by
    change Measurable fun p : I × X =>
      (s (Nat.find (hPexists k p.1)) p.1 : X → ℂ) p.2
    exact Measurable.find
      (fun n => measurable_simpleFunc_L2_coe_generic nu (s n))
      (fun n => (hPmeas k n).preimage measurable_fst)
      (fun p => hPexists k p.1)
  let d (k : ℕ) (t : I) : Lp ℂ 2 nu := v (k + 1) t - v k t
  let D (k : ℕ) (p : I × X) : ℂ := V (k + 1) p - V k p
  have hD_meas (k : ℕ) : Measurable (D k) := (hV_meas (k + 1)).sub (hV_meas k)
  have hd_norm (k : ℕ) (t : I) : ‖d k t‖ ≤ ε (k + 1) + ε k := by
    calc
      ‖d k t‖ = dist (v (k + 1) t) (v k t) := by simp [d, dist_eq_norm]
      _ ≤ dist (v (k + 1) t) (g t) + dist (v k t) (g t) :=
        dist_triangle_right _ _ _
      _ ≤ ε (k + 1) + ε k := add_le_add (hv_close (k + 1) t).le (hv_close k t).le
  have hmajor : Summable (fun k => ε (k + 1) + ε k) := by
    have hshift : Summable (fun k : ℕ => ε (k + 1)) := by
      simpa [ε, pow_succ, mul_comm] using
        summable_geometric_two.mul_left (1 / 2 : ℝ)
    exact hshift.add (by simpa [ε] using summable_geometric_two)
  have hd_norm_summable (t : I) : Summable (fun k => ‖d k t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hd_norm k t) hmajor
  have hd_summable (t : I) : Summable (d · t) := (hd_norm_summable t).of_norm
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (x := (1 / 2 : ℝ)) (by norm_num))
  have hv_tendsto (t : I) : Tendsto (fun k => v k t) atTop (𝓝 (g t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg)
      (fun k => (hv_close k t).le) hε_tendsto
  have hd_hasSum (t : I) : HasSum (d · t) (g t - v 0 t) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm (hd_norm_summable t)).2
    have htel : (fun n => ∑ k ∈ Finset.range n, d k t) =
        fun n => v n t - v 0 t := by
      funext n
      simpa only [d] using Finset.sum_range_sub (fun k => v k t) n
    rw [htel]
    exact (hv_tendsto t).sub_const (v 0 t)
  have hd_tsum (t : I) : ∑' k, d k t = g t - v 0 t := (hd_hasSum t).tsum_eq
  let U : I × X → ℂ := fun p => V 0 p + ∑' k, D k p
  have hUmeas : Measurable U := (hV_meas 0).add (Measurable.tsum hD_meas)
  refine ⟨U, hUmeas, fun t => ?_⟩
  have hdenorm : ∑' k, ‖d k t‖ₑ ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (hd_norm_summable t)
  have hcoe := Lp.coeFn_tsum hdenorm
  have hterms : ∀ᵐ x ∂nu, ∀ k : ℕ, (d k t : X → ℂ) x = D k (t, x) := by
    apply ae_all_iff.2
    intro k
    exact (Lp.coeFn_sub (v (k + 1) t) (v k t)).mono fun x hx => by
      simpa only [d, D, V, Pi.sub_apply] using hx
  have hgdecomp : g t = v 0 t + ∑' k, d k t := by
    rw [hd_tsum]
    abel
  have hsumcoe :
      (g t : X → ℂ) =ᵐ[nu] fun x => V 0 (t, x) + ∑' k, D k (t, x) := by
    rw [hgdecomp]
    filter_upwards [Lp.coeFn_add (v 0 t) (∑' k, d k t), hcoe, hterms]
      with x hadd hseries hterm
    simp only [Pi.add_apply] at hadd ⊢
    rw [hadd, hseries]
    congr 1
    apply tsum_congr
    exact hterm
  simpa only [U, g] using hsumcoe.symm

/-- AE-strongly-measurable wrapper for the generic joint representative. -/
theorem joint_representative_L2_measurable_generic
    {I X : Type*} [MeasurableSpace I] [MeasurableSpace X]
    (mu : Measure I) (nu : Measure X) (u : I → Lp ℂ 2 nu)
    (humeas : AEStronglyMeasurable u mu) :
    ∃ U : I × X → ℂ,
      Measurable U ∧
        ∀ᵐ t ∂mu, (fun x => U (t, x)) =ᵐ[nu] (u t : X → ℂ) := by
  let g : I → Lp ℂ 2 nu := humeas.mk u
  obtain ⟨U, hU, hslice⟩ :=
    joint_representative_L2_measurable_strong_generic mu nu g
      humeas.stronglyMeasurable_mk
  refine ⟨U, hU, ?_⟩
  filter_upwards [humeas.ae_eq_mk] with t ht
  exact (hslice t).trans (Filter.Eventually.of_forall fun x => by
    have hx := congrArg (fun z : Lp ℂ 2 nu => (z : X → ℂ) x) ht.symm
    simpa only [g] using hx)

end CubicNLSPhaseRetrieval
