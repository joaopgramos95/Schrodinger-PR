import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Banach-valued fundamental theorem for absolutely continuous curves

Mathlib's absolutely-continuous primitive theorem is currently specialized to
real-valued integrands.  The proof below is the same argument with the Bochner
norm and is used to differentiate the interaction-picture tensor curve.
-/

open Filter MeasureTheory Set

noncomputable section

namespace CubicNLSPhaseRetrieval

theorem absolutelyContinuousOnInterval_const
    {E : Type*} [PseudoMetricSpace E] (c : E) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  unfold AbsolutelyContinuousOnInterval
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0 : ℝ))
    (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (nhds 0))

theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b c : ℝ} (h : IntervalIntegrable f volume a b)
    (hc : c ∈ Set.uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, f v) a b := by
  let s := fun P : ℕ × (ℕ → ℝ × ℝ) =>
    ⋃ i ∈ Finset.range P.1, Set.uIoc (P.2 i).1 (P.2 i).2
  have hlin : Tendsto
      (fun P => ∫⁻ x in s P, ‖f x‖ₑ ∂volume.restrict (Set.uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (nhds 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        _ _)
  have hreal := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlin
  refine squeeze_zero' ?_ ?_ hreal
  · filter_upwards with P
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  simp only [Function.comp_apply, s]
  have hdisj : ∀ᶠ P : ℕ × (ℕ → ℝ × ℝ) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      P ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hdisj] with P hP
  rcases P with ⟨n, I⟩
  obtain ⟨hPI, hpairwise⟩ := Set.mem_setOf_eq ▸ hP
  simp only
  rw [← integral_norm_eq_lintegral_enorm
      (h.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [Set.uIoc]) hpairwise]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by apply IntervalIntegrable.mono_set' h; grind [Set.uIoc, Set.uIcc])
        (by apply IntervalIntegrable.mono_set' h; grind [Set.uIoc, Set.uIcc]),
      Measure.restrict_restrict_of_subset
        (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hP
          (Finset.mem_range.mp hi)),
      intervalIntegral.integral_symm, norm_neg,
      intervalIntegral.norm_intervalIntegral_eq]
    exact norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have hsubset :=
      AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hP
        (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact IntegrableOn.mono_set h.def'.norm hsubset |>.integrable

theorem AbsolutelyContinuousOnInterval.comp_continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (L : E →L[ℝ] F) :
    AbsolutelyContinuousOnInterval (fun t => L (f t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  refine squeeze_zero' ?_ ?_ (by simpa using hf.const_mul ‖L‖)
  · exact Filter.Eventually.of_forall fun _ =>
      Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · filter_upwards with P
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact L.le_opNorm _

/-- A continuous bilinear map sends two absolutely continuous curves to an
absolutely continuous curve. -/
theorem AbsolutelyContinuousOnInterval.clm_apply
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → E} {g : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (B : E →L[ℝ] F →L[ℝ] G) :
    AbsolutelyContinuousOnInterval (fun t => B (f t) (g t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  have hC0 : 0 ≤ C := (norm_nonneg (f a)).trans (hC a Set.left_mem_uIcc)
  have hD0 : 0 ≤ D := (norm_nonneg (g a)).trans (hD a Set.left_mem_uIcc)
  unfold AbsolutelyContinuousOnInterval at hf hg ⊢
  let A : ℝ := ‖B‖ * C
  let K : ℝ := ‖B‖ * D
  refine squeeze_zero' ?_ ?_
    (by simpa [A, K] using (hg.const_mul A).add (hf.const_mul K))
  · exact Filter.Eventually.of_forall fun _ =>
      Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · rw [eventually_inf_principal]
    filter_upwards with P hP
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hleft : (P.2 i).1 ∈ Set.uIcc a b :=
      (hP.1 i hi).1
    have hright : (P.2 i).2 ∈ Set.uIcc a b :=
      (hP.1 i hi).2
    calc
      dist (B (f (P.2 i).1) (g (P.2 i).1))
          (B (f (P.2 i).2) (g (P.2 i).2)) ≤
          dist (B (f (P.2 i).1) (g (P.2 i).1))
              (B (f (P.2 i).1) (g (P.2 i).2)) +
            dist (B (f (P.2 i).1) (g (P.2 i).2))
              (B (f (P.2 i).2) (g (P.2 i).2)) := dist_triangle _ _ _
      _ ≤ A * dist (g (P.2 i).1) (g (P.2 i).2) +
          K * dist (f (P.2 i).1) (f (P.2 i).2) := by
        dsimp [A, K]
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm,
          ← (B (f (P.2 i).1)).map_sub]
        have hBsub :
            B (f (P.2 i).1) (g (P.2 i).2) -
                B (f (P.2 i).2) (g (P.2 i).2) =
              B (f (P.2 i).1 - f (P.2 i).2) (g (P.2 i).2) := by
          exact congrArg (fun L : F →L[ℝ] G => L (g (P.2 i).2))
            (B.map_sub (f (P.2 i).1) (f (P.2 i).2)).symm
        rw [hBsub]
        apply add_le_add
        · calc
            ‖B (f (P.2 i).1) (g (P.2 i).1 - g (P.2 i).2)‖ ≤
                ‖B (f (P.2 i).1)‖ * ‖g (P.2 i).1 - g (P.2 i).2‖ :=
              (B (f (P.2 i).1)).le_opNorm _
            _ ≤ (‖B‖ * C) * ‖g (P.2 i).1 - g (P.2 i).2‖ := by
              gcongr
              exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
                (hC _ hleft) (norm_nonneg B))
        · calc
            ‖B (f (P.2 i).1 - f (P.2 i).2) (g (P.2 i).2)‖ ≤
                ‖B (f (P.2 i).1 - f (P.2 i).2)‖ * ‖g (P.2 i).2‖ :=
              (B (f (P.2 i).1 - f (P.2 i).2)).le_opNorm _
            _ ≤ (‖B‖ * ‖f (P.2 i).1 - f (P.2 i).2‖) * D := by
              exact mul_le_mul (B.le_opNorm _) (hD _ hright)
                (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg _))
            _ = (‖B‖ * D) * ‖f (P.2 i).1 - f (P.2 i).2‖ := by ring

theorem AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : IntervalIntegrable f' volume a b)
    (hderiv : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt f (f' x) x) :
    (∫ x in a..b, f' x) = f b - f a := by
  let G : ℝ → E := fun x => ∫ t in a..x, f' t
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_apply hf'
      (Set.left_mem_uIcc)
  have hGderiv : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt G (f' x) x := by
    filter_upwards [hf'.ae_hasDerivAt_integral] with x hx hxu
    exact hx hxu a (Set.left_mem_uIcc)
  let H : ℝ → E := fun x => f x - G x
  have hHac : AbsolutelyContinuousOnInterval H a b := hf.sub hGac
  have hHzero : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt H 0 x := by
    filter_upwards [hderiv, hGderiv] with x hfx hGx hx
    change HasDerivAt (f - G) 0 x
    simpa using (hfx hx).sub (hGx hx)
  obtain ⟨C, hC⟩ := hHac.const_of_ae_hasDerivAt_zero hHzero
  have ha := hC a Set.left_mem_uIcc
  have hb := hC b Set.right_mem_uIcc
  have hGa : G a = 0 := by simp [G]
  have hGb : G b = ∫ x in a..b, f' x := rfl
  dsimp [H] at ha hb
  rw [hGa, sub_zero] at ha
  rw [hGb] at hb
  rw [← ha] at hb
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact (sub_eq_iff_eq_add.mp hb).symm

end CubicNLSPhaseRetrieval
