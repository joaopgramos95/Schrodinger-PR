import Lean_Code.CommonCurrent
import Lean_Code.HsPairingPhysical

/-!
# Weak convergence at the critical derivative

A uniformly `H^{1/2}`-bounded sequence which converges in physical `L²`
converges against the distributional derivative of any fixed critical
function.  The proof uses the strong translation-difference-quotient
approximation of the derivative.  For every nonzero step the quotient is an
actual `L²` function, where the assertion is just continuity of the
`L² × L² → L¹` product.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

private noncomputable def criticalQuotient (h : ℝ) :
    Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)) :=
  (Classical.choose (Classical.choose_spec translation_dq)) h

private lemma criticalQuotient_toTempered (h : ℝ) (hh : h ≠ 0)
    (f : Hs (1 / 2 : ℝ)) :
    Hs.toTempered (-(1 / 2 : ℝ)) (criticalQuotient h f) =
      MeasureTheory.Lp.toTemperedDistribution
        (((h : ℂ)⁻¹) •
          (translateL2 h (Hs.toL2 (by norm_num) f) -
            Hs.toL2 (by norm_num) f)) := by
  exact (Classical.choose_spec (Classical.choose_spec translation_dq)).2.1 h hh f

private lemma criticalQuotient_tendsto (f : Hs (1 / 2 : ℝ)) :
    Tendsto (fun h : ℝ => criticalQuotient h f)
      (nhdsWithin 0 {0}ᶜ) (nhds (criticalDerivative f)) := by
  exact (Classical.choose_spec (Classical.choose_spec translation_dq)).2.2.1 f

private lemma criticalQuotient_eq_hsNegOfL2 (h : ℝ) (hh : h ≠ 0)
    (f : Hs (1 / 2 : ℝ)) :
    criticalQuotient h f =
      hsNegOfL2 (((h : ℂ)⁻¹ •
        (translateL2 h (Hs.toL2 (by norm_num) f) -
          Hs.toL2 (by norm_num) f))) := by
  apply Hs.toTempered_injective (-(1 / 2 : ℝ))
  rw [criticalQuotient_toTempered h hh f, hsNegOfL2_toTempered]

private lemma quotient_pairing_tendsto_of_toL2
    (h : ℝ) (hh : h ≠ 0) (f q : Hs (1 / 2 : ℝ))
    (qseq : ℕ → Hs (1 / 2 : ℝ))
    (hq : Tendsto (fun n => Hs.toL2 (by norm_num) (qseq n))
      atTop (nhds (Hs.toL2 (by norm_num) q))) :
    Tendsto (fun n => criticalPairingCLM (criticalQuotient h f) (qseq n))
      atTop (nhds (criticalPairingCLM (criticalQuotient h f) q)) := by
  let p : L2 := ((h : ℂ)⁻¹ •
    (translateL2 h (Hs.toL2 (by norm_num) f) -
      Hs.toL2 (by norm_num) f))
  have hprod : Tendsto
      (fun n => densityProductCLM p (Hs.toL2 (by norm_num) (qseq n)))
      atTop (nhds (densityProductCLM p (Hs.toL2 (by norm_num) q))) :=
    (densityProductCLM p).continuous.continuousAt.tendsto.comp hq
  have hint := (MeasureTheory.L1.integralCLM (E := ℂ)).continuous.continuousAt.tendsto.comp hprod
  have hform (r : Hs (1 / 2 : ℝ)) :
      criticalPairingCLM (criticalQuotient h f) r =
        MeasureTheory.L1.integral (densityProductCLM p
          (Hs.toL2 (by norm_num) r)) := by
    rw [criticalQuotient_eq_hsNegOfL2 h hh f]
    change hsNegPairing (hsNegOfL2 p) r = _
    rw [hsNegPairing_hsNegOfL2, MeasureTheory.L1.integral_eq_integral]
    apply integral_congr_ae
    exact coe_densityProductL1 p (Hs.toL2 (by norm_num) r) |>.symm
  have hint' : Tendsto
      (fun n => MeasureTheory.L1.integral (densityProductCLM p
        (Hs.toL2 (by norm_num) (qseq n)))) atTop
      (nhds (MeasureTheory.L1.integral (densityProductCLM p
        (Hs.toL2 (by norm_num) q)))) := by
    change Tendsto
      (fun n => MeasureTheory.L1.integralCLM (densityProductCLM p
        (Hs.toL2 (by norm_num) (qseq n)))) atTop
      (nhds (MeasureTheory.L1.integralCLM (densityProductCLM p
        (Hs.toL2 (by norm_num) q)))) at hint
    simpa only [MeasureTheory.L1.integral_eq] using hint
  simpa only [hform] using hint'

/-- Uniform critical boundedness plus physical `L²` convergence implies
convergence against a fixed critical derivative. -/
theorem criticalPairing_derivative_tendsto_of_toL2_of_bounded
    (f q : Hs (1 / 2 : ℝ)) (qseq : ℕ → Hs (1 / 2 : ℝ))
    (hq : Tendsto (fun n => Hs.toL2 (by norm_num) (qseq n))
      atTop (nhds (Hs.toL2 (by norm_num) q)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖qseq n‖ ≤ C) :
    Tendsto (fun n => criticalPairingCLM (criticalDerivative f) (qseq n))
      atTop (nhds (criticalPairingCLM (criticalDerivative f) q)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let P : ℝ := ‖criticalPairingCLM‖
  let B : ℝ := max C ‖q‖ + 1
  have hP0 : 0 ≤ P := by positivity
  have hB : 0 < B := by dsimp [B]; linarith [le_max_left C ‖q‖]
  have hsmall : Tendsto (fun h : ℝ =>
      P * ‖criticalQuotient h f - criticalDerivative f‖ * B)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hd : Tendsto
        (fun h : ℝ => criticalQuotient h f - criticalDerivative f)
        (nhdsWithin 0 {0}ᶜ) (nhds (0 : Hs (-(1 / 2 : ℝ)))) := by
      simpa using (criticalQuotient_tendsto f).sub
        (tendsto_const_nhds : Tendsto
          (fun _ : ℝ => criticalDerivative f) (nhdsWithin 0 {0}ᶜ)
            (nhds (criticalDerivative f)))
    have hn : Tendsto
        (fun h : ℝ => ‖criticalQuotient h f - criticalDerivative f‖)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      simpa using hd.norm
    simpa using (tendsto_const_nhds.mul hn).mul_const B
  have hev : ∀ᶠ h : ℝ in nhdsWithin 0 {0}ᶜ,
      P * ‖criticalQuotient h f - criticalDerivative f‖ * B < ε / 3 :=
    by
      have he := NormedAddGroup.tendsto_nhds_zero.mp hsmall
        (ε / 3) (by positivity)
      filter_upwards [he] with h hh
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg hP0 (norm_nonneg _)) hB.le)] at hh
      exact hh
  have hex : ∃ h : ℝ, h ∈ ({0}ᶜ : Set ℝ) ∧
      P * ‖criticalQuotient h f - criticalDerivative f‖ * B < ε / 3 := by
    have hall : ∀ᶠ h : ℝ in nhdsWithin 0 {0}ᶜ,
        h ∈ ({0}ᶜ : Set ℝ) ∧
          P * ‖criticalQuotient h f - criticalDerivative f‖ * B < ε / 3 := by
      filter_upwards [self_mem_nhdsWithin, hev] with h hh hs
      exact ⟨hh, hs⟩
    exact hall.exists
  obtain ⟨h, hhmem, hhsmall⟩ := hex
  have hh : h ≠ 0 := by simpa using hhmem
  have hmid := quotient_pairing_tendsto_of_toL2 h hh f q qseq hq
  rw [Metric.tendsto_atTop] at hmid
  obtain ⟨N, hN⟩ := hmid (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hqnB : ‖qseq n‖ ≤ B := by
    exact (hbound n).trans (le_trans (le_max_left _ _) (by dsimp [B]; linarith))
  have hqB : ‖q‖ ≤ B :=
    (le_max_right C ‖q‖).trans (by dsimp [B]; linarith)
  have hpair_bound (T : Hs (-(1 / 2 : ℝ)))
      (r : Hs (1 / 2 : ℝ)) :
      ‖criticalPairingCLM T r‖ ≤ P * ‖T‖ * ‖r‖ := by
    exact (criticalPairingCLM T).le_opNorm r |>.trans
      (mul_le_mul_of_nonneg_right
        (criticalPairingCLM.le_opNorm T) (norm_nonneg r))
  have hleft :
      ‖criticalPairingCLM (criticalDerivative f) (qseq n) -
        criticalPairingCLM (criticalQuotient h f) (qseq n)‖ < ε / 3 := by
    rw [← sub_apply, ← map_sub]
    refine (hpair_bound (criticalDerivative f - criticalQuotient h f) (qseq n)).trans_lt ?_
    rw [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left hqnB
      (mul_nonneg hP0 (norm_nonneg _))).trans_lt hhsmall
  have hright :
      ‖criticalPairingCLM (criticalQuotient h f) q -
        criticalPairingCLM (criticalDerivative f) q‖ < ε / 3 := by
    rw [← sub_apply, ← map_sub]
    refine (hpair_bound (criticalQuotient h f - criticalDerivative f) q).trans_lt ?_
    exact (mul_le_mul_of_nonneg_left hqB
      (mul_nonneg hP0 (norm_nonneg _))).trans_lt hhsmall
  have hmiddle := hN n hn
  rw [dist_eq_norm] at hmiddle ⊢
  let x : ℂ := criticalPairingCLM (criticalDerivative f) (qseq n) -
    criticalPairingCLM (criticalQuotient h f) (qseq n)
  let y : ℂ := criticalPairingCLM (criticalQuotient h f) (qseq n) -
    criticalPairingCLM (criticalQuotient h f) q
  let z : ℂ := criticalPairingCLM (criticalQuotient h f) q -
    criticalPairingCLM (criticalDerivative f) q
  have hdecomp :
      criticalPairingCLM (criticalDerivative f) (qseq n) -
        criticalPairingCLM (criticalDerivative f) q = x + y + z := by
    dsimp [x, y, z]
    ring
  calc
    ‖criticalPairingCLM (criticalDerivative f) (qseq n) -
        criticalPairingCLM (criticalDerivative f) q‖ = ‖x + y + z‖ := by rw [hdecomp]
    _ ≤ (‖x‖ + ‖y‖) + ‖z‖ := by
      exact (norm_add_le (x + y) z).trans
        (add_le_add (norm_add_le x y) le_rfl)
    _ = ‖criticalPairingCLM (criticalDerivative f) (qseq n) -
          criticalPairingCLM (criticalQuotient h f) (qseq n)‖ +
        ‖criticalPairingCLM (criticalQuotient h f) (qseq n) -
          criticalPairingCLM (criticalQuotient h f) q‖ +
        ‖criticalPairingCLM (criticalQuotient h f) q -
          criticalPairingCLM (criticalDerivative f) q‖ := by rfl
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end CubicNLSPhaseRetrieval
