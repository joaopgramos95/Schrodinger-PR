import Lean_Code.SmoothHsMultiplier
import Lean_Code.CriticalCurrent
import Lean_Code.DensityCurrent

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- Complex conjugation on critical Sobolev space, selected through the
proved Lipschitz-composition theorem. -/
def criticalConj (f : Hs (1 / 2 : ℝ)) : Hs (1 / 2 : ℝ) :=
  Classical.choose
    (lipschitz_composition_exists (starRingEnd ℂ) 1
      Complex.isometry_conj.lipschitz (map_zero _) f)

lemma criticalConj_toL2 (f : Hs (1 / 2 : ℝ)) :
    Hs.toL2 (by norm_num) (criticalConj f) =
      lipschitzMapL2 (starRingEnd ℂ) 1
        Complex.isometry_conj.lipschitz (map_zero _)
        (Hs.toL2 (by norm_num) f) :=
  Classical.choose_spec
    (lipschitz_composition_exists (starRingEnd ℂ) 1
      Complex.isometry_conj.lipschitz (map_zero _) f)

lemma criticalConj_toL2_ae (f : Hs (1 / 2 : ℝ)) :
    (Hs.toL2 (by norm_num) (criticalConj f) : ℝ → ℂ) =ᵐ[volume]
      fun x => starRingEnd ℂ ((Hs.toL2 (by norm_num) f : ℝ → ℂ) x) := by
  rw [criticalConj_toL2]
  exact coe_lipschitzMapL2 (starRingEnd ℂ) 1
    Complex.isometry_conj.lipschitz (map_zero _) _

lemma criticalConj_toL2_eq_conjL2 (f : Hs (1 / 2 : ℝ)) :
    Hs.toL2 (by norm_num) (criticalConj f) =
      conjL2 (Hs.toL2 (by norm_num) f) := by
  apply Lp.ext
  filter_upwards [criticalConj_toL2_ae f,
    Complex.conjLIE.toContinuousLinearMap.coeFn_compLpL
      (Hs.toL2 (by norm_num) f)] with x hl hr
  rw [hl]
  exact hr.symm

private lemma conjL2_add (f g : L2) :
    conjL2 (f + g) = conjL2 f + conjL2 g := by
  simpa [conjL2] using
    map_add (Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume) f g

private lemma conjL2_real_smul (c : ℝ) (f : L2) :
    conjL2 (c • f) = c • conjL2 f := by
  simpa [conjL2] using
    map_smul (Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume) c f

private def criticalConjLinear :
    Hs (1 / 2 : ℝ) →ₗ[ℝ] Hs (1 / 2 : ℝ) where
  toFun := criticalConj
  map_add' f g := by
    apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
    have hadd : Hs.toL2 (by norm_num) (f + g) =
        Hs.toL2 (by norm_num) f + Hs.toL2 (by norm_num) g := by
      rw [← hsHalfToL2CLM_apply, map_add, hsHalfToL2CLM_apply,
        hsHalfToL2CLM_apply]
    have hout : Hs.toL2 (by norm_num) (criticalConj f + criticalConj g) =
        Hs.toL2 (by norm_num) (criticalConj f) +
          Hs.toL2 (by norm_num) (criticalConj g) := by
      rw [← hsHalfToL2CLM_apply, map_add, hsHalfToL2CLM_apply,
        hsHalfToL2CLM_apply]
    rw [criticalConj_toL2_eq_conjL2, hadd, conjL2_add, hout,
      criticalConj_toL2_eq_conjL2, criticalConj_toL2_eq_conjL2]
  map_smul' c f := by
    apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
    have hsmul : Hs.toL2 (by norm_num) (c • f) =
        c • Hs.toL2 (by norm_num) f := by
      rw [← hsHalfToL2CLM_apply, ← hsHalfToL2CLM_apply]
      exact map_smul (hsHalfToL2CLM.restrictScalars ℝ) c f
    have hout : Hs.toL2 (by norm_num) (c • criticalConj f) =
        c • Hs.toL2 (by norm_num) (criticalConj f) := by
      rw [← hsHalfToL2CLM_apply, ← hsHalfToL2CLM_apply]
      exact map_smul (hsHalfToL2CLM.restrictScalars ℝ) c (criticalConj f)
    rw [criticalConj_toL2_eq_conjL2, hsmul, conjL2_real_smul]
    change c • conjL2 (Hs.toL2 (by norm_num) f) =
      Hs.toL2 (by norm_num) (c • criticalConj f)
    rw [hout, criticalConj_toL2_eq_conjL2]

private theorem criticalConj_seq_closed_graph :
    ∀ (u : ℕ → Hs (1 / 2 : ℝ)) (x y : Hs (1 / 2 : ℝ)),
      Tendsto u atTop (𝓝 x) →
      Tendsto (criticalConjLinear ∘ u) atTop (𝓝 y) →
      y = criticalConjLinear x := by
  intro u x y hu huy
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  have hy0 := (hsHalfToL2CLM.restrictScalars ℝ).continuous.tendsto y |>.comp huy
  have hy : Tendsto
      (fun n => Hs.toL2 (by norm_num) (criticalConjLinear (u n))) atTop
      (𝓝 (Hs.toL2 (by norm_num) y)) := by
    convert hy0 using 1 <;>
      simp [Function.comp_def, hsHalfToL2CLM_apply]
  have hx0 := (hsHalfToL2CLM.restrictScalars ℝ).continuous.tendsto x |>.comp hu
  have hx : Tendsto (fun n => Hs.toL2 (by norm_num) (u n)) atTop
      (𝓝 (Hs.toL2 (by norm_num) x)) := by
    convert hx0 using 1 <;>
      simp [Function.comp_def, hsHalfToL2CLM_apply]
  have hc0 :=
    (Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume).continuous.tendsto
      (Hs.toL2 (by norm_num) x) |>.comp hx
  have hc : Tendsto
      (fun n => Hs.toL2 (by norm_num) (criticalConjLinear (u n))) atTop
      (𝓝 (Hs.toL2 (by norm_num) (criticalConjLinear x))) := by
    convert hc0 using 1 <;>
      simp [Function.comp_def, criticalConjLinear,
        criticalConj_toL2_eq_conjL2, conjL2]
  exact tendsto_nhds_unique hy hc

/-- Conjugation as a continuous real-linear map on `H^{1/2}`. -/
def criticalConjCLM :
    Hs (1 / 2 : ℝ) →L[ℝ] Hs (1 / 2 : ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph criticalConj_seq_closed_graph

@[simp] lemma criticalConjCLM_apply (f : Hs (1 / 2 : ℝ)) :
    criticalConjCLM f = criticalConj f := rfl

/-- The endpoint quadratic current tested against a Schwartz multiplier. -/
def criticalQuadraticCurrent (f : Hs (1 / 2 : ℝ))
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  criticalPairingCLM (criticalDerivative f)
    (schwartzHsMultiplier φ (criticalConj f))

lemma continuous_criticalQuadraticCurrent (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun f : Hs (1 / 2 : ℝ) =>
      criticalQuadraticCurrent f φ) := by
  unfold criticalQuadraticCurrent
  apply Continuous.clm_apply
  · exact criticalPairingCLM.continuous.comp criticalDerivative.continuous
  · exact (schwartzHsMultiplier φ).continuous.comp criticalConjCLM.continuous

/-- The endpoint holomorphic Wronskian pairing against a Schwartz test. -/
def criticalWronskianCurrent (f g : Hs (1 / 2 : ℝ))
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  criticalPairingCLM (criticalDerivative f) (schwartzHsMultiplier φ g) -
    criticalPairingCLM (criticalDerivative g) (schwartzHsMultiplier φ f)

lemma continuous_criticalWronskianCurrent (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun p : Hs (1 / 2 : ℝ) × Hs (1 / 2 : ℝ) =>
      criticalWronskianCurrent p.1 p.2 φ) := by
  unfold criticalWronskianCurrent
  apply Continuous.sub
  · apply Continuous.clm_apply
    · exact criticalPairingCLM.continuous.comp
        (criticalDerivative.continuous.comp continuous_fst)
    · exact (schwartzHsMultiplier φ).continuous.comp continuous_snd
  · apply Continuous.clm_apply
    · exact criticalPairingCLM.continuous.comp
        (criticalDerivative.continuous.comp continuous_snd)
    · exact (schwartzHsMultiplier φ).continuous.comp continuous_fst

end CubicNLSPhaseRetrieval
