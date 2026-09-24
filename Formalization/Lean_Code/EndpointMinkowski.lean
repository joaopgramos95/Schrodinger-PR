import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Lean_Code.ScalarMixedNorms

/-!
# Endpoint scalar Minkowski inequality

The proof is specialized to the fourth time exponent used by the endpoint
argument.  Expanding the fourth power into a fourfold nonnegative integral
and applying four-factor Hölder avoids any appeal to a Bochner-space
measurability theorem for maps into `L⁴`.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

section OuterFour

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

private abbrev Quad (S : Type*) := S × (S × (S × S))

private def quadCoord (z : Quad S) : Fin 4 → S
  | ⟨0, _⟩ => z.1
  | ⟨1, _⟩ => z.2.1
  | ⟨2, _⟩ => z.2.2.1
  | ⟨3, _⟩ => z.2.2.2

private abbrev quadMeasure (ν : Measure S) : Measure (Quad S) :=
  ν.prod (ν.prod (ν.prod ν))

set_option maxHeartbeats 2000000 in
/-- Integral Minkowski for nonnegative scalar functions at exponent four. -/
theorem eLpNorm_four_lintegral_le (ν : Measure S) (μ : Measure T)
    [SFinite ν] [SFinite μ] (A : S → T → ℝ≥0∞)
    (hA : Measurable (fun z : S × T => A z.1 z.2)) :
    eLpNorm (fun t => ∫⁻ s, A s t ∂ν) 4 μ ≤
      ∫⁻ s, eLpNorm (A s) 4 μ ∂ν := by
  let N : S → ℝ≥0∞ := fun s => eLpNorm (A s) 4 μ
  let R : ℝ≥0∞ := ∫⁻ s, N s ∂ν
  have hAs (s : S) : Measurable (A s) :=
    hA.comp (measurable_const.prodMk measurable_id)
  have hAt (t : T) : Measurable (fun s => A s t) :=
    hA.comp (measurable_id.prodMk measurable_const)
  have hN : Measurable N := by
    dsimp only [N]
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
      ENNReal.toReal_ofNat, enorm_eq_self]
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((hA.pow_const (4 : ℝ)).lintegral_prod_right')
  have hpow (t : T) :
      (∫⁻ s, A s t ∂ν) ^ (4 : ℝ) =
        ∫⁻ z : Quad S,
          A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t))
            ∂quadMeasure ν := by
    have hrest3 : Measurable (fun z : S × (S × S) =>
        A z.1 t * (A z.2.1 t * A z.2.2 t)) :=
      ((hAt t).comp measurable_fst).mul
        (((hAt t).comp (measurable_fst.comp measurable_snd)).mul
          ((hAt t).comp (measurable_snd.comp measurable_snd)))
    have hrest2 : Measurable (fun z : S × S => A z.1 t * A z.2 t) :=
      ((hAt t).comp measurable_fst).mul ((hAt t).comp measurable_snd)
    symm
    change (∫⁻ z : S × (S × (S × S)),
      A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t))
        ∂ν.prod (ν.prod (ν.prod ν))) = _
    rw [lintegral_prod_mul (μ := ν) (ν := ν.prod (ν.prod ν))
        (hAt t).aemeasurable hrest3.aemeasurable,
      lintegral_prod_mul (μ := ν) (ν := ν.prod ν)
        (hAt t).aemeasurable hrest2.aemeasurable,
      lintegral_prod_mul (μ := ν) (ν := ν)
        (hAt t).aemeasurable (hAt t).aemeasurable]
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
    ring
  have hholder (z : Quad S) :
      (∫⁻ t, A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t)) ∂μ) ≤
        N z.1 * (N z.2.1 * (N z.2.2.1 * N z.2.2.2)) := by
    let f : Fin 4 → T → ℝ≥0∞ := fun i t => A (quadCoord z i) t ^ (4 : ℝ)
    have hf : ∀ i ∈ (Finset.univ : Finset (Fin 4)), AEMeasurable (f i) μ := by
      intro i _
      exact (hAs (quadCoord z i)).aemeasurable.pow_const 4
    have hh := ENNReal.lintegral_prod_norm_pow_le
      (μ := μ) (Finset.univ : Finset (Fin 4)) hf
      (p := fun _ => (1 / 4 : ℝ)) (by norm_num) (by intro; norm_num)
    calc
      (∫⁻ t, A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t)) ∂μ) =
          ∫⁻ t, ∏ i ∈ (Finset.univ : Finset (Fin 4)),
            f i t ^ (1 / 4 : ℝ) ∂μ := by
        apply lintegral_congr
        intro t
        rw [show A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t)) =
            ∏ i : Fin 4, A (quadCoord z i) t by
          simp [quadCoord, Fin.prod_univ_succ]]
        apply Finset.prod_congr rfl
        intro i _
        dsimp only [f]
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ ∏ i ∈ (Finset.univ : Finset (Fin 4)),
          (∫⁻ t, f i t ∂μ) ^ (1 / 4 : ℝ) := hh
      _ = N z.1 * (N z.2.1 * (N z.2.2.1 * N z.2.2.2)) := by
        rw [show N z.1 * (N z.2.1 * (N z.2.2.1 * N z.2.2.2)) =
            ∏ i : Fin 4, N (quadCoord z i) by
          simp [quadCoord, Fin.prod_univ_succ]]
        apply Finset.prod_congr rfl
        intro i _
        dsimp only [f, N]
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
        norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
  have hfactor :
      (∫⁻ z : Quad S, N z.1 * (N z.2.1 * (N z.2.2.1 * N z.2.2.2))
        ∂quadMeasure ν) = R ^ (4 : ℝ) := by
    have hrest3 : Measurable (fun z : S × (S × S) =>
        N z.1 * (N z.2.1 * N z.2.2)) :=
      (hN.comp measurable_fst).mul
        ((hN.comp (measurable_fst.comp measurable_snd)).mul
          (hN.comp (measurable_snd.comp measurable_snd)))
    have hrest2 : Measurable (fun z : S × S => N z.1 * N z.2) :=
      (hN.comp measurable_fst).mul (hN.comp measurable_snd)
    change (∫⁻ z : S × (S × (S × S)),
      N z.1 * (N z.2.1 * (N z.2.2.1 * N z.2.2.2))
        ∂ν.prod (ν.prod (ν.prod ν))) = _
    rw [lintegral_prod_mul (μ := ν) (ν := ν.prod (ν.prod ν))
        hN.aemeasurable hrest3.aemeasurable,
      lintegral_prod_mul (μ := ν) (ν := ν.prod ν)
        hN.aemeasurable hrest2.aemeasurable,
      lintegral_prod_mul (μ := ν) (ν := ν) hN.aemeasurable hN.aemeasurable]
    dsimp only [R]
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
    ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
  change (∫⁻ t, (∫⁻ s, A s t ∂ν) ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) ≤ R
  have hPmeas : Measurable (fun q : T × Quad S =>
      A q.2.1 q.1 *
        (A q.2.2.1 q.1 * (A q.2.2.2.1 q.1 * A q.2.2.2.2 q.1))) := by
    have hz1 : Measurable (fun q : T × Quad S => q.2.1) :=
      measurable_fst.comp measurable_snd
    have hz2 : Measurable (fun q : T × Quad S => q.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hz3 : Measurable (fun q : T × Quad S => q.2.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hz4 : Measurable (fun q : T × Quad S => q.2.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact (hA.comp (hz1.prodMk measurable_fst)).mul
      ((hA.comp (hz2.prodMk measurable_fst)).mul
        ((hA.comp (hz3.prodMk measurable_fst)).mul
          (hA.comp (hz4.prodMk measurable_fst))))
  have hbase : (∫⁻ t, (∫⁻ s, A s t ∂ν) ^ (4 : ℝ) ∂μ) ≤ R ^ (4 : ℝ) := by
    calc
    (∫⁻ t, (∫⁻ s, A s t ∂ν) ^ (4 : ℝ) ∂μ) =
        ∫⁻ t, ∫⁻ z : Quad S,
          A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t))
            ∂quadMeasure ν ∂μ := by
      apply lintegral_congr
      exact hpow
    _ = ∫⁻ z : Quad S, ∫⁻ t,
          A z.1 t * (A z.2.1 t * (A z.2.2.1 t * A z.2.2.2 t))
            ∂μ ∂quadMeasure ν := by
      apply lintegral_lintegral_swap
      exact hPmeas.aemeasurable
    _ ≤ ∫⁻ z : Quad S,
          N z.1 * (N z.2.1 * (N z.2.2.1 * N z.2.2.2))
            ∂quadMeasure ν :=
      lintegral_mono hholder
    _ = R ^ (4 : ℝ) := hfactor
  calc
    (∫⁻ t, (∫⁻ s, A s t ∂ν) ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) ≤
        (R ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) :=
      ENNReal.rpow_le_rpow hbase (by positivity)
    _ = R := by
      rw [← ENNReal.rpow_mul]
      norm_num

end OuterFour

section MixedFourTop

variable {S τ χ : Type*} [MeasurableSpace S] [MeasurableSpace τ]
  [MeasurableSpace χ]

private theorem sectionENorm_integral_le_lintegral_sectionENorm
    (nu : Measure S) (mu_x : Measure χ) [SFinite nu] [SFinite mu_x]
    (F : S → τ → χ → ℂ)
    (hF : Measurable (fun z : S × (τ × χ) ↦ F z.1 z.2.1 z.2.2))
    (t : τ) :
    sectionENorm mu_x ⊤ (fun z : τ × χ ↦ ∫ s, F s z.1 z.2 ∂nu) t ≤
      ∫⁻ s, sectionENorm mu_x ⊤ (fun z : τ × χ ↦ F s z.1 z.2) t ∂nu := by
  let A : S → ℝ≥0∞ := fun s ↦
    sectionENorm mu_x ⊤ (fun z : τ × χ ↦ F s z.1 z.2) t
  have hFst : Measurable (fun z : S × χ ↦ F z.1 t z.2) :=
    hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hA : Measurable A := by
    exact measurable_esssup_section nu mu_x
      (fun z : S × χ ↦ F z.1 t z.2) hFst
  change eLpNormEssSup (fun x ↦ ∫ s, F s t x ∂nu) mu_x ≤ ∫⁻ s, A s ∂nu
  apply eLpNormEssSup_le_of_ae_enorm_bound
  have hleft : Measurable (fun z : S × χ ↦ ‖F z.1 t z.2‖ₑ) := hFst.enorm
  have hright : Measurable (fun z : S × χ ↦ A z.1) := hA.comp measurable_fst
  have hcomm :
      (∀ᵐ s ∂nu, ∀ᵐ x ∂mu_x, ‖F s t x‖ₑ ≤ A s) ↔
        ∀ᵐ x ∂mu_x, ∀ᵐ s ∂nu, ‖F s t x‖ₑ ≤ A s :=
    MeasureTheory.Measure.ae_ae_comm (measurableSet_le hleft hright)
  have hsx : ∀ᵐ s ∂nu, ∀ᵐ x ∂mu_x, ‖F s t x‖ₑ ≤ A s := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [A, sectionENorm, eLpNorm_exponent_top] using
      (ae_le_eLpNormEssSup (f := fun x ↦ F s t x) (μ := mu_x))
  filter_upwards [hcomm.mp hsx] with x hx
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae hx)

set_option maxHeartbeats 2000000 in
/-- Endpoint integral Minkowski in the precise `L⁴_t L∞_x` form used by the
chronological Duhamel argument. -/
theorem scalar_mixed_minkowski_four_top
    (nu : Measure S) (mu_t : Measure τ) (mu_x : Measure χ)
    [SFinite nu] [SFinite mu_t] [SFinite mu_x]
    (F : S → τ → χ → ℂ)
    (hF : Measurable (fun z : S × (τ × χ) ↦ F z.1 z.2.1 z.2.2)) :
    scalarMixedENorm mu_t mu_x 4 ⊤
        (fun z ↦ ∫ s, F s z.1 z.2 ∂nu) ≤
      ∫⁻ s, scalarMixedENorm mu_t mu_x 4 ⊤
        (fun z ↦ F s z.1 z.2) ∂nu := by
  let A : S → τ → ℝ≥0∞ := fun s t ↦
    sectionENorm mu_x ⊤ (fun z : τ × χ ↦ F s z.1 z.2) t
  let B : τ → ℝ≥0∞ := fun t ↦ ∫⁻ s, A s t ∂nu
  have hFreassoc : Measurable
      (fun z : (S × τ) × χ ↦ F z.1.1 z.1.2 z.2) :=
    hF.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hA : Measurable (fun z : S × τ ↦ A z.1 z.2) := by
    exact measurable_esssup_section (nu.prod mu_t) mu_x
      (fun z : (S × τ) × χ ↦ F z.1.1 z.1.2 z.2) hFreassoc
  have houter := eLpNorm_four_lintegral_le nu mu_t A hA
  have hpoint (t : τ) :
      sectionENorm mu_x ⊤ (fun z : τ × χ ↦ ∫ s, F s z.1 z.2 ∂nu) t ≤ B t := by
    exact sectionENorm_integral_le_lintegral_sectionENorm nu mu_x F hF t
  calc
    scalarMixedENorm mu_t mu_x 4 ⊤
        (fun z ↦ ∫ s, F s z.1 z.2 ∂nu) ≤ eLpNorm B 4 mu_t := by
      apply eLpNorm_mono_enorm
      intro t
      simpa only [enorm_eq_self] using hpoint t
    _ ≤ ∫⁻ s, eLpNorm (A s) 4 mu_t ∂nu := houter
    _ = ∫⁻ s, scalarMixedENorm mu_t mu_x 4 ⊤
        (fun z ↦ F s z.1 z.2) ∂nu := rfl

end MixedFourTop

end CubicNLSPhaseRetrieval
