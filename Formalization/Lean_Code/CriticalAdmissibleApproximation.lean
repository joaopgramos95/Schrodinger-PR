import Lean_Code.CriticalMollification

/-!
# Admissible approximation of compact bounded critical coefficients

The normalized mollifiers are admissible under a cutoff which is flat on
one fixed compact enlargement of the rough coefficient's support.  Their
products with either bounded critical slice converge in physical `L²` and
remain uniformly bounded in `H^{1/2}`.
-/

open Filter MeasureTheory Set
open scoped Convolution ENNReal SchwartzMap Topology Pointwise

noncomputable section
namespace CubicNLSPhaseRetrieval

private lemma boundedCritical_mul_toL2_eq (f g : BoundedCritical) :
    (f.mul g).toL2 = boundedProductL2 f.toL2 g.toL2 g.bounded := by
  apply Lp.ext
  filter_upwards [BoundedCritical.mul_toL2_ae f g,
    coe_boundedProductL2 f.toL2 g.toL2 g.bounded] with x hfg hp
  rw [hfg, hp]

private lemma enorm_boundedCritical_mul_sq_le (f g : BoundedCritical) :
    ‖(f.mul g).val‖ₑ ^ (2 : ℕ) ≤
      (‖f.toL2‖ₑ * eLpNorm (g.toL2 : ℝ → ℂ) ∞ volume) ^ (2 : ℕ) +
        2 * eLpNorm (g.toL2 : ℝ → ℂ) ∞ volume ^ (2 : ℕ) *
            homogeneousFourierEnergy (1 / 2 : ℝ) f.toL2 +
          2 * eLpNorm (f.toL2 : ℝ → ℂ) ∞ volume ^ (2 : ℕ) *
            homogeneousFourierEnergy (1 / 2 : ℝ) g.toL2 := by
  have hmass := norm_boundedProductL2_le f.toL2 g.toL2 g.bounded
  have hhom := homogeneousFourierEnergy_boundedProductL2_le
    f.toL2 g.toL2 f.bounded g.bounded
  refine (enorm_Hs_half_sq_le_mass_add_homogeneous (f.mul g).val).trans ?_
  change ‖(f.mul g).toL2‖ₑ ^ (2 : ℕ) +
      homogeneousFourierEnergy (1 / 2 : ℝ) (f.mul g).toL2 ≤ _
  rw [boundedCritical_mul_toL2_eq]
  calc
    ‖boundedProductL2 f.toL2 g.toL2 g.bounded‖ₑ ^ (2 : ℕ) +
        homogeneousFourierEnergy (1 / 2 : ℝ)
          (boundedProductL2 f.toL2 g.toL2 g.bounded) ≤
      (‖f.toL2‖ₑ * eLpNorm (g.toL2 : ℝ → ℂ) ∞ volume) ^ (2 : ℕ) +
        (2 * eLpNorm (g.toL2 : ℝ → ℂ) ∞ volume ^ (2 : ℕ) *
            homogeneousFourierEnergy (1 / 2 : ℝ) f.toL2 +
          2 * eLpNorm (f.toL2 : ℝ → ℂ) ∞ volume ^ (2 : ℕ) *
            homogeneousFourierEnergy (1 / 2 : ℝ) g.toL2) :=
      add_le_add (pow_le_pow_left' hmass 2) hhom
    _ = _ := (add_assoc _ _ _).symm

private lemma schwartzMollifier_toL2_eq (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume)
    (hAc : HasCompactSupport A) :
    (schwartzBoundedCritical
      (criticalMollify_toSchwartz n A
        (hA2.locallyIntegrable (by norm_num)) hAc)).toL2 =
      criticalMollifyL2 n A hAm hA2 := by
  apply Lp.ext
  filter_upwards [schwartzBoundedCritical_toL2_ae
      (criticalMollify_toSchwartz n A
        (hA2.locallyIntegrable (by norm_num)) hAc),
    criticalMollifyL2_coe n A hAm hA2] with x hφ hm
  rw [hφ, criticalMollify_toSchwartz_apply, hm]

private lemma schwartzMollifier_top_le (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume)
    (hAc : HasCompactSupport A) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, ‖A x‖ ≤ M) :
    eLpNorm ((schwartzBoundedCritical
      (criticalMollify_toSchwartz n A
        (hA2.locallyIntegrable (by norm_num)) hAc)).toL2 : ℝ → ℂ)
        ∞ volume ≤ ENNReal.ofReal M := by
  rw [schwartzMollifier_toL2_eq n A hAm hA2 hAc,
    eLpNorm_congr_ae (criticalMollifyL2_coe n A hAm hA2),
    eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound
    (Filter.Eventually.of_forall fun x => by
      exact norm_criticalMollify_le n A M hM hbound x)

private lemma schwartzMollifier_admissible
    (chi : SchwartzMap ℝ ℂ) (n : ℕ) (A : ℝ → ℂ)
    (hA2 : MemLp A 2 volume) (hAc : HasCompactSupport A)
    (hflat : ∀ x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport A,
      chi x = 1 ∧ deriv (chi : ℝ → ℂ) x = 0) :
    IsAdmissibleCurrentTest chi
      (criticalMollify_toSchwartz n A
        (hA2.locallyIntegrable (by norm_num)) hAc) := by
  refine ⟨criticalMollify_hasCompactSupport n A hAc, ?_⟩
  intro x hx
  have hraw : criticalMollify n A x ≠ 0 := by
    simpa only [criticalMollify_toSchwartz_apply] using hx
  exact hflat x (criticalMollify_support_subset n A hraw)

set_option maxHeartbeats 4000000 in
/-- A compact pointwise-bounded representative supplies the simultaneous
approximation required to extend the recovered current. -/
theorem simultaneousCurrentApproximation_of_compactRep
    (chi : SchwartzMap ℝ ℂ) (f g a : BoundedCritical)
    (A : ℝ → ℂ) (hAm : Measurable A) (hAc : HasCompactSupport A)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, ‖A x‖ ≤ M)
    (hrep : A =ᵐ[volume] (a.toL2 : ℝ → ℂ))
    (hflat : ∀ x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport A,
      chi x = 1 ∧ deriv (chi : ℝ → ℂ) x = 0) :
    IsSimultaneousCurrentApproximation chi f g a := by
  let hA2 : MemLp A 2 volume :=
    (memLp_congr_ae hrep).2 (Lp.memLp a.toL2)
  let phi : ℕ → SchwartzMap ℝ ℂ := fun n =>
    criticalMollify_toSchwartz n A
      (hA2.locallyIntegrable (by norm_num)) hAc
  let c : ℕ → BoundedCritical := fun n => schwartzBoundedCritical (phi n)
  have hcL2 (n : ℕ) : (c n).toL2 = criticalMollifyL2 n A hAm hA2 := by
    exact schwartzMollifier_toL2_eq n A hAm hA2 hAc
  have hctend : Tendsto (fun n => (c n).toL2) atTop (nhds a.toL2) := by
    simp_rw [hcL2]
    exact criticalMollifyL2_tendsto a.val A hAm hAc M hM hbound hrep
  have hprodF : Tendsto (fun n => ((c n).mul f.conj).toL2) atTop
      (nhds ((a.mul f.conj).toL2)) := by
    simp_rw [boundedCritical_mul_toL2_eq]
    exact tendsto_boundedProductL2_left (fun n => (c n).toL2) a.toL2
      f.conj.toL2 hctend f.conj.bounded
  have hprodG : Tendsto (fun n => ((c n).mul g.conj).toL2) atTop
      (nhds ((a.mul g.conj).toL2)) := by
    simp_rw [boundedCritical_mul_toL2_eq]
    exact tendsto_boundedProductL2_left (fun n => (c n).toL2) a.toL2
      g.conj.toL2 hctend g.conj.bounded
  let Da : ℝ≥0∞ := ‖a.toL2‖ₑ
  let Ha : ℝ≥0∞ := homogeneousFourierEnergy (1 / 2 : ℝ) a.toL2
  let Mf : ℝ≥0∞ := eLpNorm (f.conj.toL2 : ℝ → ℂ) ∞ volume
  let Mg : ℝ≥0∞ := eLpNorm (g.conj.toL2 : ℝ → ℂ) ∞ volume
  let Hf : ℝ≥0∞ := homogeneousFourierEnergy (1 / 2 : ℝ) f.conj.toL2
  let Hg : ℝ≥0∞ := homogeneousFourierEnergy (1 / 2 : ℝ) g.conj.toL2
  let E : ℝ≥0∞ := ENNReal.ofReal M
  let Df : ℝ≥0∞ := (Da * Mf) ^ (2 : ℕ) +
    2 * Mf ^ (2 : ℕ) * Ha + 2 * E ^ (2 : ℕ) * Hf
  let Dg : ℝ≥0∞ := (Da * Mg) ^ (2 : ℕ) +
    2 * Mg ^ (2 : ℕ) * Ha + 2 * E ^ (2 : ℕ) * Hg
  have hDa : Da < ⊤ := by dsimp [Da]; exact enorm_lt_top
  have hHa : Ha < ⊤ := by
    dsimp [Ha, BoundedCritical.toL2]
    exact homogeneousFourierEnergy_Hs_toL2_lt_top a.val
  have hMf : Mf < ⊤ := f.conj.bounded
  have hMg : Mg < ⊤ := g.conj.bounded
  have hHf : Hf < ⊤ := by
    dsimp [Hf, BoundedCritical.toL2]
    exact homogeneousFourierEnergy_Hs_toL2_lt_top f.conj.val
  have hHg : Hg < ⊤ := by
    dsimp [Hg, BoundedCritical.toL2]
    exact homogeneousFourierEnergy_Hs_toL2_lt_top g.conj.val
  have hE : E < ⊤ := ENNReal.ofReal_lt_top
  have hDf : Df < ⊤ := by
    dsimp [Df]
    apply ENNReal.add_lt_top.2
    constructor
    · apply ENNReal.add_lt_top.2
      exact ⟨ENNReal.pow_lt_top (ENNReal.mul_lt_top hDa hMf),
        ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hMf)) hHa⟩
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hE)) hHf
  have hDg : Dg < ⊤ := by
    dsimp [Dg]
    apply ENNReal.add_lt_top.2
    constructor
    · apply ENNReal.add_lt_top.2
      exact ⟨ENNReal.pow_lt_top (ENNReal.mul_lt_top hDa hMg),
        ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hMg)) hHa⟩
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hE)) hHg
  have hcMass (n : ℕ) : ‖(c n).toL2‖ₑ ≤ Da := by
    rw [hcL2]
    have hn := criticalMollifyL2_norm_le n A hAm hA2
    have hto : hA2.toLp A = a.toL2 := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp hA2, hrep] with x hA hx
      rw [hA, hx]
    rw [hto] at hn
    simpa only [Da, ← ofReal_norm] using ENNReal.ofReal_le_ofReal hn
  have hcHom (n : ℕ) :
      homogeneousFourierEnergy (1 / 2 : ℝ) (c n).toL2 ≤ Ha := by
    rw [hcL2]
    have hh := homogeneousFourierEnergy_criticalMollifyL2_le n A hAm hA2
    have hto : hA2.toLp A = a.toL2 := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp hA2, hrep] with x hA hx
      rw [hA, hx]
    simpa only [hto, Ha] using hh
  have hcTop (n : ℕ) :
      eLpNorm ((c n).toL2 : ℝ → ℂ) ∞ volume ≤ E := by
    exact schwartzMollifier_top_le n A hAm hA2 hAc M hM hbound
  have hbF2 (n : ℕ) : ‖((c n).mul f.conj).val‖ₑ ^ (2 : ℕ) ≤ Df := by
    refine (enorm_boundedCritical_mul_sq_le (c n) f.conj).trans ?_
    dsimp only [Df, Da, Ha, Mf, Hf, E]
    gcongr
    · exact hcMass n
    · exact hcHom n
    · exact hcTop n
  have hbG2 (n : ℕ) : ‖((c n).mul g.conj).val‖ₑ ^ (2 : ℕ) ≤ Dg := by
    refine (enorm_boundedCritical_mul_sq_le (c n) g.conj).trans ?_
    dsimp only [Dg, Da, Ha, Mg, Hg, E]
    gcongr
    · exact hcMass n
    · exact hcHom n
    · exact hcTop n
  let C : ℝ := Df.toReal + Dg.toReal + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbF (n : ℕ) : ‖((c n).mul f.conj).val‖ ≤ C := by
    have hr := ENNReal.toReal_mono hDf.ne (hbF2 n)
    rw [ENNReal.toReal_pow, toReal_enorm] at hr
    dsimp [C]
    nlinarith [norm_nonneg ((c n).mul f.conj).val,
      (ENNReal.toReal_nonneg : 0 ≤ Dg.toReal)]
  have hbG (n : ℕ) : ‖((c n).mul g.conj).val‖ ≤ C := by
    have hr := ENNReal.toReal_mono hDg.ne (hbG2 n)
    rw [ENNReal.toReal_pow, toReal_enorm] at hr
    dsimp [C]
    nlinarith [norm_nonneg ((c n).mul g.conj).val,
      (ENNReal.toReal_nonneg : 0 ≤ Df.toReal)]
  refine ⟨phi, ?_, ?_, ?_, C, hC, ?_, ?_⟩
  · intro n
    exact schwartzMollifier_admissible chi n A hA2 hAc hflat
  · simpa only [c, phi, BoundedCritical.toL2] using hprodF
  · simpa only [c, phi, BoundedCritical.toL2] using hprodG
  · intro n
    exact hbF n
  · intro n
    exact hbG n

end CubicNLSPhaseRetrieval
