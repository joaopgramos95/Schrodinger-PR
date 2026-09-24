import Lean_Code.StrichartzFreeFlow

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 5000000

namespace CubicNLSPhaseRetrieval

def spatialPairing (h : Lp ℂ ⊤ (volume : Measure ℝ)) (g : L1Complex) : ℂ :=
  ∫ x : ℝ, (h : ℝ → ℂ) x * (g : ℝ → ℂ) x

lemma spatialPairing_integrable (h : Lp ℂ ⊤ (volume : Measure ℝ))
    (g : L1Complex) :
    Integrable (fun x : ℝ => (h : ℝ → ℂ) x * (g : ℝ → ℂ) x) volume := by
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  exact memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 (Lp.memLp h) (Lp.memLp g))

lemma spatialPairing_sub (h : Lp ℂ ⊤ (volume : Measure ℝ))
    (g₁ g₂ : L1Complex) :
    spatialPairing h g₁ - spatialPairing h g₂ = spatialPairing h (g₁ - g₂) := by
  unfold spatialPairing
  rw [← integral_sub (spatialPairing_integrable h g₁) (spatialPairing_integrable h g₂)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub g₁ g₂] with x hx
  rw [hx]
  simp only [Pi.sub_apply]
  ring

lemma exists_L1_normer_gt (h : Lp ℂ ⊤ (volume : Measure ℝ))
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r < ‖h‖) :
    ∃ g : L1Complex, ‖g‖ ≤ 1 ∧
      r < ‖∫ x : ℝ, (h : ℝ → ℂ) x * (g : ℝ → ℂ) x‖ := by
  let A : Set ℝ := {x | r < ‖(h : ℝ → ℂ) x‖}
  have hAmeas : MeasurableSet A := by
    exact measurableSet_lt measurable_const (Lp.stronglyMeasurable h).norm.measurable
  have hApos : 0 < volume A := by
    rw [pos_iff_ne_zero]
    intro hAzero
    have hae : ∀ᵐ x : ℝ ∂volume, ‖(h : ℝ → ℂ) x‖ ≤ r := by
      rw [ae_iff]
      rw [show {x : ℝ | ¬‖(h : ℝ → ℂ) x‖ ≤ r} = A by
        ext x
        simp only [A, Set.mem_setOf_eq, not_le]]
      exact hAzero
    have hess := eLpNormEssSup_le_of_ae_bound hae
    have hnormle : ‖h‖ ≤ r := by
      rw [Lp.norm_def, eLpNorm_exponent_top]
      calc
        (eLpNormEssSup (h : ℝ → ℂ) volume).toReal ≤
            (ENNReal.ofReal r).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
        _ = r := ENNReal.toReal_ofReal hr0
    exact (not_lt_of_ge hnormle) hr
  obtain ⟨B, hBmeas, hBA, hBpos, hBtop⟩ :=
    Measure.exists_subset_measure_lt_top hAmeas hApos
  have hBreal : 0 < volume.real B :=
    ENNReal.toReal_pos hBpos.ne' hBtop.ne
  let phase : ℝ → ℂ := fun x => conj ((h : ℝ → ℂ) x) / (‖(h : ℝ → ℂ) x‖ : ℂ)
  have hphase_meas : Measurable phase := by
    unfold phase
    exact (Complex.continuous_conj.measurable.comp (Lp.stronglyMeasurable h).measurable).div
      (Complex.ofRealCLM.continuous.measurable.comp (Lp.stronglyMeasurable h).norm.measurable)
  have hphase_norm (x : ℝ) : ‖phase x‖ ≤ 1 := by
    unfold phase
    rw [Complex.norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    by_cases hx : ‖(h : ℝ → ℂ) x‖ = 0
    · simp [hx]
    · rw [div_self hx]
  let qfun : ℝ → ℂ := B.indicator phase
  have hqint : Integrable qfun volume := by
    rw [integrable_indicator_iff hBmeas]
    apply Integrable.mono' (integrableOn_const hBtop.ne (C := (1 : ℝ)))
      hphase_meas.aestronglyMeasurable.restrict
    filter_upwards with x
    exact hphase_norm x
  let a : ℝ := (volume.real B)⁻¹
  have ha : 0 < a := inv_pos.mpr hBreal
  let gfun : ℝ → ℂ := fun x => (a : ℂ) * qfun x
  have hgint : Integrable gfun volume := hqint.const_mul (a : ℂ)
  have hphase_on (x : ℝ) (hx : x ∈ B) : ‖phase x‖ = 1 := by
    have hxA := hBA hx
    change r < ‖(h : ℝ → ℂ) x‖ at hxA
    have hxnorm : ‖(h : ℝ → ℂ) x‖ ≠ 0 := by
      intro hz
      exact (not_lt_of_ge hr0) (by simpa only [hz] using hxA)
    unfold phase
    rw [Complex.norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self hxnorm]
  have hg_norm_integral : ∫ x : ℝ, ‖gfun x‖ = 1 := by
    have hpoint : (fun x : ℝ => ‖gfun x‖) = B.indicator (fun _ => a) := by
      funext x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        simp only [gfun, qfun, Set.indicator_of_mem hx, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ha, hphase_on x hx, mul_one]
      · rw [Set.indicator_of_notMem hx]
        simp [gfun, qfun, Set.indicator_of_notMem hx]
    rw [hpoint, integral_indicator hBmeas, setIntegral_const, smul_eq_mul]
    dsimp [a]
    field_simp
  let hgmem : MemLp gfun 1 volume := memLp_one_iff_integrable.mpr hgint
  let g : L1Complex := hgmem.toLp gfun
  have hgnorm : ‖g‖ ≤ 1 := by
    rw [show ‖g‖ = ∫ x : ℝ, ‖gfun x‖ by
      dsimp [g]
      rw [Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm hgint,
        ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)] ]
    rw [hg_norm_integral]
  refine ⟨g, hgnorm, ?_⟩
  have hnormB : IntegrableOn (fun x : ℝ => ‖(h : ℝ → ℂ) x‖) B volume :=
    (integrableOn_Lp_of_measure_ne_top h (by simp) hBtop.ne).norm
  let F : ℝ → ℝ := B.indicator fun x => ‖(h : ℝ → ℂ) x‖
  have hFint : Integrable F volume := by
    rw [integrable_indicator_iff hBmeas]
    exact hnormB
  have hset : {x : ℝ | r < F x} = B := by
    ext x
    by_cases hx : x ∈ B
    · simp only [F, Set.indicator_of_mem hx, Set.mem_setOf_eq, hx, iff_true]
      exact hBA hx
    · simp only [F, Set.indicator_of_notMem hx, Set.mem_setOf_eq, hx, iff_false]
      exact not_lt_of_ge hr0
  have hlower : volume.real B * r < ∫ x in B, ‖(h : ℝ → ℂ) x‖ := by
    have hh := setIntegral_gt_gt hr0 (hFint.integrableOn) (show volume {x | r < F x} ≠ 0 by
      rw [hset]
      exact hBpos.ne')
    rw [hset] at hh
    convert hh using 1
    apply setIntegral_congr_fun hBmeas
    intro x hx
    simp only [F, Set.indicator_of_mem hx]
  have hscaled : r < a * ∫ x in B, ‖(h : ℝ → ℂ) x‖ := by
    calc
      r = a * (volume.real B * r) := by
        dsimp [a]
        field_simp
      _ < a * ∫ x in B, ‖(h : ℝ → ℂ) x‖ := mul_lt_mul_of_pos_left hlower ha
  have hpair : ∫ x : ℝ, (h : ℝ → ℂ) x * (gfun x) =
      ((a * ∫ x in B, ‖(h : ℝ → ℂ) x‖ : ℝ) : ℂ) := by
    rw [show (fun x : ℝ => (h : ℝ → ℂ) x * gfun x) =
        fun x => (a : ℂ) * B.indicator (fun x => (‖(h : ℝ → ℂ) x‖ : ℂ)) x by
      funext x
      by_cases hx : x ∈ B
      · simp only [gfun, qfun, Set.indicator_of_mem hx]
        have hx0 : (h : ℝ → ℂ) x ≠ 0 := by
          rw [← norm_ne_zero_iff]
          have := hphase_on x hx
          unfold phase at this
          intro hz
          simp [hz] at this
        unfold phase
        have hhp : (h : ℝ → ℂ) x *
            (conj ((h : ℝ → ℂ) x) / (‖(h : ℝ → ℂ) x‖ : ℂ)) =
            (‖(h : ℝ → ℂ) x‖ : ℂ) := by
          rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          field_simp
        calc
          (h : ℝ → ℂ) x * ((a : ℂ) *
              (conj ((h : ℝ → ℂ) x) / (‖(h : ℝ → ℂ) x‖ : ℂ))) =
              (a : ℂ) * ((h : ℝ → ℂ) x *
                (conj ((h : ℝ → ℂ) x) / (‖(h : ℝ → ℂ) x‖ : ℂ))) := by ring
          _ = (a : ℂ) * (‖(h : ℝ → ℂ) x‖ : ℂ) := by rw [hhp]
      · simp [gfun, qfun, Set.indicator_of_notMem hx]]
    rw [integral_const_mul, integral_indicator hBmeas]
    have hi : (∫ x in B, (‖(h : ℝ → ℂ) x‖ : ℂ)) =
        ((∫ x in B, ‖(h : ℝ → ℂ) x‖ : ℝ) : ℂ) := by
      change (∫ x : ℝ, (‖(h : ℝ → ℂ) x‖ : ℂ) ∂volume.restrict B) = _
      exact integral_ofReal
    rw [hi, Complex.ofReal_mul]
  have hgcoe := hgmem.coeFn_toLp
  rw [show (∫ x : ℝ, (h : ℝ → ℂ) x * (g : ℝ → ℂ) x) =
      ∫ x : ℝ, (h : ℝ → ℂ) x * gfun x by
    apply integral_congr_ae
    filter_upwards [hgcoe] with x hx
    rw [hx]]
  rw [hpair, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_of_le_of_lt hr0 hscaled)]
  exact hscaled

theorem exists_schwartz_spatial_norming_sequence :
    ∃ b : ℕ → SchwartzMap ℝ ℂ,
      (∀ n, ‖(b n).toLp 1 volume‖ ≤ 1) ∧
      ∀ h : Lp ℂ ⊤ (volume : Measure ℝ),
        ENNReal.ofReal ‖h‖ =
          ⨆ n : ℕ, ENNReal.ofReal ‖spatialPairing h ((b n).toLp 1 volume)‖ := by
  obtain ⟨b, hb, hdense⟩ := exists_schwartz_unit_norming_sequence
  refine ⟨b, hb, ?_⟩
  intro h
  apply le_antisymm
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hrreal : (r : ℝ) < ‖h‖ := by
      have ht := (ENNReal.toReal_lt_toReal (by simp : (r : ℝ≥0∞) ≠ ⊤)
        ENNReal.ofReal_ne_top).mpr hr
      simpa only [ENNReal.coe_toReal, ENNReal.toReal_ofReal (norm_nonneg h)] using ht
    obtain ⟨g, hg, hpair⟩ := exists_L1_normer_gt h r (by positivity) hrreal
    let gap : ℝ := ‖spatialPairing h g‖ - r
    have hgap : 0 < gap := sub_pos.mpr hpair
    have hhpos : 0 < ‖h‖ := lt_of_le_of_lt (by positivity) hrreal
    let ε : ℝ := gap / (‖h‖ + 1)
    have hε : 0 < ε := div_pos hgap (by positivity)
    obtain ⟨n, hn⟩ := hdense g hg ε hε
    have herr : ‖spatialPairing h ((b n).toLp 1 volume) - spatialPairing h g‖ ≤
        ‖h‖ * dist ((b n).toLp 1 volume) g := by
      rw [spatialPairing_sub]
      simpa only [spatialPairing, dist_eq_norm] using
        norm_integral_Linfty_L1_le h ((b n).toLp 1 volume - g)
    have hsmall : ‖h‖ * dist ((b n).toLp 1 volume) g < gap := by
      calc
        ‖h‖ * dist ((b n).toLp 1 volume) g < ‖h‖ * ε :=
          mul_lt_mul_of_pos_left hn hhpos
        _ < gap := by
          have hratio : ‖h‖ / (‖h‖ + 1) < 1 := by
            rw [div_lt_one (by positivity)]
            linarith
          rw [show ‖h‖ * ε = gap * (‖h‖ / (‖h‖ + 1)) by
            dsimp [ε]
            field_simp]
          simpa only [mul_one] using mul_lt_mul_of_pos_left hratio hgap
    have htri := norm_le_norm_add_norm_sub
      (spatialPairing h ((b n).toLp 1 volume)) (spatialPairing h g)
    have hrn : (r : ℝ) < ‖spatialPairing h ((b n).toLp 1 volume)‖ := by
      dsimp [gap] at hsmall
      linarith
    exact (calc
      (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by simp
      _ < ENNReal.ofReal ‖spatialPairing h ((b n).toLp 1 volume)‖ := by
        have hpos : 0 < ‖spatialPairing h ((b n).toLp 1 volume)‖ :=
          lt_of_le_of_lt (by positivity) hrn
        rw [ENNReal.ofReal_lt_ofReal_iff hpos]
        exact hrn
      _ ≤ ⨆ n : ℕ, ENNReal.ofReal
          ‖spatialPairing h ((b n).toLp 1 volume)‖ :=
        le_iSup (fun k : ℕ => ENNReal.ofReal
          ‖spatialPairing h ((b k).toLp 1 volume)‖) n).le
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖spatialPairing h ((b n).toLp 1 volume)‖ ≤
          ‖h‖ * ‖(b n).toLp 1 volume‖ :=
        by simpa only [spatialPairing] using
          norm_integral_Linfty_L1_le h ((b n).toLp 1 volume)
      _ ≤ ‖h‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb n) (norm_nonneg h)

end CubicNLSPhaseRetrieval
