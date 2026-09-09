import Lean_Code.StrichartzTensorPairing

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 10000000

namespace CubicNLSPhaseRetrieval

theorem tensorAdjoint_sq_estimate :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ (n : ℕ) (a b : Fin n → SchwartzMap ℝ ℂ),
      ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
        D * eLpNorm (tensorSliceL1 a b) (4 / 3) volume ^ (2 : ℕ) := by
  have hp : (1 : ℝ≥0∞) < 4 / 3 := by
    rw [← ENNReal.toReal_lt_toReal (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  have hpq : (4 / 3 : ℝ≥0∞) < 4 := by
    rw [← ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)]
    norm_num
  have hexp : (4 : ℝ≥0∞)⁻¹ =
      (4 / 3 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (1 / 2 : ℝ) := by
    have hl : (4 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
    have hdiv : (4 / 3 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvtop : (4 / 3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hdiv
    have hr : (4 / 3 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.sub_ne_top hinvtop
    have hle : ENNReal.ofReal (1 / 2 : ℝ) ≤ (4 / 3 : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.toReal_le_toReal (by norm_num) hinvtop]
      norm_num
    apply le_antisymm
    · rw [← ENNReal.toReal_le_toReal hl hr,
        ENNReal.toReal_sub_of_le hle hinvtop]
      norm_num
    · rw [← ENNReal.toReal_le_toReal hr hl,
        ENNReal.toReal_sub_of_le hle hinvtop]
      norm_num
  obtain ⟨Ch, hChtop, hHLS⟩ := HLS_time (1 / 2) (by norm_num) (by norm_num)
    (4 / 3) 4 hp hpq (by norm_num) (by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
      exact hexp)
  let c : ℝ≥0∞ := ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ)))
  refine ⟨c * Ch, ENNReal.mul_lt_top (by simp [c]) hChtop, ?_⟩
  intro n a b
  let G : ℝ × ℝ → ℂ := tensorG a b
  let q : ℝ → ℝ≥0∞ := tensorSliceL1 a b
  have hG : Measurable G := tensorG_measurable a b
  have hq : Measurable q := tensorSliceL1_measurable a b
  have hfinite (t : ℝ) : spatialL1 G t ≠ ⊤ := by
    rw [show spatialL1 G t = q t by exact spatialL1_tensorG a b t]
    exact schwartzL1E_ne_top _
  have hmix : scalarMixedENorm volume volume (4 / 3) 1 G < ⊤ := by
    rw [← spatialL1Complex_eLpNorm G hfinite]
    have heq : eLpNorm (spatialL1Complex G) (4 / 3) volume =
        eLpNorm q (4 / 3) volume := by
      apply eLpNorm_congr_enorm_ae
      filter_upwards with t
      rw [spatialL1Complex_enorm G hfinite]
      exact (spatialL1_tensorG a b t).trans (enorm_eq_self _).symm
    rw [heq]
    exact (tensorSliceL1_memLp a b).2
  have hqcomplex := spatialL1Complex_memLp G hG hfinite hmix
  have hfrac := hHLS (spatialL1Complex G) hqcomplex
  have hfracmeas : AEMeasurable
      (fractionalIntegral (1 / 2) (spatialL1Complex G)) volume := by
    have hcomplex : Measurable (spatialL1Complex G) := by
      unfold spatialL1Complex
      exact Complex.ofRealCLM.continuous.measurable.comp
        (ENNReal.measurable_toReal.comp (spatialL1_measurable G hG))
    have hk : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (|p.1 - p.2| ^ (-(1 / 2 : ℝ))) *
          ‖spatialL1Complex G p.2‖₊) := by
      have hkernel : Measurable (fun p : ℝ × ℝ =>
          ENNReal.ofReal (|p.1 - p.2| ^ (-(1 / 2 : ℝ)))) := by fun_prop
      have hnorm : Measurable (fun p : ℝ × ℝ =>
          (↑‖spatialL1Complex G p.2‖₊ : ℝ≥0∞)) :=
        (hcomplex.comp measurable_snd).nnnorm.coe_nnreal_ennreal
      change Measurable
        ((fun p : ℝ × ℝ => ENNReal.ofReal (|p.1 - p.2| ^ (-(1 / 2 : ℝ)))) *
          (fun p : ℝ × ℝ => (↑‖spatialL1Complex G p.2‖₊ : ℝ≥0∞)))
      exact hkernel.mul hnorm
    exact hk.lintegral_prod_right'.aemeasurable
  have hdouble : ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
      c * ∫⁻ s : ℝ, q s * fractionalIntegral (1 / 2) (spatialL1Complex G) s := by
    change ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
      c * ∫⁻ s : ℝ, tensorSliceL1 a b s *
        fractionalIntegral (1 / 2) (spatialL1Complex (tensorG a b)) s
    have henorm : ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) =
        ‖@inner ℂ L2 _ (tensorAdjoint a b) (tensorAdjoint a b)‖ₑ := by
      rw [inner_self_eq_norm_sq_to_K, enorm_pow]
      congr 1
      calc
        ‖tensorAdjoint a b‖ₑ = ENNReal.ofReal ‖tensorAdjoint a b‖ :=
          (ofReal_norm _).symm
        _ = ENNReal.ofReal ‖(‖tensorAdjoint a b‖ : ℂ)‖ := by simp
        _ = ‖(‖tensorAdjoint a b‖ : ℂ)‖ₑ := ofReal_norm _
    rw [henorm, inner_tensorAdjoint_double]
    calc
      ‖∫ s : ℝ, ∫ r : ℝ,
          @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ ≤
          ∫⁻ s : ℝ, ‖∫ r : ℝ,
            @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s : ℝ, ∫⁻ r : ℝ,
          ‖@inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ := by
        apply lintegral_mono
        intro s
        exact enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s : ℝ, ∫⁻ r : ℝ, q s *
          (ENNReal.ofReal ((4 * Real.pi * |s - r|) ^ (-(1 / 2 : ℝ))) * q r) := by
        apply lintegral_mono_ae
        filter_upwards with s
        apply lintegral_mono_ae
        rw [ae_iff]
        have hsingle : volume {s} = 0 := measure_singleton s
        have hne : ∀ᵐ r : ℝ ∂volume, r ≠ s := by
          rw [ae_iff]
          rw [show {r : ℝ | ¬r ≠ s} = {s} by
            ext r
            simp [eq_comm]]
          exact hsingle
        filter_upwards [hne] with r hrs
        exact inner_tensorAdjointCurve_bound a b s r (Ne.symm hrs)
      _ = c * ∫⁻ s : ℝ, q s *
          fractionalIntegral (1 / 2) (spatialL1Complex G) s := by
        change (∫⁻ s : ℝ, ∫⁻ r : ℝ, tensorSliceL1 a b s *
            (ENNReal.ofReal ((4 * Real.pi * |s - r|) ^ (-(1 / 2 : ℝ))) *
              tensorSliceL1 a b r)) =
          c * ∫⁻ s : ℝ, tensorSliceL1 a b s *
            fractionalIntegral (1 / 2) (spatialL1Complex (tensorG a b)) s
        simp_rw [freeKernel_time_factor, ← spatialL1_tensorG a b,
          fractionalIntegral_spatialL1 (tensorG a b) hfinite]
        change (∫⁻ s : ℝ, ∫⁻ r : ℝ, spatialL1 G s *
            (c * ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r)) =
          c * ∫⁻ s : ℝ, spatialL1 G s *
            (∫⁻ r : ℝ, ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r)
        simp_rw [show ∀ s r : ℝ, spatialL1 G s *
            (c * ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r) =
            c * (spatialL1 G s *
              (ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r)) by
          intro s r
          ring]
        rw [show (∫⁻ s : ℝ, ∫⁻ r : ℝ, c *
              (spatialL1 G s *
                (ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r))) =
            c * ∫⁻ s : ℝ, spatialL1 G s *
              (∫⁻ r : ℝ, ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) *
                spatialL1 G r) by
          simp_rw [lintegral_const_mul' _ _ (by simp [c] : c ≠ ⊤),
            lintegral_const_mul' _ _ (hfinite _)]]
  calc
    ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
        c * ∫⁻ s : ℝ, q s * fractionalIntegral (1 / 2) (spatialL1Complex G) s := hdouble
    _ ≤ c * (eLpNorm q (4 / 3) volume *
        eLpNorm (fractionalIntegral (1 / 2) (spatialL1Complex G)) 4 volume) := by
      gcongr
      exact lintegral_mul_le_eLpNorm_four_thirds_four q _ hq.aemeasurable hfracmeas
    _ ≤ c * (eLpNorm q (4 / 3) volume *
        (Ch * eLpNorm (spatialL1Complex G) (4 / 3) volume)) := by
      gcongr
    _ = (c * Ch) * eLpNorm q (4 / 3) volume ^ (2 : ℕ) := by
      have heq : eLpNorm (spatialL1Complex G) (4 / 3) volume =
          eLpNorm q (4 / 3) volume := by
        apply eLpNorm_congr_enorm_ae
        filter_upwards with t
        rw [spatialL1Complex_enorm G hfinite, spatialL1_tensorG]
        exact (enorm_eq_self _).symm
      rw [heq]
      ring

theorem tensorAdjoint_estimate :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (n : ℕ) (a b : Fin n → SchwartzMap ℝ ℂ),
      ‖tensorAdjoint a b‖ₑ ≤ C * eLpNorm (tensorSliceL1 a b) (4 / 3) volume := by
  obtain ⟨D, hDtop, hD⟩ := tensorAdjoint_sq_estimate
  let C : ℝ≥0∞ := D ^ (1 / 2 : ℝ)
  refine ⟨C, ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDtop.ne, ?_⟩
  intro n a b
  let x : ℝ≥0∞ := ‖tensorAdjoint a b‖ₑ
  let y : ℝ≥0∞ := eLpNorm (tensorSliceL1 a b) (4 / 3) volume
  have hs := ENNReal.rpow_le_rpow (hD n a b) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change x ≤ C * y
  calc
    x = (x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (D * y ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := hs
    _ = C * y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul]
      norm_num
      rfl

end CubicNLSPhaseRetrieval
