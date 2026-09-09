import Lean_Code.CubicFlow
import Lean_Code.EndpointControl
import Lean_Code.WronskianExterior
import Lean_Code.DiagonalTrace
import Lean_Code.HalfspacePropagation

/-!
# Completion of the phase-retrieval proof

Blueprint chapter: `chap:completion` (module 15).
Imports: modules 5, 10, 11, and 14.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The elementary `L²`--`L∞` interpolation inequality used for spatial
sections of the exterior product. -/
private theorem spatial_interp (μ : Measure ℝ) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 4 μ ≤
      eLpNorm f 2 μ ^ (1 / 2 : ℝ) * eLpNorm f ⊤ μ ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), eLpNorm_exponent_top]
  norm_num only [ENNReal.toReal_ofNat]
  let B : ℝ≥0∞ := eLpNormEssSup f μ
  have hB : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ B := ae_le_eLpNormEssSup
  have hpow : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ (4 : ℝ) ≤ B ^ (2 : ℝ) * ‖f x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hB] with x hx
    have hnat : ‖f x‖ₑ ^ (4 : ℕ) ≤ B ^ (2 : ℕ) * ‖f x‖ₑ ^ (2 : ℕ) := by
      calc
        ‖f x‖ₑ ^ (4 : ℕ) = ‖f x‖ₑ ^ 2 * ‖f x‖ₑ ^ 2 := by ring
        _ ≤ B ^ 2 * ‖f x‖ₑ ^ 2 :=
          mul_le_mul_right' (pow_le_pow_left' hx 2) _
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      ENNReal.rpow_natCast, ENNReal.rpow_natCast, ENNReal.rpow_natCast]
    exact hnat
  calc
    (∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) ≤
        (∫⁻ x, B ^ (2 : ℝ) * ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) (by positivity)
    _ = (B ^ (2 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) := by
      rw [lintegral_const_mul'' _ (hf.enorm.pow_const 2)]
    _ = B ^ (1 / 2 : ℝ) *
        (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 4 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      rw [← ENNReal.rpow_mul]
      norm_num
    _ = ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNormEssSup f μ ^ (1 / 2 : ℝ) := by
      have hquarter : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 4 : ℝ) =
          ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hquarter]
      dsimp only [B]
      ac_rfl

private lemma zeroExtendNormal_measurable' {F : Spacetime2} (hF : Measurable F) :
    Measurable (zeroExtendNormal F) := by
  unfold zeroExtendNormal
  exact Measurable.ite
    (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
    hF measurable_const

private lemma zeroExtendNormal_measurable_slice {σ : ℝ}
    (u v : GlobalSolution σ) (t : ℝ) :
    (fun z => zeroExtendNormal (measurableNormalExterior u v) (t, z))
      =ᵐ[volume.prod volume]
    (fun z => zeroExtendNormal (normalExterior u.u v.u) (t, z)) := by
  filter_upwards [measurableNormalExterior_slice u v t] with z hz
  unfold zeroExtendNormal
  split_ifs <;> simp_all

private lemma zeroExtendNormal_measurable_sectionENorm {σ : ℝ}
    (u v : GlobalSolution σ) (t : ℝ) (p : ℝ≥0∞) :
    sectionENorm (volume.prod volume) p
        (zeroExtendNormal (measurableNormalExterior u v)) t =
      sectionENorm (volume.prod volume) p
        (zeroExtendNormal (normalExterior u.u v.u)) t := by
  exact eLpNorm_congr_ae (zeroExtendNormal_measurable_slice u v t)

private lemma measurableRidgePotential_sectionENorm {σ : ℝ}
    (u : GlobalSolution σ) (t : ℝ) (p : ℝ≥0∞) :
    sectionENorm (volume.prod volume) p (measurableRidgePotential σ u) t =
      sectionENorm (volume.prod volume) p (ridgePotential σ u.u) t := by
  exact eLpNorm_congr_ae (measurableRidgePotential_slice σ u t)

/-- Equal-modulus data restricted to one nonempty open time interval. -/
def SameModulusOn (a b : ℝ) (u v : ℝ → L2) : Prop :=
  SameModulusOnSet (Set.Ioo a b) u v

/-- The part of `Q_bounds` needed by half-space propagation follows directly
from the endpoint `L⁴_tL∞_x` control.  Keeping this statement local avoids
placing the stronger strip estimate on the main theorem's dependency path. -/
private theorem ridgePotential_majorant_compact (σ : ℝ) (u : GlobalSolution σ)
    (K : Set ℝ) (hK : IsCompact K) :
    ∃ R : ℝ → ℝ, Integrable R (volume.restrict K) ∧ (∀ t, 0 ≤ R t) ∧
      ∀ᵐ t ∂volume.restrict K,
        sectionENorm (volume.prod volume) ⊤ (measurableRidgePotential σ u) t ≤
          ENNReal.ofReal (R t) := by
  let A : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative u.u) t
  let B : ℝ → ℝ := fun t => (A t).toReal
  have hend := endpoint_control σ u K hK.measurableSet hK.isBounded
  have hB4 : MemLp B 4 (volume.restrict K) := by
    simpa [B, A] using hend.2.1
  have hAfin : ∀ᵐ t ∂volume.restrict K, A t < ⊤ := by
    simpa [A] using hend.2.2
  have hsection : ∀ᵐ t ∂volume.restrict K,
      sectionENorm (volume.prod volume) ⊤ (measurableRidgePotential σ u) t ≤
        ENNReal.ofReal (2 * |σ| * B t ^ 2) := by
    filter_upwards [hAfin] with t ht
    have hAtop : eLpNormEssSup (u.u t : ℝ → ℂ) volume < ⊤ := by
      simpa [A, sectionENorm, eLpNorm_exponent_top, curveRepresentative] using ht
    have huBound : ∀ᵐ x : ℝ ∂volume,
        ‖(u.u t : ℝ → ℂ) x‖ ≤ B t := by
      filter_upwards [ae_le_eLpNormEssSup (f := (u.u t : ℝ → ℂ)) (μ := volume)]
        with x hx
      have hle : ENNReal.ofReal ‖(u.u t : ℝ → ℂ) x‖ ≤
          eLpNormEssSup (u.u t : ℝ → ℂ) volume := by
        simpa [ofReal_norm] using hx
      have hr :=
        (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hAtop.ne).2 hle
      simpa [B, A, sectionENorm, eLpNorm_exponent_top, curveRepresentative,
        ENNReal.toReal_ofReal (norm_nonneg _)] using hr
    have hxy : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
        ‖(u.u t : ℝ → ℂ) z.1‖ ≤ B t ∧ ‖(u.u t : ℝ → ℂ) z.2‖ ≤ B t := by
      filter_upwards [
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae huBound,
        (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae huBound]
        with z hz1 hz2
      exact ⟨hz1, hz2⟩
    have hnormal := normalToParticle_quasiMeasurePreserving.ae hxy
    rw [measurableRidgePotential_sectionENorm, sectionENorm, eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [hnormal] with z hz
    change
      ‖(u.u t : ℝ → ℂ) ((z.2 + z.1) / Real.sqrt 2)‖ ≤ B t ∧
        ‖(u.u t : ℝ → ℂ) ((z.2 - z.1) / Real.sqrt 2)‖ ≤ B t at hz
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simp only [ridgePotential, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (by positivity : 0 ≤
      ‖(u.u t : ℝ → ℂ) ((z.2 + z.1) / Real.sqrt 2)‖ ^ 2 +
        ‖(u.u t : ℝ → ℂ) ((z.2 - z.1) / Real.sqrt 2)‖ ^ 2)]
    have hB0 : 0 ≤ B t := ENNReal.toReal_nonneg
    have hx2 : ‖(u.u t : ℝ → ℂ) ((z.2 + z.1) / Real.sqrt 2)‖ ^ 2 ≤ B t ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hB0).2 hz.1
    have hy2 : ‖(u.u t : ℝ → ℂ) ((z.2 - z.1) / Real.sqrt 2)‖ ^ 2 ≤ B t ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hB0).2 hz.2
    calc
      |σ| * (‖(u.u t : ℝ → ℂ) ((z.2 + z.1) / Real.sqrt 2)‖ ^ 2 +
          ‖(u.u t : ℝ → ℂ) ((z.2 - z.1) / Real.sqrt 2)‖ ^ 2) ≤
          |σ| * (B t ^ 2 + B t ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hx2 hy2) (abs_nonneg σ)
      _ = 2 * |σ| * B t ^ 2 := by ring
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hB2 : MemLp B 2 (volume.restrict K) :=
    hB4.mono_exponent (by norm_num)
  have hR : Integrable (fun t => 2 * |σ| * B t ^ 2) (volume.restrict K) := by
    simpa [mul_assoc] using hB2.integrable_sq.const_mul (2 * |σ|)
  exact ⟨fun t => 2 * |σ| * B t ^ 2, hR,
    fun t => mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg σ)) (sq_nonneg (B t)),
    hsection⟩

/-- The ridge potential has locally finite first-summand `Y` norm. -/
private theorem ridgePotential_L1Linfty_compact (σ : ℝ) (u : GlobalSolution σ)
    (K : Set ℝ) (hK : IsCompact K) :
    scalarMixedENorm (volume.restrict K) (volume.prod volume) 1 ⊤
      (measurableRidgePotential σ u) < ⊤ := by
  obtain ⟨R, hR, hR0, hsection⟩ := ridgePotential_majorant_compact σ u K hK
  unfold scalarMixedENorm
  exact (eLpNorm_mono_enorm_ae (p := (1 : ℝ≥0∞))
    (hsection.mono fun t ht => by
      rw [enorm_eq_self, Real.enorm_eq_ofReal (hR0 t)]
      exact ht)).trans_lt
      (memLp_one_iff_integrable.2 hR).eLpNorm_lt_top

/-- Absolute continuity of the integrable endpoint majorant makes the ridge
potential small on a sufficiently short symmetric interval. -/
private theorem ridgePotential_small_symmetric_interval (σ : ℝ)
    (u : GlobalSolution σ) (a b t c0 : ℝ) (ht : t ∈ Set.Ioo a b) (hc0 : 0 < c0) :
    ∃ r : ℝ, 0 < r ∧ Set.Icc (t - r) (t + r) ⊆ Set.Ioo a b ∧
      scalarMixedENorm (volume.restrict (Set.Ioo (t - r) (t + r)))
        (volume.prod volume) 1 ⊤ (measurableRidgePotential σ u) ≤ ENNReal.ofReal c0 := by
  let ρ : ℝ := min (t - a) (b - t) / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)) (by norm_num)
  let K : Set ℝ := Set.Icc (t - ρ) (t + ρ)
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨R, hR, hR0, hsection⟩ := ridgePotential_majorant_compact σ u K hK
  let S : ℕ → Set ℝ := fun n =>
    Set.Ioo (t - (1 / ((n : ℝ) + 1))) (t + (1 / ((n : ℝ) + 1)))
  have hmeasure : Tendsto ((volume.restrict K) ∘ S) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, (volume.restrict K) (S n) ≤
        ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1))) := by
      intro n
      calc
        (volume.restrict K) (S n) ≤ volume (S n) := Measure.restrict_le_self _
        _ = ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1))) := by
          rw [show S n = Set.Ioo (t - (1 / ((n : ℝ) + 1)))
            (t + (1 / ((n : ℝ) + 1))) by rfl, Real.volume_Ioo]
          congr 1
          ring
    have hreal : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    have htop : Tendsto (fun n : ℕ => ENNReal.ofReal
        (2 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hreal
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun _ => bot_le) hbound
  have hsmallInt : Tendsto (fun n => ∫⁻ s in S n, ‖R s‖ₑ ∂volume.restrict K)
      atTop (𝓝 0) :=
    tendsto_setLIntegral_zero hR.hasFiniteIntegral.ne hmeasure
  have hsmallEventually : ∀ᶠ n : ℕ in atTop,
      (∫⁻ s in S n, ‖R s‖ₑ ∂volume.restrict K) < ENNReal.ofReal c0 :=
    (tendsto_order.1 hsmallInt).2 _ (ENNReal.ofReal_pos.2 hc0)
  have hrhoEventually : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ρ :=
    (tendsto_order.1
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _ hρ
  obtain ⟨n, hnsmall, hnρ⟩ := (hsmallEventually.and hrhoEventually).exists
  let r : ℝ := 1 / ((n : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r < ρ := by simpa [r] using hnρ
  have hSK : S n ⊆ K := by
    intro s hs
    change s ∈ Set.Icc (t - ρ) (t + ρ)
    change s ∈ Set.Ioo (t - r) (t + r) at hs
    rcases hs with ⟨hsl, hsr⟩
    constructor <;> linarith
  have hIccJ : Set.Icc (t - r) (t + r) ⊆ Set.Ioo a b := by
    intro s hs
    rcases hs with ⟨hsl, hsr⟩
    have hρa : ρ < t - a := by
      dsimp [ρ]
      have hmin : min (t - a) (b - t) ≤ t - a := min_le_left _ _
      nlinarith [sub_pos.mpr ht.1, sub_pos.mpr ht.2]
    have hρb : ρ < b - t := by
      dsimp [ρ]
      have hmin : min (t - a) (b - t) ≤ b - t := min_le_right _ _
      nlinarith [sub_pos.mpr ht.1, sub_pos.mpr ht.2]
    constructor <;> linarith
  have hsectionS : ∀ᵐ s ∂volume.restrict (S n),
      sectionENorm (volume.prod volume) ⊤ (measurableRidgePotential σ u) s ≤
        ENNReal.ofReal (R s) :=
    (ae_mono (Measure.restrict_mono hSK le_rfl)) hsection
  have hnorm : scalarMixedENorm (volume.restrict (S n)) (volume.prod volume) 1 ⊤
      (measurableRidgePotential σ u) ≤
        ∫⁻ s in S n, ‖R s‖ₑ ∂volume.restrict K := by
    unfold scalarMixedENorm
    calc
      eLpNorm (fun s => sectionENorm (volume.prod volume) ⊤
          (measurableRidgePotential σ u) s) 1 (volume.restrict (S n)) ≤
          eLpNorm R 1 (volume.restrict (S n)) := by
        apply eLpNorm_mono_enorm_ae
        filter_upwards [hsectionS] with s hs
        rw [enorm_eq_self, Real.enorm_eq_ofReal (hR0 s)]
        exact hs
      _ = ∫⁻ s in S n, ‖R s‖ₑ ∂volume.restrict K := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hm : (volume.restrict K).restrict (S n) = volume.restrict (S n) := by
          rw [Measure.restrict_restrict measurableSet_Ioo]
          rw [Set.inter_eq_left.2 hSK]
        rw [hm]
  refine ⟨r, hr, ?_, hnorm.trans hnsmall.le⟩
  exact hIccJ

private lemma exteriorProduct_memLp_two (u v : ℝ → L2) (t : ℝ) :
    MemLp (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 2
      (volume.prod volume) := by
  have hcoe := coe_exteriorProductL2 (u t) (v t)
  have hae : ((exteriorProductL2 (u t) (v t) : TwoParticleL2) : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun z => exteriorProduct u v (t, z) := by
    simpa [exteriorProduct] using hcoe
  exact (memLp_congr_ae hae).1 (Lp.memLp (exteriorProductL2 (u t) (v t)))

private lemma zeroExtendNormal_section_memLp_two (u v : ℝ → L2) (t : ℝ) :
    MemLp (fun z : ℝ × ℝ => zeroExtendNormal (normalExterior u v) (t, z)) 2
      (volume.prod volume) := by
  let S : Set (ℝ × ℝ) := {z | z.1 < 0}
  have hS : MeasurableSet S := measurableSet_lt measurable_fst measurable_const
  have hcomp := MemLp.comp_normalToParticle (exteriorProduct_memLp_two u v t)
  have hind := hcomp.indicator hS
  have heq : S.indicator
      ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘ normalToParticle) =
      fun z => zeroExtendNormal (normalExterior u v) (t, z) := by
    funext z
    by_cases hz : z.1 < 0
    · simp [S, hz, Function.comp_def, zeroExtendNormal, normalExterior,
        fromNormalCoordinates_eq]
    · simp [S, hz, zeroExtendNormal]
  rw [heq] at hind
  exact hind

private lemma zeroExtendNormal_section_two_bound (u v : ℝ → L2) (t : ℝ) :
    eLpNorm (fun z : ℝ × ℝ => zeroExtendNormal (normalExterior u v) (t, z)) 2
        (volume.prod volume) ≤
      (ENNReal.ofReal
        |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
          (1 / (2 : ℝ≥0∞)).toReal •
        ‖exteriorProductL2 (u t) (v t)‖ₑ := by
  let S : Set (ℝ × ℝ) := {z | z.1 < 0}
  have hraw := exteriorProduct_memLp_two u v t
  have hcomp := eLpNorm_comp_normalToParticle_le hraw
  have hind :
      eLpNorm (S.indicator
        ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘ normalToParticle)) 2
          (volume.prod volume) ≤
        eLpNorm ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘
          normalToParticle) 2 (volume.prod volume) :=
    eLpNorm_indicator_le _
  calc
    eLpNorm (fun z : ℝ × ℝ => zeroExtendNormal (normalExterior u v) (t, z)) 2
        (volume.prod volume) =
        eLpNorm (S.indicator
          ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘ normalToParticle)) 2
            (volume.prod volume) := by
          congr 1
    _ ≤ eLpNorm ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘
          normalToParticle) 2 (volume.prod volume) := hind
    _ ≤ _ := by
      calc
        _ ≤ (ENNReal.ofReal
            |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
              (1 / (2 : ℝ≥0∞)).toReal •
            eLpNorm (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 2
              (volume.prod volume) := hcomp
        _ = _ := by
          congr 1
          let E : TwoParticleL2 := exteriorProductL2 (u t) (v t)
          have hae : ((E : TwoParticleL2) : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
              fun z => exteriorProduct u v (t, z) := by
            simpa [E, exteriorProduct] using
              (coe_exteriorProductL2 (u t) (v t))
          calc
            eLpNorm (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 2
                (volume.prod volume) = eLpNorm (E : ℝ × ℝ → ℂ) 2
                  (volume.prod volume) := eLpNorm_congr_ae hae.symm
            _ = ‖E‖ₑ := (Lp.enorm_def E).symm

private theorem zeroExtendNormal_LinftyL2_compact_raw (u v : ℝ → L2)
    (hu : Continuous u) (hv : Continuous v) (K : Set ℝ) (hK : IsCompact K) :
    scalarMixedENorm (volume.restrict K) (volume.prod volume) ⊤ 2
      (zeroExtendNormal (normalExterior u v)) < ⊤ := by
  let E : ℝ → TwoParticleL2 := fun t => exteriorProductL2 (u t) (v t)
  have hEcont : Continuous E := continuous_exteriorProductL2 u v hu hv
  have hcomp : IsCompact (E '' K) := hK.image_of_continuousOn hEcont.continuousOn
  obtain ⟨M, hMpos, hM⟩ := hcomp.isBounded.subset_closedBall_lt 0 (0 : TwoParticleL2)
  let jac : ℝ≥0∞ := (ENNReal.ofReal
    |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
      (1 / (2 : ℝ≥0∞)).toReal
  let D : ℝ≥0∞ := jac * ENNReal.ofReal M
  have hjac : jac ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · positivity
    · exact ENNReal.ofReal_ne_top
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top hjac ENNReal.ofReal_ne_top
  let C : NNReal := D.toNNReal
  rw [scalarMixedENorm, eLpNorm_exponent_top]
  apply eLpNormEssSup_lt_top_of_ae_enorm_bound (C := C)
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  have hEt : ‖E t‖ ≤ M := by
    have hm := hM ⟨t, ht, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hm
  have hEenorm : ‖E t‖ₑ ≤ ENNReal.ofReal M := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hEt
  have hsec := zeroExtendNormal_section_two_bound u v t
  calc
    ‖sectionENorm (volume.prod volume) 2 (zeroExtendNormal (normalExterior u v)) t‖ₑ =
        eLpNorm (fun z : ℝ × ℝ =>
          zeroExtendNormal (normalExterior u v) (t, z)) 2
          (volume.prod volume) := by simp [sectionENorm]
    _ ≤ jac • ‖E t‖ₑ := by simpa [jac, E] using hsec
    _ ≤ jac • ENNReal.ofReal M := by
      exact smul_le_smul_of_nonneg_left hEenorm (by positivity)
    _ = (C : ℝ≥0∞) := by
      change jac * ENNReal.ofReal M = (C : ℝ≥0∞)
      rw [show jac * ENNReal.ofReal M = D from rfl, ENNReal.coe_toNNReal hD]

private theorem zeroExtendNormal_LinftyL2_compact (σ : ℝ)
    (u v : GlobalSolution σ) (K : Set ℝ) (hK : IsCompact K) :
    scalarMixedENorm (volume.restrict K) (volume.prod volume) ⊤ 2
      (zeroExtendNormal (measurableNormalExterior u v)) < ⊤ := by
  have hraw :=
    zeroExtendNormal_LinftyL2_compact_raw u.u v.u u.continuous v.continuous K hK
  unfold scalarMixedENorm at hraw ⊢
  simpa only [zeroExtendNormal_measurable_sectionENorm] using
    hraw

private lemma tensorProduct_memLp_four (f g : L2)
    (hf : MemLp (f : ℝ → ℂ) 4 volume) (hg : MemLp (g : ℝ → ℂ) 4 volume) :
    MemLp (fun z : ℝ × ℝ => (f : ℝ → ℂ) z.1 * (g : ℝ → ℂ) z.2) 4
      (volume.prod volume) := by
  let T : ℝ × ℝ → ℂ := fun z => (f : ℝ → ℂ) z.1 * (g : ℝ → ℂ) z.2
  have hTmeas : AEStronglyMeasurable T (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (memLp_norm_rpow_iff hTmeas (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).1
  have hfint := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have hgint := hg.integrable_norm_rpow (by norm_num) (by norm_num)
  have hprod := hfint.mul_prod hgint
  rw [show (4 : ℝ≥0∞) / 4 = 1 by
    change (4 : ℝ≥0∞) * 4⁻¹ = 1
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  apply memLp_one_iff_integrable.2
  simpa only [T, norm_mul, ENNReal.toReal_ofNat,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] using hprod

private lemma eLpNorm_tensorProduct_four (f g : L2)
    (hf : MemLp (f : ℝ → ℂ) 4 volume) (hg : MemLp (g : ℝ → ℂ) 4 volume) :
    eLpNorm (fun z : ℝ × ℝ => (f : ℝ → ℂ) z.1 * (g : ℝ → ℂ) z.2) 4
        (volume.prod volume) =
      eLpNorm (f : ℝ → ℂ) 4 volume * eLpNorm (g : ℝ → ℂ) 4 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [enorm_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (4 : ℝ))]
  rw [lintegral_prod_mul
    (hf.aestronglyMeasurable.enorm.pow_const 4)
    (hg.aestronglyMeasurable.enorm.pow_const 4)]
  rw [ENNReal.mul_rpow_of_nonneg]
  positivity

private lemma exteriorProduct_memLp_four (u v : ℝ → L2) (t : ℝ)
    (hu : MemLp (u t : ℝ → ℂ) 4 volume)
    (hv : MemLp (v t : ℝ → ℂ) 4 volume) :
    MemLp (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 4
      (volume.prod volume) := by
  have huv := tensorProduct_memLp_four (u t) (v t) hu hv
  have hvu := tensorProduct_memLp_four (v t) (u t) hv hu
  change MemLp ((fun z : ℝ × ℝ =>
    (u t : ℝ → ℂ) z.1 * (v t : ℝ → ℂ) z.2) -
      (fun z : ℝ × ℝ =>
        (v t : ℝ → ℂ) z.1 * (u t : ℝ → ℂ) z.2)) 4
          (volume.prod volume)
  exact huv.sub hvu

private lemma exteriorProduct_four_bound (u v : ℝ → L2) (t : ℝ)
    (hu : MemLp (u t : ℝ → ℂ) 4 volume)
    (hv : MemLp (v t : ℝ → ℂ) 4 volume) :
    eLpNorm (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 4
        (volume.prod volume) ≤
      2 * (eLpNorm (u t : ℝ → ℂ) 4 volume *
        eLpNorm (v t : ℝ → ℂ) 4 volume) := by
  let U : ℝ × ℝ → ℂ := fun z =>
    (u t : ℝ → ℂ) z.1 * (v t : ℝ → ℂ) z.2
  let V : ℝ × ℝ → ℂ := fun z =>
    (v t : ℝ → ℂ) z.1 * (u t : ℝ → ℂ) z.2
  have hU := tensorProduct_memLp_four (u t) (v t) hu hv
  have hV := tensorProduct_memLp_four (v t) (u t) hv hu
  calc
    eLpNorm (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 4
        (volume.prod volume) = eLpNorm (U - V) 4 (volume.prod volume) := by
          rfl
    _ ≤ eLpNorm U 4 (volume.prod volume) + eLpNorm V 4 (volume.prod volume) :=
      eLpNorm_sub_le hU.aestronglyMeasurable hV.aestronglyMeasurable (by norm_num)
    _ = _ := by
      rw [eLpNorm_tensorProduct_four (u t) (v t) hu hv,
        eLpNorm_tensorProduct_four (v t) (u t) hv hu]
      ring

private lemma zeroExtendNormal_section_four_bound (u v : ℝ → L2) (t : ℝ)
    (hu : MemLp (u t : ℝ → ℂ) 4 volume)
    (hv : MemLp (v t : ℝ → ℂ) 4 volume) :
    eLpNorm (fun z : ℝ × ℝ => zeroExtendNormal (normalExterior u v) (t, z)) 4
        (volume.prod volume) ≤
      (ENNReal.ofReal
        |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
          (1 / (4 : ℝ≥0∞)).toReal •
        (2 * (eLpNorm (u t : ℝ → ℂ) 4 volume *
          eLpNorm (v t : ℝ → ℂ) 4 volume)) := by
  let S : Set (ℝ × ℝ) := {z | z.1 < 0}
  have hraw := exteriorProduct_memLp_four u v t hu hv
  have hcomp := eLpNorm_comp_normalToParticle_le hraw
  calc
    eLpNorm (fun z : ℝ × ℝ => zeroExtendNormal (normalExterior u v) (t, z)) 4
        (volume.prod volume) =
        eLpNorm (S.indicator
          ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘ normalToParticle)) 4
            (volume.prod volume) := by
          congr 1
    _ ≤ eLpNorm ((fun z : ℝ × ℝ => exteriorProduct u v (t, z)) ∘
          normalToParticle) 4 (volume.prod volume) := eLpNorm_indicator_le _
    _ ≤ (ENNReal.ofReal
          |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
            (1 / (4 : ℝ≥0∞)).toReal •
          eLpNorm (fun z : ℝ × ℝ => exteriorProduct u v (t, z)) 4
            (volume.prod volume) := hcomp
    _ ≤ _ := smul_le_smul_of_nonneg_left (exteriorProduct_four_bound u v t hu hv)
      (by positivity)

private lemma eLpNorm_prod_le_scalarMixed_four (F : ℝ × (ℝ × ℝ) → ℂ)
    (K : Set ℝ) :
    eLpNorm F 4 ((volume.restrict K).prod (volume.prod volume)) ≤
      scalarMixedENorm (volume.restrict K) (volume.prod volume) 4 4 F := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    scalarMixedENorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    (∫⁻ p, ‖F p‖ₑ ^ (4 : ℝ)
        ∂((volume.restrict K).prod (volume.prod volume))) ≤
        ∫⁻ t, ∫⁻ z, ‖F (t, z)‖ₑ ^ (4 : ℝ)
          ∂(volume.prod volume) ∂(volume.restrict K) := lintegral_prod_le _
    _ = ∫⁻ t, ‖sectionENorm (volume.prod volume) 4 F t‖ₑ ^ (4 : ℝ)
          ∂(volume.restrict K) := by
      apply lintegral_congr
      intro t
      rw [sectionENorm,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      norm_num only [ENNReal.toReal_ofNat, enorm_eq_self]
      rw [← ENNReal.rpow_mul]
      norm_num

private theorem zeroExtendNormal_Lfour_compact (σ : ℝ) (u v : GlobalSolution σ)
    (K : Set ℝ) (hK : IsCompact K) :
    eLpNorm (zeroExtendNormal (measurableNormalExterior u v)) 4
      ((volume.restrict K).prod (volume.prod volume)) < ⊤ := by
  let Au : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative u.u) t
  let Av : ℝ → ℝ≥0∞ := fun t =>
    sectionENorm volume ⊤ (curveRepresentative v.u) t
  let Bu : ℝ → ℝ := fun t => (Au t).toReal
  let Bv : ℝ → ℝ := fun t => (Av t).toReal
  have huend := endpoint_control σ u K hK.measurableSet hK.isBounded
  have hvend := endpoint_control σ v K hK.measurableSet hK.isBounded
  have hBu4 : MemLp Bu 4 (volume.restrict K) := by
    simpa [Bu, Au] using huend.2.1
  have hBv4 : MemLp Bv 4 (volume.restrict K) := by
    simpa [Bv, Av] using hvend.2.1
  have hAfin : ∀ᵐ t ∂volume.restrict K, Au t < ⊤ ∧ Av t < ⊤ := by
    filter_upwards [huend.2.2, hvend.2.2] with t hut hvt
    exact ⟨hut, hvt⟩
  have hucomp : IsCompact (u.u '' K) :=
    hK.image_of_continuousOn u.continuous.continuousOn
  have hvcomp : IsCompact (v.u '' K) :=
    hK.image_of_continuousOn v.continuous.continuousOn
  obtain ⟨Mu, hMupos, hMu⟩ := hucomp.isBounded.subset_closedBall_lt 0 (0 : L2)
  obtain ⟨Mv, hMvpos, hMv⟩ := hvcomp.isBounded.subset_closedBall_lt 0 (0 : L2)
  let jac : ℝ≥0∞ := (ENNReal.ofReal
    |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
      (1 / (4 : ℝ≥0∞)).toReal
  let D : ℝ≥0∞ := jac * 2 *
    ((ENNReal.ofReal Mu) ^ (1 / 2 : ℝ) * (ENNReal.ofReal Mv) ^ (1 / 2 : ℝ))
  have hjac : jac ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · positivity
    · exact ENNReal.ofReal_ne_top
  have hD : D ≠ ⊤ := by
    dsimp [D]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top hjac (by norm_num)
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have hsection : ∀ᵐ t ∂volume.restrict K,
      sectionENorm (volume.prod volume) 4
          (zeroExtendNormal (measurableNormalExterior u v)) t ≤
        D * (ENNReal.ofReal (Bu t * Bv t)) ^ (1 / 2 : ℝ) := by
    filter_upwards [hAfin, ae_restrict_mem hK.measurableSet] with t htfin htK
    have huTop : eLpNorm (u.u t : ℝ → ℂ) ⊤ volume = Au t := by
      rfl
    have hvTop : eLpNorm (v.u t : ℝ → ℂ) ⊤ volume = Av t := by
      rfl
    have hu2 : eLpNorm (u.u t : ℝ → ℂ) 2 volume ≤ ENNReal.ofReal Mu := by
      rw [← Lp.enorm_def]
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have hm := hMu ⟨t, htK, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    have hv2 : eLpNorm (v.u t : ℝ → ℂ) 2 volume ≤ ENNReal.ofReal Mv := by
      rw [← Lp.enorm_def]
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have hm := hMv ⟨t, htK, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    have hu4bound : eLpNorm (u.u t : ℝ → ℂ) 4 volume ≤
        (ENNReal.ofReal Mu) ^ (1 / 2 : ℝ) * (Au t) ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ eLpNorm (u.u t : ℝ → ℂ) 2 volume ^ (1 / 2 : ℝ) *
            eLpNorm (u.u t : ℝ → ℂ) ⊤ volume ^ (1 / 2 : ℝ) :=
          spatial_interp volume (u.u t : ℝ → ℂ) (Lp.aestronglyMeasurable (u.u t))
        _ ≤ _ := by rw [huTop]; gcongr
    have hv4bound : eLpNorm (v.u t : ℝ → ℂ) 4 volume ≤
        (ENNReal.ofReal Mv) ^ (1 / 2 : ℝ) * (Av t) ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ eLpNorm (v.u t : ℝ → ℂ) 2 volume ^ (1 / 2 : ℝ) *
            eLpNorm (v.u t : ℝ → ℂ) ⊤ volume ^ (1 / 2 : ℝ) :=
          spatial_interp volume (v.u t : ℝ → ℂ) (Lp.aestronglyMeasurable (v.u t))
        _ ≤ _ := by rw [hvTop]; gcongr
    have huRtop : (ENNReal.ofReal Mu) ^ (1 / 2 : ℝ) *
        (Au t) ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) htfin.1.ne)
    have hvRtop : (ENNReal.ofReal Mv) ^ (1 / 2 : ℝ) *
        (Av t) ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) htfin.2.ne)
    have hu4 : MemLp (u.u t : ℝ → ℂ) 4 volume :=
      ⟨Lp.aestronglyMeasurable (u.u t), hu4bound.trans_lt huRtop⟩
    have hv4 : MemLp (v.u t : ℝ → ℂ) 4 volume :=
      ⟨Lp.aestronglyMeasurable (v.u t), hv4bound.trans_lt hvRtop⟩
    have hsec := zeroExtendNormal_section_four_bound u.u v.u t hu4 hv4
    have hAu : ENNReal.ofReal (Bu t) = Au t := by
      simpa [Bu] using ENNReal.ofReal_toReal htfin.1.ne
    have hAv : ENNReal.ofReal (Bv t) = Av t := by
      simpa [Bv] using ENNReal.ofReal_toReal htfin.2.ne
    calc
      sectionENorm (volume.prod volume) 4
          (zeroExtendNormal (measurableNormalExterior u v)) t =
          sectionENorm (volume.prod volume) 4
            (zeroExtendNormal (normalExterior u.u v.u)) t :=
        zeroExtendNormal_measurable_sectionENorm u v t 4
      _ =
          eLpNorm (fun z : ℝ × ℝ =>
            zeroExtendNormal (normalExterior u.u v.u) (t, z)) 4
            (volume.prod volume) := rfl
      _ ≤ jac • (2 * (eLpNorm (u.u t : ℝ → ℂ) 4 volume *
          eLpNorm (v.u t : ℝ → ℂ) 4 volume)) := by simpa [jac] using hsec
      _ ≤ jac • (2 * (((ENNReal.ofReal Mu) ^ (1 / 2 : ℝ) *
          (Au t) ^ (1 / 2 : ℝ)) * ((ENNReal.ofReal Mv) ^ (1 / 2 : ℝ) *
          (Av t) ^ (1 / 2 : ℝ)))) := by
            exact smul_le_smul_of_nonneg_left
              (mul_le_mul_left' (mul_le_mul hu4bound hv4bound (by positivity) (by positivity)) 2)
              (by positivity)
      _ = D * (Au t * Av t) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        change jac * (2 * (((ENNReal.ofReal Mu) ^ (1 / 2 : ℝ) *
          (Au t) ^ (1 / 2 : ℝ)) * ((ENNReal.ofReal Mv) ^ (1 / 2 : ℝ) *
          (Av t) ^ (1 / 2 : ℝ)))) = _
        dsimp [D]
        ring
      _ = D * (ENNReal.ofReal (Bu t * Bv t)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg)]
        rw [hAu, hAv]
  let P : ℝ → ℝ := fun t => Bu t * Bv t
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    change ((4 : NNReal) : ENNReal)⁻¹ + ((4 : NNReal) : ENNReal)⁻¹ =
      ((2 : NNReal) : ENNReal)⁻¹
    change ((4 : NNReal)⁻¹ : ENNReal) + ((4 : NNReal)⁻¹ : ENNReal) =
      ((2 : NNReal)⁻¹ : ENNReal)
    norm_cast
    norm_num⟩
  have hP2 : MemLp P 2 (volume.restrict K) := by
    change MemLp (Bu * Bv) 2 (volume.restrict K)
    exact MemLp.mul (p := 4) (q := 4) (r := 2) hBv4 hBu4
  have hroot : MemLp (fun t => ‖P t‖ ^ (1 / 2 : ℝ)) 4
      (volume.restrict K) := by
    have h := hP2.norm_rpow_div (1 / 2 : ℝ≥0∞)
    convert h using 1 <;> norm_num [div_eq_mul_inv]
  let d : ℝ := D.toReal
  let R : ℝ → ℝ := fun t => d * ‖P t‖ ^ (1 / 2 : ℝ)
  have hR : MemLp R 4 (volume.restrict K) := by
    change MemLp (d • (fun t => ‖P t‖ ^ (1 / 2 : ℝ))) 4 (volume.restrict K)
    exact hroot.const_smul d
  have hmixed : scalarMixedENorm (volume.restrict K) (volume.prod volume) 4 4
      (zeroExtendNormal (measurableNormalExterior u v)) < ⊤ := by
    unfold scalarMixedENorm
    apply lt_of_le_of_lt (eLpNorm_mono_enorm_ae (p := (4 : ℝ≥0∞)) ?_)
      hR.eLpNorm_lt_top
    filter_upwards [hsection] with t ht
    have hP0 : 0 ≤ P t := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    calc
      ‖sectionENorm (volume.prod volume) 4
          (zeroExtendNormal (measurableNormalExterior u v)) t‖ₑ =
          sectionENorm (volume.prod volume) 4
            (zeroExtendNormal (measurableNormalExterior u v)) t := enorm_eq_self _
      _ ≤ D * (ENNReal.ofReal (P t)) ^ (1 / 2 : ℝ) := by simpa [P] using ht
      _ = ‖R t‖ₑ := by
        change D * (ENNReal.ofReal (P t)) ^ (1 / 2 : ℝ) =
          ‖d * ‖P t‖ ^ (1 / 2 : ℝ)‖ₑ
        symm
        rw [Real.enorm_eq_ofReal (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _))]
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        rw [ENNReal.ofReal_toReal hD]
        congr 1
        rw [Real.norm_eq_abs, abs_of_nonneg hP0,
          ENNReal.ofReal_rpow_of_nonneg hP0 (by positivity)]
  exact (eLpNorm_prod_le_scalarMixed_four
    (zeroExtendNormal (measurableNormalExterior u v)) K).trans_lt hmixed

/--
`lem:F-vanishing`: reflection and half-space unique continuation annihilate the
exterior product at every time in the observation interval. The accompanying
norm equality is the all-time density consequence used by the Hilbert lemma.
-/
theorem F_vanishing (σ : ℝ) (u v : GlobalSolution σ)
    (a b : ℝ) (hab : a < b) (hmod : SameModulusOn a b u.u v.u) :
  ∀ t ∈ Set.Ioo a b,
    (∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      (u.u t : ℝ → ℂ) p.1 * (v.u t : ℝ → ℂ) p.2 -
        (v.u t : ℝ → ℂ) p.1 * (u.u t : ℝ → ℂ) p.2 = 0) ∧
    ‖u.u t‖ = ‖v.u t‖ := by
  let J : Set ℝ := Set.Ioo a b
  let F : Spacetime2 := measurableNormalExterior u v
  let G : Spacetime2 := zeroExtendNormal F
  let Q : Spacetime2 := measurableRidgePotential σ u
  have hJopen : IsOpen J := isOpen_Ioo
  have hGweak : IsWeakTwoParticleEquationOn J G (zeroExtendForcing Q F) := by
    simpa [G, F, Q, J] using zero_extension_jump σ u v a b hab hmod
  have hforcing : zeroExtendForcing Q F = fun p => Q p * G p := by
    funext p
    simp only [zeroExtendForcing, G, zeroExtendNormal]
    split_ifs <;> simp_all
  have heq : IsWeakPotentialEquation J G Q := by
    rw [IsWeakPotentialEquation, ← hforcing]
    intro Ψ hΨ hc hs
    rcases hGweak Ψ hΨ hc hs with ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Measure.volume_eq_prod] using h0
    · simpa only [schrodinger2DAdjointTest, twoParticleAdjointTest,
        Measure.volume_eq_prod] using h1
    · simpa only [Measure.volume_eq_prod] using h2
    · simpa only [schrodinger2DAdjointTest, twoParticleAdjointTest] using h3
  have hX : ∀ K : Set ℝ, IsCompact K → K ⊆ J →
      carlemanXprimeNorm K G < ⊤ := by
    intro K hK hKJ
    have hGmeas : AEStronglyMeasurable G
        ((volume.restrict K).prod (volume.prod volume)) := by
      dsimp [G, F]
      exact (zeroExtendNormal_measurable'
        (measurableNormalExterior_measurable u v)).aestronglyMeasurable
    rw [carlemanXprimeNorm, if_pos hGmeas]
    simpa [G, F] using
      zeroExtendNormal_LinftyL2_compact σ u v K hK
  have hzero : VanishesAbove 0 (restrictTimeField J G) := by
    filter_upwards with p
    intro hp
    by_cases ht : p.1 ∈ J
    · rw [restrictTimeField, Set.indicator_of_mem]
      · simp [G, zeroExtendNormal, not_lt_of_ge (le_of_lt hp)]
      · exact ⟨ht, Set.mem_univ _⟩
    · simp [restrictTimeField, ht]
  intro t ht
  have htJ : t ∈ J := ht
  obtain ⟨c0, hc0, hpropagate⟩ := halfspace_small_L1Linfty
  obtain ⟨r, hr, hIccJ, hQsmall⟩ :=
    ridgePotential_small_symmetric_interval σ u a b t c0 ht hc0
  let I : Set ℝ := Set.Ioo (t - r) (t + r)
  let Jlocal : Set ℝ :=
    Set.Ioo ((t - r) + ((t + r) - (t - r)) / 8)
      ((t + r) - ((t + r) - (t - r)) / 8)
  have hIJ : I ⊆ J := by
    intro s hs
    exact hIccJ ⟨hs.1.le, hs.2.le⟩
  have hIIcc : I ⊆ Set.Icc (t - r) (t + r) := fun _ hs => ⟨hs.1.le, hs.2.le⟩
  have hXI : carlemanXprimeNorm I G < ⊤ :=
    (carlemanXprimeNorm_mono hIIcc G).trans_lt
      (hX (Set.Icc (t - r) (t + r)) isCompact_Icc hIccJ)
  have heqI : IsWeakPotentialEquation I G Q := weakPotentialEquation_mono hIJ heq
  have hzeroI : VanishesAbove 0 (restrictTimeField I G) :=
    vanishesAbove_restrict_mono hIJ hzero
  have hQsmall' : scalarMixedENorm (volume.restrict I) (volume.prod volume) 1 ⊤ Q ≤
      ENNReal.ofReal c0 := by simpa [I, Q] using hQsmall
  have hQmeas : AEStronglyMeasurable Q
      ((volume.restrict I).prod (volume.prod volume)) := by
    dsimp [Q]
    exact (measurableRidgePotential_measurable σ u).aestronglyMeasurable
  have hGzero : ∀ᵐ p ∂((volume.restrict Jlocal).prod (volume.prod volume)), G p = 0 := by
    simpa [I, Jlocal] using
      hpropagate (t - r) (t + r) 0 G Q (by linarith) heqI hXI hQmeas hQsmall' hzeroI
  have hJlocalOpen : IsOpen Jlocal := isOpen_Ioo
  have htJlocal : t ∈ Jlocal := by
    dsimp [Jlocal]
    constructor <;> linarith
  have hGslices : ∀ᵐ t ∂volume.restrict Jlocal,
      ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), G (t, z) = 0 :=
    Measure.ae_ae_of_ae_prod hGzero
  have hnormal : ∀ᵐ t ∂volume.restrict Jlocal,
      ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), F (t, z) = 0 := by
    filter_upwards [hGslices] with t ht
    have htr := normalReflection_quasiMeasurePreserving.ae ht
    filter_upwards [ht, htr] with z hz hzr
    by_cases hneg : z.1 < 0
    · simpa [G, zeroExtendNormal, hneg] using hz
    by_cases hz0 : z.1 = 0
    · rcases z with ⟨s, r⟩
      simp only at hz0
      subst s
      dsimp [F, measurableNormalExterior, fromNormalCoordinates, measurableExterior]
      ring
    · have hpos : 0 < z.1 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz0)
      have hrneg : (normalReflection z).1 < 0 := by simp [normalReflection, hpos]
      have hFr : F (t, normalReflection z) = 0 := by
        simpa [G, zeroExtendNormal, hrneg] using hzr
      change measurableNormalExterior u v (t, normalReflection z) = 0 at hFr
      rw [measurableNormalExterior_reflection] at hFr
      exact neg_eq_zero.mp hFr
  have hexterior : ∀ᵐ t ∂volume.restrict Jlocal,
      ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), exteriorProduct u.u v.u (t, z) = 0 := by
    filter_upwards [hnormal] with t ht
    have hraw : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
        normalExterior u.u v.u (t, z) = 0 := by
      filter_upwards [measurableNormalExterior_slice u v t, ht] with z hrep hz
      exact hrep.symm.trans hz
    exact exterior_ae_zero_of_normal_ae_zero u.u v.u t hraw
  have hcurve_ae :
      (fun t => exteriorProductL2 (u.u t) (v.u t)) =ᵐ[volume.restrict Jlocal]
        (fun _ => (0 : TwoParticleL2)) := by
    filter_upwards [hexterior] with t ht
    apply Lp.ext
    filter_upwards [coe_exteriorProductL2 (u.u t) (v.u t), ht] with z hcoe hz
    rw [hcoe]
    simpa [exteriorProduct] using hz
  have hcurve : Set.EqOn (fun t => exteriorProductL2 (u.u t) (v.u t))
      (fun _ => (0 : TwoParticleL2)) Jlocal :=
    Measure.eqOn_open_of_ae_eq hcurve_ae hJlocalOpen
      (continuous_exteriorProductL2 u.u v.u u.continuous v.continuous).continuousOn
      continuous_const.continuousOn
  constructor
  · have hcoe := coe_exteriorProductL2 (u.u t) (v.u t)
    have hEt : exteriorProductL2 (u.u t) (v.u t) = 0 := by
      simpa using hcurve htJlocal
    rw [hEt] at hcoe
    filter_upwards [hcoe, Lp.coeFn_zero ℂ 2 (volume.prod volume)] with p hp hzeroLp
    simpa using hp.symm.trans hzeroLp
  · have hdensity := density_on_open σ u v J hJopen hmod t htJ
    have hnorm_ae : ∀ᵐ x : ℝ ∂volume,
        ‖(u.u t : ℝ → ℂ) x‖ = ‖(v.u t : ℝ → ℂ) x‖ := by
      filter_upwards [hdensity] with x hx
      nlinarith [norm_nonneg ((u.u t : ℝ → ℂ) x), norm_nonneg ((v.u t : ℝ → ℂ) x)]
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae hnorm_ae

private lemma cubic_pointwise_lipschitz (z w : ℂ) :
    ‖((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w‖ ≤
      (‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2) * ‖z - w‖ := by
  have hzsq : ((‖z‖ ^ 2 : ℝ) : ℂ) = (Complex.normSq z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
  have hwsq : ((‖w‖ ^ 2 : ℝ) : ℂ) = (Complex.normSq w : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
  rw [hzsq, hwsq, Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_conj_mul_self]
  have halg :
      starRingEnd ℂ z * z * z - starRingEnd ℂ w * w * w =
        (starRingEnd ℂ z - starRingEnd ℂ w) * z * z +
          starRingEnd ℂ w * (z - w) * z + starRingEnd ℂ w * w * (z - w) := by ring
  rw [halg]
  calc
    ‖(starRingEnd ℂ z - starRingEnd ℂ w) * z * z +
          starRingEnd ℂ w * (z - w) * z + starRingEnd ℂ w * w * (z - w)‖
        ≤ ‖(starRingEnd ℂ z - starRingEnd ℂ w) * z * z‖ +
            ‖starRingEnd ℂ w * (z - w) * z‖ + ‖starRingEnd ℂ w * w * (z - w)‖ := by
          calc
            _ ≤ ‖(starRingEnd ℂ z - starRingEnd ℂ w) * z * z +
                  starRingEnd ℂ w * (z - w) * z‖ +
                ‖starRingEnd ℂ w * w * (z - w)‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ = (‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2) * ‖z - w‖ := by
      simp only [norm_mul]
      rw [← map_sub, RCLike.norm_conj, RCLike.norm_conj]
      ring

private lemma cubic_difference_norm (f g nf ng : L2)
    (hnf : (nf : ℝ → ℂ) =ᵐ[volume]
      fun x => ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x)
    (hng : (ng : ℝ → ℂ) =ᵐ[volume]
      fun x => ((‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) * (g : ℝ → ℂ) x)
    (Af Ag : ℝ) (hAf : 0 ≤ Af) (hAg : 0 ≤ Ag)
    (hf : ∀ᵐ x : ℝ ∂volume, ‖(f : ℝ → ℂ) x‖ ≤ Af)
    (hg : ∀ᵐ x : ℝ ∂volume, ‖(g : ℝ → ℂ) x‖ ≤ Ag) :
    ‖nf - ng‖ ≤ (Af ^ 2 + Af * Ag + Ag ^ 2) * ‖f - g‖ := by
  let C : ℝ := Af ^ 2 + Af * Ag + Ag ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hraw : ∀ᵐ x : ℝ ∂volume,
      ‖(nf - ng : L2) x‖ ≤ C * ‖(f - g : L2) x‖ := by
    filter_upwards [hnf, hng, Lp.coeFn_sub nf ng, Lp.coeFn_sub f g, hf, hg]
      with x hnfx hngx hnsub hfsub hfx hgx
    rw [hnsub, hfsub]
    simp only [Pi.sub_apply]
    rw [hnfx, hngx]
    have hpoint := cubic_pointwise_lipschitz ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x)
    calc
      _ ≤ (‖(f : ℝ → ℂ) x‖ ^ 2 +
          ‖(f : ℝ → ℂ) x‖ * ‖(g : ℝ → ℂ) x‖ +
          ‖(g : ℝ → ℂ) x‖ ^ 2) *
            ‖(f : ℝ → ℂ) x - (g : ℝ → ℂ) x‖ := hpoint
      _ ≤ C * ‖(f : ℝ → ℂ) x - (g : ℝ → ℂ) x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [C]
        nlinarith [norm_nonneg ((f : ℝ → ℂ) x), norm_nonneg ((g : ℝ → ℂ) x)]
  rw [Lp.norm_def, Lp.norm_def]
  have hle : eLpNorm (nf - ng : L2) 2 volume ≤
      ENNReal.ofReal C * eLpNorm (f - g : L2) 2 volume := by
    calc
      eLpNorm (nf - ng : L2) 2 volume ≤
          eLpNorm (fun x => C * ‖(f - g : L2) x‖) 2 volume :=
        eLpNorm_mono_ae_real hraw
      _ = eLpNorm (fun x => (C : ℂ) * (f - g : L2) x) 2 volume := by
        apply eLpNorm_congr_norm_ae
        filter_upwards with x
        simp [norm_mul, hC]
      _ = ENNReal.ofReal C * eLpNorm (f - g : L2) 2 volume := by
        rw [show (fun x => (C : ℂ) * (f - g : L2) x) =
            (C : ℂ) • (fun x => (f - g : L2) x) by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]]
        rw [eLpNorm_const_smul]
        rw [show ‖(C : ℂ)‖ₑ = ENNReal.ofReal C by
          rw [← ofReal_norm]
          congr 1
          simpa [abs_of_nonneg hC] using Complex.norm_real C]
  have htr := (ENNReal.toReal_le_toReal
    (Lp.memLp (nf - ng)).eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp (f - g)).eLpNorm_ne_top)).2 hle
  calc
    (eLpNorm (nf - ng : L2) 2 volume).toReal ≤
        (ENNReal.ofReal C * eLpNorm (f - g : L2) 2 volume).toReal := htr
    _ = C * (eLpNorm (f - g : L2) 2 volume).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    _ = (Af ^ 2 + Af * Ag + Ag ^ 2) *
        (eLpNorm (f - g : L2) 2 volume).toReal := rfl

private def endpointSize (u : ℝ → L2) (t : ℝ) : ℝ :=
  (sectionENorm volume ⊤ (curveRepresentative u) t).toReal

private def cubicDifferenceCoefficient (u v : ℝ → L2) (t : ℝ) : ℝ :=
  endpointSize u t ^ 2 + endpointSize u t * endpointSize v t + endpointSize v t ^ 2

private lemma global_nonlinear_difference_bound (σ : ℝ) (u v : GlobalSolution σ) :
    ∀ᵐ t : ℝ ∂volume, ‖u.nonlin t - v.nonlin t‖ ≤
      cubicDifferenceCoefficient u.u v.u t * ‖u.u t - v.u t‖ := by
  have hfinite : ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Icc (-(n : ℝ)) n →
        sectionENorm volume ⊤ (curveRepresentative u.u) t < ⊤ ∧
        sectionENorm volume ⊤ (curveRepresentative v.u) t < ⊤ := by
    intro n
    have hu := (endpoint_control σ u (Set.Icc (-(n : ℝ)) n)
      measurableSet_Icc isCompact_Icc.isBounded).2.2
    have hv := (endpoint_control σ v (Set.Icc (-(n : ℝ)) n)
      measurableSet_Icc isCompact_Icc.isBounded).2.2
    filter_upwards [ae_imp_of_ae_restrict hu, ae_imp_of_ae_restrict hv]
      with t hut hvt ht
    exact ⟨hut ht, hvt ht⟩
  have hfinite_all : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      t ∈ Set.Icc (-(n : ℝ)) n →
        sectionENorm volume ⊤ (curveRepresentative u.u) t < ⊤ ∧
        sectionENorm volume ⊤ (curveRepresentative v.u) t < ⊤ :=
    ae_all_iff.2 hfinite
  filter_upwards [hfinite_all, u.nonlin_eq, v.nonlin_eq] with t ht hnlu hnlv
  obtain ⟨n : ℕ, hn : |t| < n⟩ := exists_nat_gt |t|
  have htI : t ∈ Set.Icc (-(n : ℝ)) n := by
    constructor
    · linarith [neg_abs_le t]
    · exact (le_abs_self t).trans hn.le
  obtain ⟨huTop, hvTop⟩ := ht n htI
  have huTop' : eLpNormEssSup (u.u t : ℝ → ℂ) volume < ⊤ := by
    simpa [sectionENorm, eLpNorm_exponent_top, curveRepresentative] using huTop
  have hvTop' : eLpNormEssSup (v.u t : ℝ → ℂ) volume < ⊤ := by
    simpa [sectionENorm, eLpNorm_exponent_top, curveRepresentative] using hvTop
  have huBound : ∀ᵐ x : ℝ ∂volume,
      ‖(u.u t : ℝ → ℂ) x‖ ≤ endpointSize u.u t := by
    filter_upwards [ae_le_eLpNormEssSup (f := (u.u t : ℝ → ℂ)) (μ := volume)] with x hx
    have hle : ENNReal.ofReal ‖(u.u t : ℝ → ℂ) x‖ ≤
        eLpNormEssSup (u.u t : ℝ → ℂ) volume := by
      simpa [ofReal_norm] using hx
    have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top huTop'.ne).2 hle
    simpa [endpointSize, sectionENorm, eLpNorm_exponent_top, curveRepresentative,
      ENNReal.toReal_ofReal (norm_nonneg _)] using hr
  have hvBound : ∀ᵐ x : ℝ ∂volume,
      ‖(v.u t : ℝ → ℂ) x‖ ≤ endpointSize v.u t := by
    filter_upwards [ae_le_eLpNormEssSup (f := (v.u t : ℝ → ℂ)) (μ := volume)] with x hx
    have hle : ENNReal.ofReal ‖(v.u t : ℝ → ℂ) x‖ ≤
        eLpNormEssSup (v.u t : ℝ → ℂ) volume := by
      simpa [ofReal_norm] using hx
    have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hvTop'.ne).2 hle
    simpa [endpointSize, sectionENorm, eLpNorm_exponent_top, curveRepresentative,
      ENNReal.toReal_ofReal (norm_nonneg _)] using hr
  exact cubic_difference_norm (u.u t) (v.u t) (u.nonlin t) (v.nonlin t)
    hnlu hnlv (endpointSize u.u t) (endpointSize v.u t)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg huBound hvBound

private lemma cubicDifferenceCoefficient_integrableOn (σ : ℝ)
    (u v : GlobalSolution σ) (T : ℝ) :
    IntegrableOn (cubicDifferenceCoefficient u.u v.u) (Set.Icc (-T) T) := by
  have hu4 : MemLp (endpointSize u.u) 4
      (volume.restrict (Set.Icc (-T) T)) := by
    change MemLp (fun t =>
      (sectionENorm volume ⊤ (curveRepresentative u.u) t).toReal) 4 _
    exact (endpoint_control σ u (Set.Icc (-T) T) measurableSet_Icc
      isCompact_Icc.isBounded).2.1
  have hv4 : MemLp (endpointSize v.u) 4
      (volume.restrict (Set.Icc (-T) T)) := by
    change MemLp (fun t =>
      (sectionENorm volume ⊤ (curveRepresentative v.u) t).toReal) 4 _
    exact (endpoint_control σ v (Set.Icc (-T) T) measurableSet_Icc
      isCompact_Icc.isBounded).2.1
  have hu2 : MemLp (endpointSize u.u) 2 (volume.restrict (Set.Icc (-T) T)) :=
    hu4.mono_exponent (by norm_num)
  have hv2 : MemLp (endpointSize v.u) 2 (volume.restrict (Set.Icc (-T) T)) :=
    hv4.mono_exponent (by norm_num)
  have huv1 : MemLp (fun t => endpointSize u.u t * endpointSize v.u t) 1
      (volume.restrict (Set.Icc (-T) T)) := by
    exact hv2.mul' hu2
  exact (hu2.integrable_sq.add (memLp_one_iff_integrable.mp huv1)).add hv2.integrable_sq

/--
`lem:Hilbert-wedge`: if the exterior product of two L² functions vanishes almost
everywhere and their norms agree, they differ by one unimodular scalar.

This formulation uses the product-a.e. representative of equality in `L²(ℝ²)`, which is
the exact form produced after `lem:F-vanishing`.
-/
theorem hilbert_wedge (f g : L2)
    (hwedge : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2 -
        (g : ℝ → ℂ) p.1 * (f : ℝ → ℂ) p.2 = 0)
    (hnorm : ‖f‖ = ‖g‖) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ g = ζ • f := by
  by_cases hf : f = 0
  · subst f
    have hg : g = 0 := by
      apply norm_eq_zero.mp
      simpa using hnorm.symm
    subst g
    exact ⟨1, by simp, by simp⟩
  · have hf_ae : ¬∀ᵐ x : ℝ ∂volume, (f : ℝ → ℂ) x = 0 := by
      intro h
      apply hf
      apply Lp.ext (g := (0 : L2))
      filter_upwards [h] with x hx
      simpa using hx
    have hf_freq : ∃ᶠ x : ℝ in ae volume, (f : ℝ → ℂ) x ≠ 0 :=
      (not_eventually.mp hf_ae)
    have hsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
        (f : ℝ → ℂ) x * (g : ℝ → ℂ) y -
          (g : ℝ → ℂ) x * (f : ℝ → ℂ) y = 0 :=
      Measure.ae_ae_of_ae_prod hwedge
    obtain ⟨x, hfx, hx⟩ := (hf_freq.and_eventually hsections).exists
    let ζ : ℂ := (g : ℝ → ℂ) x / (f : ℝ → ℂ) x
    have hgf : g = ζ • f := by
      apply Lp.ext
      filter_upwards [hx, Lp.coeFn_smul ζ f] with y hy hsmul
      rw [hsmul]
      change (g : ℝ → ℂ) y = ζ * (f : ℝ → ℂ) y
      have hxy : (f : ℝ → ℂ) x * (g : ℝ → ℂ) y =
          (g : ℝ → ℂ) x * (f : ℝ → ℂ) y := sub_eq_zero.mp hy
      dsimp [ζ]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hfx).2
      simpa [mul_comm] using hxy
    refine ⟨ζ, ?_, hgf⟩
    have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hscale : ‖f‖ = ‖ζ‖ * ‖f‖ := by
      calc
        ‖f‖ = ‖g‖ := hnorm
        _ = ‖ζ • f‖ := congrArg norm hgf
        _ = ‖ζ‖ * ‖f‖ := norm_smul ζ f
    nlinarith

/-- Multiplication by a unimodular constant preserves the canonical global
solution interface. -/
private def phaseRotate (σ : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (u : GlobalSolution σ) : GlobalSolution σ where
  u := fun t => ζ • u.u t
  continuous := (continuous_const_smul ζ).comp u.continuous
  memL6_loc := by
    intro T
    have hsection (t : ℝ) : eLpNorm (⇑(ζ • u.u t)) 6 volume =
        eLpNorm (⇑(u.u t)) 6 volume := by
      calc
        eLpNorm (⇑(ζ • u.u t)) 6 volume =
            eLpNorm (ζ • (⇑(u.u t) : ℝ → ℂ)) 6 volume :=
          eLpNorm_congr_ae (Lp.coeFn_smul ζ (u.u t))
        _ = ‖ζ‖ₑ * eLpNorm (⇑(u.u t)) 6 volume :=
          eLpNorm_const_smul ζ _ _ _
        _ = eLpNorm (⇑(u.u t)) 6 volume := by
          rw [← ofReal_norm, hζ]
          simp
    simpa only [hsection] using u.memL6_loc T
  nonlin := fun t => ζ • u.nonlin t
  nonlin_eq := by
    filter_upwards [u.nonlin_eq] with t ht
    filter_upwards [ht, Lp.coeFn_smul ζ (u.nonlin t), Lp.coeFn_smul ζ (u.u t)]
      with x hnonlin hnonlin_smul hu_smul
    rw [hnonlin_smul, hu_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hnonlin, norm_mul, hζ, one_mul]
    ring
  forcing_integrable := by
    intro t0 t
    have h := (u.forcing_integrable t0 t).smul ζ
    rw [show (fun s => freeProp (t - s) (ζ • u.nonlin s)) =
        ζ • (fun s => freeProp (t - s) (u.nonlin s)) by
      funext s
      exact freeProp_smul ζ (t - s) (u.nonlin s)]
    exact h
  mild := by
    intro t t0
    rw [u.mild t t0]
    have hint : (∫ s in t0..t, freeProp (t - s) (ζ • u.nonlin s)) =
        ζ • ∫ s in t0..t, freeProp (t - s) (u.nonlin s) := by
      simp_rw [freeProp_smul]
      exact intervalIntegral.integral_smul ζ _
    rw [freeProp_smul, hint]
    simp only [smul_sub]
    simp only [smul_smul]
    congr 1
    rw [mul_comm ζ (Complex.I * (σ : ℂ))]

private theorem primitive_pow_integral (a : ℝ → ℝ) (t0 t : ℝ) (ht : t0 ≤ t)
    (ha : IntervalIntegrable a volume t0 t) (n : ℕ) :
    ∫ x in t0..t, a x * (∫ r in t0..x, a r) ^ n =
      (∫ r in t0..t, a r) ^ (n + 1) / (n + 1) := by
  let A : ℝ → ℝ := fun x => ∫ r in t0..x, a r
  have ht0 : t0 ∈ Set.uIcc t0 t := by simp [ht]
  have hA : AbsolutelyContinuousOnInterval A t0 t :=
    ha.absolutelyContinuousOnInterval_intervalIntegral ht0
  have hApow : ∀ k : ℕ, AbsolutelyContinuousOnInterval (A ^ (k + 1)) t0 t := by
    intro k
    induction k with
    | zero => simpa using hA
    | succ k ih =>
        convert ih.mul hA using 1
        ext x
        simp [pow_succ]
  have hderiv : ∀ᵐ x : ℝ ∂volume, x ∈ Set.uIcc t0 t →
      deriv (A ^ (n + 1)) x =
        (n + 1 : ℝ) * (a x * A x ^ n) := by
    filter_upwards [ha.ae_hasDerivAt_integral] with x hx hxt
    have hAx : HasDerivAt A (a x) x := hx hxt t0 ht0
    simpa [mul_assoc, mul_comm, mul_left_comm] using (hAx.pow (n + 1)).deriv
  have hcalc := (hApow n).integral_deriv_eq_sub
  have hrewrite :
      (∫ x in t0..t, deriv (A ^ (n + 1)) x) =
        ∫ x in t0..t, (n + 1 : ℝ) * (a x * A x ^ n) := by
    apply intervalIntegral.integral_congr_ae
    exact hderiv.mono fun x hx hmem => hx (Set.uIoc_subset_uIcc hmem)
  rw [hrewrite, intervalIntegral.integral_const_mul] at hcalc
  have hA0 : A t0 = 0 := by simp [A]
  have hmul : (n + 1 : ℝ) * (∫ x in t0..t, a x * A x ^ n) = A t ^ (n + 1) := by
    simpa [hA0] using hcalc
  change (∫ x in t0..t, a x * A x ^ n) = A t ^ (n + 1) / (n + 1 : ℝ)
  exact (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).2 (by simpa [mul_comm] using hmul)

private theorem integral_gronwall_forward (a y : ℝ → ℝ) (t0 : ℝ)
    (ha : ∀ T : ℝ, IntegrableOn a (Set.Icc (-T) T))
    (ha0 : ∀ᵐ t ∂volume, 0 ≤ a t)
    (hy0 : ∀ t, 0 ≤ y t)
    (hyb : ∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Set.Icc (-T) T, y t ≤ M)
    (hforward : ∀ t, t0 ≤ t → y t ≤ ∫ s in t0..t, a s * y s) :
    ∀ t, t0 ≤ t → y t = 0 := by
  intro t ht
  let T : ℝ := |t0| + |t| + 1
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have ht0T : t0 ∈ Set.Icc (-T) T := by
    constructor
    · calc
        -T ≤ -|t0| := by dsimp [T]; linarith [abs_nonneg t]
        _ ≤ t0 := neg_abs_le t0
    · calc
        t0 ≤ |t0| := le_abs_self t0
        _ ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have htT : t ∈ Set.Icc (-T) T := by
    constructor
    · calc
        -T ≤ -|t| := by dsimp [T]; linarith [abs_nonneg t0]
        _ ≤ t := neg_abs_le t
    · calc
        t ≤ |t| := le_abs_self t
        _ ≤ T := by dsimp [T]; linarith [abs_nonneg t0]
  have hsub : Set.Icc t0 t ⊆ Set.Icc (-T) T := by
    intro x hx
    exact ⟨(ht0T.1.trans hx.1), (hx.2.trans htT.2)⟩
  have hsubu : Set.uIcc t0 t ⊆ Set.Icc (-T) T := by
    simpa [Set.uIcc_of_le ht] using hsub
  have ha_int : IntervalIntegrable a volume t0 t :=
    (ha T).mono_set hsubu |>.intervalIntegrable
  obtain ⟨M, hM⟩ := hyb T
  have hM0 : 0 ≤ M := (hy0 t0).trans (hM t0 ht0T)
  let A : ℝ → ℝ := fun x => ∫ r in t0..x, a r
  have hbound : ∀ n : ℕ, ∀ s ∈ Set.Icc t0 t,
      y s ≤ M * A s ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro s hs
        simpa using hM s (hsub hs)
    | succ n ih =>
        intro s hs
        have hsub_s : Set.uIcc t0 s ⊆ Set.uIcc t0 t := by
          rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le ht]
          exact Set.Icc_subset_Icc_right hs.2
        have ha_s : IntervalIntegrable a volume t0 s := ha_int.mono_set hsub_s
        by_cases hay : IntervalIntegrable (fun r => a r * y r) volume t0 s
        · have hAcont : ContinuousOn A (Set.uIcc t0 s) :=
            (ha_s.absolutelyContinuousOnInterval_intervalIntegral (by simp [hs.1])).continuousOn
          have hrhs : IntervalIntegrable
              (fun r => a r * (M * A r ^ n / (n.factorial : ℝ))) volume t0 s :=
            ha_s.mul_continuousOn (by fun_prop)
          calc
            y s ≤ ∫ r in t0..s, a r * y r := hforward s hs.1
            _ ≤ ∫ r in t0..s, a r * (M * A r ^ n / (n.factorial : ℝ)) := by
              apply intervalIntegral.integral_mono_ae_restrict hs.1 hay hrhs
              filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ha0]
                with r hr har
              exact mul_le_mul_of_nonneg_left (ih r (by
                rw [← Set.uIcc_of_le ht]
                exact hsub_s (by rwa [Set.uIcc_of_le hs.1]))) har
            _ = (M / (n.factorial : ℝ)) * ∫ r in t0..s, a r * A r ^ n := by
              calc
                _ = ∫ r in t0..s, (M / (n.factorial : ℝ)) * (a r * A r ^ n) := by
                  apply intervalIntegral.integral_congr
                  intro r _
                  ring
                _ = _ := by
                  simpa using intervalIntegral.integral_const_mul
                    (M / (n.factorial : ℝ)) (fun r => a r * A r ^ n)
            _ = (M / (n.factorial : ℝ)) * (A s ^ (n + 1) / (n + 1 : ℝ)) := by
              rw [primitive_pow_integral a t0 s hs.1 ha_s n]
            _ = M * A s ^ (n + 1) / ((n + 1).factorial : ℝ) := by
              rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
              field_simp
        · have hys := hforward s hs.1
          rw [intervalIntegral.integral_undef hay] at hys
          have hAs : 0 ≤ A s := intervalIntegral.integral_nonneg_of_ae hs.1 ha0
          exact hys.trans (by positivity)
  have hlim : Tendsto (fun n : ℕ => M * (A t ^ n / (n.factorial : ℝ))) atTop (𝓝 0) :=
    by simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (A t)).const_mul M
  have hle : y t ≤ 0 := ge_of_tendsto' hlim fun n => by
    simpa [mul_div_assoc] using hbound n t ⟨ht, le_rfl⟩
  exact le_antisymm hle (hy0 t)

/-- `lem:integral-gronwall`: two-sided variable-coefficient integral Grönwall. -/
theorem integral_gronwall (a y : ℝ → ℝ) (t0 : ℝ)
    (ha : ∀ T : ℝ, IntegrableOn a (Set.Icc (-T) T))
    (ha0 : ∀ᵐ t ∂volume, 0 ≤ a t)
    (hy0 : ∀ t, 0 ≤ y t)
    (hyb : ∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Set.Icc (-T) T, y t ≤ M)
    (hforward : ∀ t, t0 ≤ t → y t ≤ ∫ s in t0..t, a s * y s)
    (hbackward : ∀ t, t ≤ t0 → y t ≤ ∫ s in t..t0, a s * y s) :
  ∀ t, y t = 0 := by
  have hfwd := integral_gronwall_forward a y t0 ha ha0 hy0 hyb hforward
  let ar : ℝ → ℝ := fun t => a (-t)
  let yr : ℝ → ℝ := fun t => y (-t)
  have har : ∀ T : ℝ, IntegrableOn ar (Set.Icc (-T) T) := by
    intro T
    by_cases hT : 0 ≤ T
    · have haI : IntervalIntegrable a volume (-T) T :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 (ha T)
      have harI : IntervalIntegrable ar volume (-T) T := by
        have hcomp := (IntervalIntegrable.iff_comp_neg (f := a) (a := -T) (b := T)).mp haI
        simpa [ar] using hcomp.symm
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 harI
    · have hempty : Set.Icc (-T) T = ∅ := Set.Icc_eq_empty (by linarith)
      rw [hempty]
      exact integrableOn_empty
  have har0 : ∀ᵐ t : ℝ ∂volume, 0 ≤ ar t := by
    change {t : ℝ | 0 ≤ a (-t)} ∈ ae volume
    change (fun t : ℝ => -t) ⁻¹' {t : ℝ | 0 ≤ a t} ∈ ae volume
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae ha0
  have hyr0 : ∀ t, 0 ≤ yr t := fun t => hy0 (-t)
  have hyrb : ∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Set.Icc (-T) T, yr t ≤ M := by
    intro T
    obtain ⟨M, hM⟩ := hyb T
    refine ⟨M, fun t ht => ?_⟩
    exact hM (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hyrf : ∀ t, -t0 ≤ t → yr t ≤ ∫ s in -t0..t, ar s * yr s := by
    intro t ht
    have hb := hbackward (-t) (by linarith)
    calc
      yr t = y (-t) := rfl
      _ ≤ ∫ s in -t..t0, a s * y s := hb
      _ = ∫ s in -t0..t, ar s * yr s := by
        symm
        simpa [ar, yr] using
          (intervalIntegral.integral_comp_neg
            (f := fun s : ℝ => a s * y s) (a := -t0) (b := t))
  have hbwd := integral_gronwall_forward ar yr (-t0) har har0 hyr0 hyrb hyrf
  intro t
  rcases le_total t0 t with htt | htt
  · exact hfwd t htt
  · have h := hbwd (-t) (by linarith)
    simpa [yr] using h

/-- Uniqueness of global mild solutions from the endpoint bound and the
variable-coefficient integral Grönwall lemma. -/
theorem global_solution_unique_endpoint (σ : ℝ) (u v : GlobalSolution σ) (t0 : ℝ)
    (h0 : u.u t0 = v.u t0) : ∀ t : ℝ, u.u t = v.u t := by
  let c : ℝ → ℝ := cubicDifferenceCoefficient u.u v.u
  let a : ℝ → ℝ := fun t => |σ| * c t
  let y : ℝ → ℝ := fun t => ‖u.u t - v.u t‖
  have hc : ∀ T : ℝ, IntegrableOn c (Set.Icc (-T) T) := by
    intro T
    simpa [c] using cubicDifferenceCoefficient_integrableOn σ u v T
  have ha : ∀ T : ℝ, IntegrableOn a (Set.Icc (-T) T) := by
    intro T
    change Integrable a (volume.restrict (Set.Icc (-T) T))
    simpa [a] using (hc T).const_mul |σ|
  have ha0 : ∀ᵐ t : ℝ ∂volume, 0 ≤ a t := by
    filter_upwards with t
    have hu : 0 ≤ endpointSize u.u t := ENNReal.toReal_nonneg
    have hv : 0 ≤ endpointSize v.u t := ENNReal.toReal_nonneg
    dsimp [a, c, cubicDifferenceCoefficient]
    exact mul_nonneg (abs_nonneg σ) (by nlinarith)
  have hy0 : ∀ t, 0 ≤ y t := fun t => norm_nonneg _
  have hyb : ∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Set.Icc (-T) T, y t ≤ M := by
    intro T
    have hcomp : IsCompact ((fun t => u.u t - v.u t) '' Set.Icc (-T) T) :=
      isCompact_Icc.image_of_continuousOn (u.continuous.sub v.continuous).continuousOn
    obtain ⟨M, _hMpos, hM⟩ := hcomp.isBounded.subset_closedBall_lt 0 (0 : L2)
    refine ⟨M, fun t ht => ?_⟩
    have hm := hM ⟨t, ht, rfl⟩
    simpa [y, Metric.mem_closedBall, dist_zero_right] using hm
  have hnonlin := global_nonlinear_difference_bound σ u v
  have hineq : ∀ t : ℝ, y t ≤ |∫ s in t0..t, a s * y s| := by
    intro t
    have hdiff : u.u t - v.u t =
        -(Complex.I * (σ : ℂ)) •
          ∫ s in t0..t, freeProp (t - s) (u.nonlin s - v.nonlin s) := by
      rw [u.mild t t0, v.mild t t0, h0]
      calc
        (freeProp (t - t0) (v.u t0) -
              (Complex.I * (σ : ℂ)) •
                ∫ s in t0..t, freeProp (t - s) (u.nonlin s)) -
            (freeProp (t - t0) (v.u t0) -
              (Complex.I * (σ : ℂ)) •
                ∫ s in t0..t, freeProp (t - s) (v.nonlin s)) =
            -(Complex.I * (σ : ℂ)) •
              ((∫ s in t0..t, freeProp (t - s) (u.nonlin s)) -
                ∫ s in t0..t, freeProp (t - s) (v.nonlin s)) := by module
        _ = -(Complex.I * (σ : ℂ)) •
              ∫ s in t0..t,
                (freeProp (t - s) (u.nonlin s) - freeProp (t - s) (v.nonlin s)) := by
              rw [intervalIntegral.integral_sub (u.forcing_integrable t0 t)
                (v.forcing_integrable t0 t)]
        _ = _ := by
              apply congrArg (fun z : L2 => -(Complex.I * (σ : ℂ)) • z)
              apply intervalIntegral.integral_congr
              intro s _
              exact (freeProp_sub (t - s) (u.nonlin s) (v.nonlin s)).symm
    let T : ℝ := |t0| + |t| + 1
    have ht0T : t0 ∈ Set.Icc (-T) T := by
      constructor
      · calc
          -T ≤ -|t0| := by dsimp [T]; linarith [abs_nonneg t]
          _ ≤ t0 := neg_abs_le t0
      · calc
          t0 ≤ |t0| := le_abs_self t0
          _ ≤ T := by dsimp [T]; linarith [abs_nonneg t]
    have htT : t ∈ Set.Icc (-T) T := by
      constructor
      · calc
          -T ≤ -|t| := by dsimp [T]; linarith [abs_nonneg t0]
          _ ≤ t := neg_abs_le t
      · calc
          t ≤ |t| := le_abs_self t
          _ ≤ T := by dsimp [T]; linarith [abs_nonneg t0]
    have hsub : Set.uIcc t0 t ⊆ Set.Icc (-T) T := by
      intro s hs
      rw [Set.mem_uIcc] at hs
      rcases hs with hs | hs
      · exact ⟨ht0T.1.trans hs.1, hs.2.trans htT.2⟩
      · exact ⟨htT.1.trans hs.1, hs.2.trans ht0T.2⟩
    have hcint : IntervalIntegrable c volume t0 t :=
      (hc T).mono_set hsub |>.intervalIntegrable
    have hycont : Continuous y := (u.continuous.sub v.continuous).norm
    have hcyint : IntervalIntegrable (fun s => c s * y s) volume t0 t :=
      hcint.mul_continuousOn hycont.continuousOn
    have hpoint : ∀ᵐ s : ℝ ∂volume,
        ‖freeProp (t - s) (u.nonlin s - v.nonlin s)‖ ≤ c s * y s := by
      filter_upwards [hnonlin] with s hs
      simpa only [norm_freeProp, c, y] using hs
    have hint := intervalIntegral.norm_integral_le_abs_of_norm_le
      (ae_restrict_of_ae hpoint) hcyint
    have hscale : ‖Complex.I * (σ : ℂ)‖ = |σ| := by simp [norm_mul]
    have hraw : y t ≤ |σ| * |∫ s in t0..t, c s * y s| := by
      change ‖u.u t - v.u t‖ ≤ _
      rw [hdiff, norm_smul, norm_neg, hscale]
      exact mul_le_mul_of_nonneg_left hint (abs_nonneg σ)
    have hfactor : (∫ s in t0..t, a s * y s) =
        |σ| * ∫ s in t0..t, c s * y s := by
      calc
        (∫ s in t0..t, a s * y s) =
            ∫ s in t0..t, |σ| * (c s * y s) := by
              apply intervalIntegral.integral_congr
              intro s _
              simp only [a]
              ring
        _ = _ := by
          simpa using
            (intervalIntegral.integral_const_mul (a := t0) (b := t) (|σ| : ℝ)
              (fun s : ℝ => c s * y s))
    rw [hfactor, abs_mul, abs_of_nonneg (abs_nonneg σ)]
    exact hraw
  have hforward : ∀ t, t0 ≤ t → y t ≤ ∫ s in t0..t, a s * y s := by
    intro t ht
    have h := hineq t
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg_of_ae ht
      (ha0.mono fun s hs => mul_nonneg hs (hy0 s)))] at h
    exact h
  have hbackward : ∀ t, t ≤ t0 → y t ≤ ∫ s in t..t0, a s * y s := by
    intro t ht
    have h := hineq t
    have hpos : 0 ≤ ∫ s in t..t0, a s * y s :=
      intervalIntegral.integral_nonneg_of_ae ht
        (ha0.mono fun s hs => mul_nonneg hs (hy0 s))
    rw [intervalIntegral.integral_symm t t0, abs_neg, abs_of_nonneg hpos] at h
    exact h
  have hzero := integral_gronwall a y t0 ha ha0 hy0 hyb hforward hbackward
  intro t
  exact sub_eq_zero.mp (norm_eq_zero.mp (hzero t))

/-- Flow uniqueness and gauge covariance propagate a one-time phase relation globally. -/
theorem phase_relation_of_time (σ : ℝ) (u v : GlobalSolution σ) (t0 : ℝ)
    (hwedge : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      (u.u t0 : ℝ → ℂ) p.1 * (v.u t0 : ℝ → ℂ) p.2 -
        (v.u t0 : ℝ → ℂ) p.1 * (u.u t0 : ℝ → ℂ) p.2 = 0)
    (hnorm : ‖u.u t0‖ = ‖v.u t0‖) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ t : ℝ, v.u t = ζ • u.u t := by
  obtain ⟨ζ, hζ, hphase⟩ := hilbert_wedge (u.u t0) (v.u t0) hwedge hnorm
  let zu := phaseRotate σ ζ hζ u
  have heq := global_solution_unique_endpoint σ v zu t0
    (by simpa [zu, phaseRotate] using hphase)
  exact ⟨ζ, hζ, fun t => by simpa [zu, phaseRotate] using heq t⟩

/-- `thm:main`: spacetime equal modulus gives one global unimodular phase. -/
theorem phase_retrieval_cubic_NLS (σ : ℝ) (u v : GlobalSolution σ)
    (hmod : SameModulus u.u v.u) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ t : ℝ, v.u t = ζ • u.u t := by
  have hJ : SameModulusOn 0 1 u.u v.u := hmod.mono (fun _ hp _ => hp)
  obtain ⟨hwedge, hnorm⟩ := F_vanishing σ u v 0 1 (by norm_num) hJ (1 / 2) (by norm_num)
  exact phase_relation_of_time σ u v (1 / 2) hwedge hnorm

/-- `cor:interval-version`: observation on any nonempty interval determines the phase globally. -/
theorem phase_retrieval_interval (σ : ℝ) (u v : GlobalSolution σ)
    (a b : ℝ) (hab : a < b) (hmod : SameModulusOn a b u.u v.u) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ t : ℝ, v.u t = ζ • u.u t := by
  have ht : (a + b) / 2 ∈ Set.Ioo a b := by constructor <;> linarith
  obtain ⟨hwedge, hnorm⟩ := F_vanishing σ u v a b hab hmod ((a + b) / 2) ht
  exact phase_relation_of_time σ u v ((a + b) / 2) hwedge hnorm

/-- `cor:H1-case`: the main theorem specialized to finite-energy solutions. -/
theorem phase_retrieval_H1 (σ : ℝ) (u v : GlobalSolution σ)
    (hu : TemperedDistribution.MemSobolev 1 2
      (MeasureTheory.Lp.toTemperedDistribution (u.u 0)))
    (hv : TemperedDistribution.MemSobolev 1 2
      (MeasureTheory.Lp.toTemperedDistribution (v.u 0)))
    (hmod : SameModulus u.u v.u) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ t : ℝ, v.u t = ζ • u.u t :=
  phase_retrieval_cubic_NLS σ u v hmod

/-- Mild solution of a linear Schrödinger equation with a common potential. -/
def IsLinearMildSolution (V : ℝ × ℝ → ℂ) (u forcing : ℝ → L2) : Prop :=
  Continuous u ∧
  (∀ᵐ t ∂volume, (forcing t : ℝ → ℂ) =ᵐ[volume]
    fun x => V (t, x) * (u t : ℝ → ℂ) x) ∧
  ∀ t t0, IntervalIntegrable (fun s => freeProp (t - s) (forcing s)) volume t0 t ∧
    u t = freeProp (t - t0) (u t0) - Complex.I •
      ∫ s in t0..t, freeProp (t - s) (forcing s)

end CubicNLSPhaseRetrieval
