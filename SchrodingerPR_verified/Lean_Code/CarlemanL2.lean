import Lean_Code.Carleman2D
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The selected Carleman propagator on spatial `L²`

The branch multiplier is a contraction for every nonzero time increment.
This packages that fact on the two-dimensional Plancherel space and records
the Bochner-integral estimate used by the graph closure.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

abbrev SpatialL2Two := Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))

theorem TbetaSymbol_measurable (β τ : ℝ) :
    Measurable (TbetaSymbol β τ) := by
  unfold TbetaSymbol
  apply Measurable.ite
  · exact measurableSet_lt
      (measurable_const.mul measurable_fst) measurable_const
  · fun_prop
  · exact measurable_const

theorem TbetaSymbol_norm_le_one (β τ : ℝ) (hβ : 0 < β) :
    ∀ ξ : ℝ × ℝ, ‖TbetaSymbol β τ ξ‖ ≤ 1 := by
  by_cases hτ : τ = 0
  · subst τ
    intro ξ
    simp [TbetaSymbol]
  · exact (Tbeta_symbol β τ hβ hτ).2

private lemma carlemanFrequencyProduct_memLp (β τ : ℝ) (hβ : 0 < β)
    (h : SpatialL2Two) :
    MemLp (fun ξ => TbetaSymbol β τ ξ * (h : ℝ × ℝ → ℂ) ξ) 2
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun ξ => TbetaSymbol β τ ξ * (h : ℝ × ℝ → ℂ) ξ)
      (volume.prod volume) :=
    (TbetaSymbol_measurable β τ).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable h)
  refine ((Lp.memLp h).norm).mono' hmeas ?_
  filter_upwards with ξ
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (TbetaSymbol_norm_le_one β τ hβ ξ)

/-- The frequency-side selected propagator at time increment `τ`. -/
def carlemanFrequencyPropagator (β τ : ℝ) (hβ : 0 < β)
    (h : SpatialL2Two) : SpatialL2Two :=
  MemLp.toLp (fun ξ => TbetaSymbol β τ ξ * (h : ℝ × ℝ → ℂ) ξ)
    (carlemanFrequencyProduct_memLp β τ hβ h)

theorem coeFn_carlemanFrequencyPropagator (β τ : ℝ) (hβ : 0 < β)
    (h : SpatialL2Two) :
    (carlemanFrequencyPropagator β τ hβ h : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun ξ => TbetaSymbol β τ ξ * (h : ℝ × ℝ → ℂ) ξ :=
  MemLp.coeFn_toLp _

private lemma TbetaSymbol_continuousAt_time (β τ : ℝ) (hτ : τ ≠ 0)
    (ξ : ℝ × ℝ) :
    ContinuousAt (fun r => TbetaSymbol β r ξ) τ := by
  rcases lt_or_gt_of_ne hτ with hτneg | hτpos
  · by_cases hξ : 0 < ξ.1
    · have hevent : (fun r => TbetaSymbol β r ξ) =ᶠ[𝓝 τ]
          fun r => -Complex.I * Complex.exp
            ((Complex.I *
                ((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) +
              ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) * r) := by
        filter_upwards [isOpen_Iio.mem_nhds hτneg] with r hr
        unfold TbetaSymbol
        rw [if_pos (mul_neg_of_neg_of_pos hr hξ)]
      exact (by fun_prop : ContinuousAt (fun r : ℝ => -Complex.I * Complex.exp
        ((Complex.I *
            ((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) +
          ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) * (r : ℂ))) τ).congr_of_eventuallyEq hevent
    · have hevent : (fun r => TbetaSymbol β r ξ) =ᶠ[𝓝 τ] fun _ => 0 := by
        filter_upwards [isOpen_Iio.mem_nhds hτneg] with r hr
        unfold TbetaSymbol
        rw [if_neg]
        exact not_lt_of_ge
          (mul_nonneg_of_nonpos_of_nonpos hr.le (le_of_not_gt hξ))
      exact continuousAt_const.congr_of_eventuallyEq hevent
  · by_cases hξ : ξ.1 < 0
    · have hevent : (fun r => TbetaSymbol β r ξ) =ᶠ[𝓝 τ]
          fun r => -Complex.I * Complex.exp
            ((Complex.I *
                ((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) +
              ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) * r) := by
        filter_upwards [isOpen_Ioi.mem_nhds hτpos] with r hr
        unfold TbetaSymbol
        rw [if_pos (mul_neg_of_pos_of_neg hr hξ)]
      exact (by fun_prop : ContinuousAt (fun r : ℝ => -Complex.I * Complex.exp
        ((Complex.I *
            ((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) +
          ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) * (r : ℂ))) τ).congr_of_eventuallyEq hevent
    · have hevent : (fun r => TbetaSymbol β r ξ) =ᶠ[𝓝 τ] fun _ => 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds hτpos] with r hr
        unfold TbetaSymbol
        rw [if_neg]
        exact not_lt_of_ge (mul_nonneg hr.le (le_of_not_gt hξ))
      exact continuousAt_const.congr_of_eventuallyEq hevent

/-- For fixed spatial data, the selected multiplier curve is continuous away
from its single branch-switching time. -/
theorem carlemanFrequencyPropagator_continuousAt
    (β τ : ℝ) (hβ : 0 < β) (hτ : τ ≠ 0) (h : SpatialL2Two) :
    ContinuousAt (fun r => carlemanFrequencyPropagator β r hβ h) τ := by
  unfold ContinuousAt carlemanFrequencyPropagator
  apply Lp.tendsto_Lp_of_tendsto_eLpNorm
    (fun ξ => TbetaSymbol β τ ξ * (h : ℝ × ℝ → ℂ) ξ)
    (carlemanFrequencyProduct_memLp β τ hβ h)
  have heq (r : ℝ) :
      eLpNorm
          ((MemLp.toLp
              (fun ξ => TbetaSymbol β r ξ * (h : ℝ × ℝ → ℂ) ξ)
              (carlemanFrequencyProduct_memLp β r hβ h) : ℝ × ℝ → ℂ) -
            fun ξ => TbetaSymbol β τ ξ * (h : ℝ × ℝ → ℂ) ξ)
          2 (volume.prod volume) =
        eLpNorm
          (fun ξ => (TbetaSymbol β r ξ - TbetaSymbol β τ ξ) *
            (h : ℝ × ℝ → ℂ) ξ) 2 (volume.prod volume) := by
    apply eLpNorm_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (carlemanFrequencyProduct_memLp β r hβ h)] with ξ hcoe
    rw [Pi.sub_apply, hcoe]
    ring
  simp_rw [heq]
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hint : Tendsto (fun r =>
      ∫⁻ ξ, ‖(TbetaSymbol β r ξ - TbetaSymbol β τ ξ) *
        (h : ℝ × ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂(volume.prod volume))
      (𝓝 τ) (𝓝 0) := by
    have hDCT : Tendsto (fun r =>
        ∫⁻ ξ, ‖(TbetaSymbol β r ξ - TbetaSymbol β τ ξ) *
          (h : ℝ × ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂(volume.prod volume))
        (𝓝 τ) (𝓝 (∫⁻ _ : ℝ × ℝ, (0 : ℝ≥0∞) ∂(volume.prod volume))) := by
      refine tendsto_lintegral_filter_of_dominated_convergence
        (f := fun _ => 0)
        (fun ξ => (2 * ‖(h : ℝ × ℝ → ℂ) ξ‖ₑ) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
      · filter_upwards with r
        exact (((TbetaSymbol_measurable β r).sub
          (TbetaSymbol_measurable β τ)).mul
            (Lp.stronglyMeasurable h).measurable).enorm.pow_const 2
      · filter_upwards with r
        filter_upwards with ξ
        rw [enorm_mul]
        have hsym : ‖TbetaSymbol β r ξ - TbetaSymbol β τ ξ‖ ≤ 2 := by
          calc
            _ ≤ ‖TbetaSymbol β r ξ‖ + ‖TbetaSymbol β τ ξ‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add
              (TbetaSymbol_norm_le_one β r hβ ξ)
              (TbetaSymbol_norm_le_one β τ hβ ξ)
            _ = 2 := by norm_num
        have hsymE : ‖TbetaSymbol β r ξ - TbetaSymbol β τ ξ‖ₑ ≤ 2 := by
          rw [← ofReal_norm]
          simpa using ENNReal.ofReal_le_ofReal hsym
        exact ENNReal.rpow_le_rpow
          (mul_le_mul_right' hsymE ‖(h : ℝ × ℝ → ℂ) ξ‖ₑ)
          (by norm_num : (0 : ℝ) ≤ 2)
      · rw [show (fun ξ => (2 * ‖(h : ℝ × ℝ → ℂ) ξ‖ₑ) ^ (2 : ℝ)) =
            fun ξ => 4 * ‖(h : ℝ × ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) by
          funext ξ
          rw [ENNReal.mul_rpow_of_nonneg 2 ‖(h : ℝ × ℝ → ℂ) ξ‖ₑ
            (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num]
        rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        exact ENNReal.mul_ne_top (by norm_num)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
            (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            (Lp.eLpNorm_lt_top h)).ne
      · filter_upwards with ξ
        have hs := (TbetaSymbol_continuousAt_time β τ hτ ξ).tendsto
        have hsub : Tendsto (fun r => TbetaSymbol β r ξ - TbetaSymbol β τ ξ)
            (𝓝 τ) (𝓝 0) := by simpa using hs.sub_const (TbetaSymbol β τ ξ)
        have hmul : Tendsto
            (fun r => (TbetaSymbol β r ξ - TbetaSymbol β τ ξ) *
              (h : ℝ × ℝ → ℂ) ξ) (𝓝 τ) (𝓝 0) := by
          simpa using hsub.mul_const ((h : ℝ × ℝ → ℂ) ξ)
        have henorm : Tendsto
            (fun r => ‖(TbetaSymbol β r ξ - TbetaSymbol β τ ξ) *
              (h : ℝ × ℝ → ℂ) ξ‖ₑ) (𝓝 τ) (𝓝 0) := by
          have hz := (continuous_enorm.tendsto 0).comp hmul
          rw [enorm_zero] at hz
          exact hz.congr fun _ => rfl
        simpa using henorm.ennrpow_const (2 : ℝ)
    simpa using hDCT
  convert hint.ennrpow_const (1 / ENNReal.toReal 2) using 1 <;> norm_num

/-- For fixed data, the selected multiplier curve is strongly measurable;
the only possible discontinuity is at the branch switch `τ = 0`. -/
theorem carlemanFrequencyPropagator_stronglyMeasurable
    (β : ℝ) (hβ : 0 < β) (h : SpatialL2Two) :
    StronglyMeasurable (fun τ => carlemanFrequencyPropagator β τ hβ h) := by
  have hcont : ContinuousOn
      (fun τ => carlemanFrequencyPropagator β τ hβ h) ({0} : Set ℝ)ᶜ := by
    intro τ hτ
    exact (carlemanFrequencyPropagator_continuousAt β τ hβ
      (by simpa using hτ) h).continuousWithinAt
  exact hcont.stronglyMeasurable_of_countable_compl (by simp)

/-- The selected frequency propagator is an `L²` contraction. -/
theorem carlemanFrequencyPropagator_norm_le (β τ : ℝ) (hβ : 0 < β)
    (h : SpatialL2Two) :
    ‖carlemanFrequencyPropagator β τ hβ h‖ ≤ ‖h‖ := by
  rw [carlemanFrequencyPropagator, Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top h)
  apply eLpNorm_mono_enorm_ae
  filter_upwards with ξ
  rw [enorm_mul]
  exact mul_le_of_le_one_left (by positivity) (by
    simpa [ofReal_norm] using
      ENNReal.ofReal_le_ofReal (TbetaSymbol_norm_le_one β τ hβ ξ))

private lemma carlemanFrequencyPropagator_sub
    (β τ : ℝ) (hβ : 0 < β) (f g : SpatialL2Two) :
    carlemanFrequencyPropagator β τ hβ (f - g) =
      carlemanFrequencyPropagator β τ hβ f -
        carlemanFrequencyPropagator β τ hβ g := by
  apply Lp.ext
  filter_upwards [coeFn_carlemanFrequencyPropagator β τ hβ (f - g),
    coeFn_carlemanFrequencyPropagator β τ hβ f,
    coeFn_carlemanFrequencyPropagator β τ hβ g,
    Lp.coeFn_sub f g,
    Lp.coeFn_sub (carlemanFrequencyPropagator β τ hβ f)
      (carlemanFrequencyPropagator β τ hβ g)] with ξ hfg hf hg hsub hout
  rw [hfg, hsub, hout]
  simp only [Pi.sub_apply]
  rw [hf, hg]
  ring

private lemma carlemanFrequencyPropagator_continuous_data
    (β τ : ℝ) (hβ : 0 < β) :
    Continuous (fun h : SpatialL2Two =>
      carlemanFrequencyPropagator β τ hβ h) := by
  rw [Metric.continuous_iff]
  intro g ε hε
  refine ⟨ε, hε, ?_⟩
  intro f hfg
  rw [dist_eq_norm] at hfg
  rw [dist_eq_norm, ← carlemanFrequencyPropagator_sub]
  exact (carlemanFrequencyPropagator_norm_le β τ hβ (f - g)).trans_lt hfg

/-- A strongly measurable `L²` source remains strongly measurable after
application of the time-dependent selected branch. -/
theorem carlemanFrequencyPropagator_integrand_stronglyMeasurable
    (β t : ℝ) (hβ : 0 < β) (g : ℝ → SpatialL2Two)
    (hg : StronglyMeasurable g) :
    StronglyMeasurable
      (fun s => carlemanFrequencyPropagator β (t - s) hβ (g s)) := by
  letI : MeasurableSpace SpatialL2Two := borel SpatialL2Two
  haveI : BorelSpace SpatialL2Two := ⟨rfl⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hjoint : StronglyMeasurable (Function.uncurry
      (fun h : SpatialL2Two => fun s : ℝ =>
        carlemanFrequencyPropagator β (t - s) hβ h)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro s
      exact carlemanFrequencyPropagator_continuous_data β (t - s) hβ
    · intro h
      exact (carlemanFrequencyPropagator_stronglyMeasurable β hβ h).comp_measurable
        (by fun_prop)
  exact hjoint.comp_measurable (hg.measurable.prodMk measurable_id)

/-- The selected-branch integrand is Bochner integrable for every integrable
`L²` source. -/
theorem carlemanFrequencyPropagator_integrand_integrable
    (β t : ℝ) (hβ : 0 < β) (g : ℝ → SpatialL2Two)
    (hg : Integrable g) :
    Integrable (fun s => carlemanFrequencyPropagator β (t - s) hβ (g s)) := by
  have hmeas : AEStronglyMeasurable
      (fun s => carlemanFrequencyPropagator β (t - s) hβ (g s)) := by
    refine (carlemanFrequencyPropagator_integrand_stronglyMeasurable
      β t hβ (hg.1.mk g) hg.1.stronglyMeasurable_mk).aestronglyMeasurable.congr ?_
    filter_upwards [hg.1.ae_eq_mk] with s hs
    rw [← hs]
  exact hg.mono
    hmeas
    (Filter.Eventually.of_forall fun s =>
      carlemanFrequencyPropagator_norm_le β (t - s) hβ (g s))

/-- Minkowski's inequality plus the multiplier contraction.  The explicit
integrability premise is separated out; the graph-closure construction
supplies it from strong measurability of the selected branch. -/
theorem norm_integral_carlemanFrequencyPropagator_le
    (β t : ℝ) (hβ : 0 < β) (g : ℝ → SpatialL2Two)
    (hg : Integrable g) :
    ‖∫ s, carlemanFrequencyPropagator β (t - s) hβ (g s)‖ ≤
      ∫ s, ‖g s‖ := by
  have hprop := carlemanFrequencyPropagator_integrand_integrable β t hβ g hg
  calc
    ‖∫ s, carlemanFrequencyPropagator β (t - s) hβ (g s)‖ ≤
        ∫ s, ‖carlemanFrequencyPropagator β (t - s) hβ (g s)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s, ‖g s‖ := by
      exact integral_mono hprop.norm hg.norm fun s =>
        carlemanFrequencyPropagator_norm_le β (t - s) hβ (g s)

end CubicNLSPhaseRetrieval
