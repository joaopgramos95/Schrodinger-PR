import Lean_Code.HardyPrimitive
import Lean_Code.EndpointForcing
import Mathlib.MeasureTheory.Integral.FinMeasAdditive

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

private abbrev compactTimeMeasure (a b : ℝ) : Measure ℝ :=
  volume.restrict (Icc a b)

private lemma compactTimeMeasure_univ_lt_top (a b : ℝ) :
    compactTimeMeasure a b Set.univ < ⊤ := by
  rw [compactTimeMeasure, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter]
  exact measure_Icc_lt_top

private def cumulativeCoeff (a b : ℝ) (E : Set ℝ) (t : ℝ) : ℂ :=
  (((compactTimeMeasure a b).restrict E) (Iic t)).toReal

private lemma cumulativeCoeff_measurable (a b : ℝ) (E : Set ℝ) :
    Measurable (cumulativeCoeff a b E) := by
  apply Complex.continuous_ofReal.measurable.comp
  apply Monotone.measurable
  intro s t hst
  have hfin : ((compactTimeMeasure a b).restrict E) (Iic t) ≠ ⊤ := by
    rw [Measure.restrict_apply measurableSet_Iic]
    exact (lt_of_le_of_lt (measure_mono (subset_univ _))
      (compactTimeMeasure_univ_lt_top a b)).ne
  exact ENNReal.toReal_mono
    hfin
    (measure_mono (Iic_subset_Iic.mpr hst))

private lemma norm_cumulativeCoeff_le (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) (t : ℝ) :
    ‖cumulativeCoeff a b E t‖ ≤ (compactTimeMeasure a b).real E := by
  unfold cumulativeCoeff Measure.real
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  apply ENNReal.toReal_mono
  · exact (lt_of_le_of_lt (measure_mono (subset_univ E))
      (compactTimeMeasure_univ_lt_top a b)).ne
  · rw [Measure.restrict_apply measurableSet_Iic]
    exact measure_mono inter_subset_right

private def cumulativeCoeffLp (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) : Lp ℂ ⊤ (compactTimeMeasure a b) :=
  (memLp_top_of_bound (cumulativeCoeff_measurable a b E).aestronglyMeasurable
    ((compactTimeMeasure a b).real E)
    (Filter.Eventually.of_forall (norm_cumulativeCoeff_le a b E hE))).toLp
      (cumulativeCoeff a b E)

private lemma coe_cumulativeCoeffLp (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) :
    (cumulativeCoeffLp a b E hE : ℝ → ℂ) =ᵐ[compactTimeMeasure a b]
      cumulativeCoeff a b E :=
  MemLp.coeFn_toLp _

private lemma norm_cumulativeCoeffLp_le (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) :
    ‖cumulativeCoeffLp a b E hE‖ ≤ (compactTimeMeasure a b).real E := by
  rw [Lp.norm_def]
  calc
    (eLpNorm (cumulativeCoeffLp a b E hE : ℝ → ℂ) ⊤
        (compactTimeMeasure a b)).toReal ≤
        (ENNReal.ofReal ((compactTimeMeasure a b).real E)).toReal := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      rw [eLpNorm_congr_ae (coe_cumulativeCoeffLp a b E hE),
        eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound
        (Filter.Eventually.of_forall (norm_cumulativeCoeff_le a b E hE))
    _ = (compactTimeMeasure a b).real E := by
      rw [ENNReal.toReal_ofReal]
      exact ENNReal.toReal_nonneg

private def cumulativeMulLinear (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) :
    Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b) →ₗ[ℝ]
      Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b) where
  toFun v := cumulativeCoeffLp a b E hE • v
  map_add' v w := Lp.add_smul (p := ⊤) (q := 2) (r := 2) _ _ _
  map_smul' c v := by
    rw [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (cumulativeCoeffLp a b E hE) (c • v),
      Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (cumulativeCoeffLp a b E hE) v,
      Lp.coeFn_smul c v,
      Lp.coeFn_smul c (cumulativeCoeffLp a b E hE • v)]
      with x hleft hright hv hout
    rw [hleft, hout]
    change (cumulativeCoeffLp a b E hE : ℝ → ℂ) x •
        ((c • v : Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b)) :
          ℝ → Hs (1 / 2 : ℝ)) x =
      c • ((cumulativeCoeffLp a b E hE • v :
        Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b)) :
          ℝ → Hs (1 / 2 : ℝ)) x
    rw [hv, hright]
    exact smul_comm
      ((cumulativeCoeffLp a b E hE : ℝ → ℂ) x) (c : ℝ)
      ((v : ℝ → Hs (1 / 2 : ℝ)) x)

private def cumulativeMulCLM (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) :
    Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b) →L[ℝ]
      Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b) :=
  (cumulativeMulLinear a b E hE).mkContinuous
    ((compactTimeMeasure a b).real E) fun v => by
      exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_cumulativeCoeffLp_le a b E hE) (norm_nonneg v))

private def simpleRetardedSetOperator
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (E : Set ℝ) :
    L2 →L[ℝ] Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b) := by
  classical
  exact if hE : MeasurableSet E then
      (cumulativeMulCLM a b E hE).comp (localizedFreeCurveCLM chi a b)
    else 0

private lemma simpleRetardedSetOperator_apply_of_measurable
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) (f : L2) :
    simpleRetardedSetOperator chi a b E f =
      cumulativeCoeffLp a b E hE • localizedFreeCurveCLM chi a b f := by
  simp [simpleRetardedSetOperator, hE, cumulativeMulCLM,
    cumulativeMulLinear]

private lemma norm_simpleRetardedSetOperator_le
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E) :
    ‖simpleRetardedSetOperator chi a b E‖ ≤
      localizedFreeBound chi a b * (compactTimeMeasure a b).real E := by
  refine ContinuousLinearMap.opNorm_le_bound
    (simpleRetardedSetOperator chi a b E)
    (mul_nonneg (localizedFreeBound_nonneg chi a b) ENNReal.toReal_nonneg) ?_
  intro f
  rw [simpleRetardedSetOperator_apply_of_measurable chi a b E hE]
  calc
    ‖cumulativeCoeffLp a b E hE • localizedFreeCurveCLM chi a b f‖ ≤
        ‖cumulativeCoeffLp a b E hE‖ * ‖localizedFreeCurveCLM chi a b f‖ :=
      Lp.norm_smul_le _ _
    _ ≤ (compactTimeMeasure a b).real E *
        (localizedFreeBound chi a b * ‖f‖) := by
      gcongr
      · exact norm_cumulativeCoeffLp_le a b E hE
      · exact norm_localizedFreeCurveCLM_le chi a b f
    _ = (localizedFreeBound chi a b * (compactTimeMeasure a b).real E) * ‖f‖ := by
      ring

private lemma cumulativeCoeff_union (a b : ℝ) (E F : Set ℝ)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : Disjoint E F)
    (t : ℝ) :
    cumulativeCoeff a b (E ∪ F) t =
      cumulativeCoeff a b E t + cumulativeCoeff a b F t := by
  unfold cumulativeCoeff
  rw [Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  rw [Set.inter_union_distrib_left]
  have hdis : Disjoint (Iic t ∩ E) (Iic t ∩ F) :=
    hEF.mono inter_subset_right inter_subset_right
  rw [measure_union hdis (measurableSet_Iic.inter hF)]
  rw [ENNReal.toReal_add]
  · norm_cast
  · exact (lt_of_le_of_lt (measure_mono (subset_univ _))
      (compactTimeMeasure_univ_lt_top a b)).ne
  · exact (lt_of_le_of_lt (measure_mono (subset_univ _))
      (compactTimeMeasure_univ_lt_top a b)).ne

private lemma cumulativeCoeffLp_union (a b : ℝ) (E F : Set ℝ)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : Disjoint E F) :
    cumulativeCoeffLp a b (E ∪ F) (hE.union hF) =
      cumulativeCoeffLp a b E hE + cumulativeCoeffLp a b F hF := by
  apply Lp.ext
  filter_upwards [coe_cumulativeCoeffLp a b (E ∪ F) (hE.union hF),
    coe_cumulativeCoeffLp a b E hE, coe_cumulativeCoeffLp a b F hF,
    Lp.coeFn_add (cumulativeCoeffLp a b E hE)
      (cumulativeCoeffLp a b F hF)] with t hUnion hEc hFc hAdd
  rw [hUnion, hAdd]
  change cumulativeCoeff a b (E ∪ F) t =
    (cumulativeCoeffLp a b E hE : ℝ → ℂ) t +
      (cumulativeCoeffLp a b F hF : ℝ → ℂ) t
  rw [hEc, hFc, cumulativeCoeff_union a b E F hE hF hEF t]

private theorem simpleRetardedSetOperator_finMeasAdditive
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    FinMeasAdditive (compactTimeMeasure a b)
      (simpleRetardedSetOperator chi a b) := by
  intro E F hE hF _hμE _hμF hEF
  apply ContinuousLinearMap.ext
  intro f
  rw [simpleRetardedSetOperator_apply_of_measurable chi a b (E ∪ F)
      (hE.union hF)]
  change cumulativeCoeffLp a b (E ∪ F) (hE.union hF) •
      localizedFreeCurveCLM chi a b f =
    simpleRetardedSetOperator chi a b E f +
      simpleRetardedSetOperator chi a b F f
  rw [
    simpleRetardedSetOperator_apply_of_measurable chi a b E hE,
    simpleRetardedSetOperator_apply_of_measurable chi a b F hF,
    cumulativeCoeffLp_union a b E F hE hF hEF]
  exact Lp.smul_add (p := ⊤) (q := 2) (r := 2) _ _ _

private theorem simpleRetardedSetOperator_dominated
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    DominatedFinMeasAdditive (compactTimeMeasure a b)
      (simpleRetardedSetOperator chi a b) (localizedFreeBound chi a b) := by
  refine ⟨simpleRetardedSetOperator_finMeasAdditive chi a b, ?_⟩
  intro E hE _hμE
  simpa [mul_comm] using
    norm_simpleRetardedSetOperator_le chi a b E hE

/-- Retarded local smoothing, extended continuously from interaction-picture
indicator forcings to arbitrary `L¹_t L²_x` forcing. -/
def retardedSmoothingCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp L2 1 (compactTimeMeasure a b) →L[ℝ]
      Lp (Hs (1 / 2 : ℝ)) 2 (compactTimeMeasure a b) :=
  L1.setToL1 (simpleRetardedSetOperator_dominated chi a b)

theorem norm_retardedSmoothingCLM_le (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ‖retardedSmoothingCLM chi a b‖ ≤ localizedFreeBound chi a b := by
  exact L1.norm_setToL1_le (simpleRetardedSetOperator_dominated chi a b)
    (localizedFreeBound_nonneg chi a b)

theorem retardedSmoothingCLM_indicatorConst (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (E : Set ℝ) (hE : MeasurableSet E) (f : L2) :
    retardedSmoothingCLM chi a b
        (indicatorConstLp 1 hE
          ((lt_of_le_of_lt (measure_mono (subset_univ E))
            (compactTimeMeasure_univ_lt_top a b)).ne) f) =
      cumulativeCoeffLp a b E hE • localizedFreeCurveCLM chi a b f := by
  rw [retardedSmoothingCLM, L1.setToL1_indicatorConstLp
    (simpleRetardedSetOperator_dominated chi a b)]
  exact simpleRetardedSetOperator_apply_of_measurable chi a b E hE f

private lemma cumulativeCoeff_measure_eq_interval (a b t : ℝ)
    (ht : t ∈ Icc a b) (E : Set ℝ) (hE : MeasurableSet E) :
    (volume.restrict (Ioc a t)).real (Icc a b ∩ E) =
      (((compactTimeMeasure a b).restrict E) (Iic t)).toReal := by
  unfold Measure.real
  congr 1
  rw [Measure.restrict_apply (measurableSet_Icc.inter hE),
    Measure.restrict_apply measurableSet_Iic,
    compactTimeMeasure,
    Measure.restrict_apply (measurableSet_Iic.inter hE)]
  apply measure_congr
  filter_upwards [(volume : Measure ℝ).ae_ne a] with x hxa
  apply propext
  constructor
  · rintro ⟨⟨hIcc, hxE⟩, hIoc⟩
    exact ⟨⟨hIoc.2, hxE⟩, hIcc⟩
  · rintro ⟨⟨hxt, hxE⟩, hIcc⟩
    exact ⟨⟨hIcc, hxE⟩,
      ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hxa), hxt⟩⟩

private lemma timeZeroExtension_indicatorConst_ae (a b : ℝ)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hfin : compactTimeMeasure a b E ≠ ⊤) (f : L2) :
    timeZeroExtension a b (indicatorConstLp 1 hE hfin f) =ᵐ[volume]
      (Icc a b ∩ E).indicator (fun _ : ℝ => f) := by
  have hrestrict :
      (indicatorConstLp 1 hE hfin f : ℝ → L2) =ᵐ[compactTimeMeasure a b]
        E.indicator (fun _ : ℝ => f) :=
    indicatorConstLp_coeFn
  have hind := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 hrestrict
  filter_upwards [hind] with s hs
  unfold timeZeroExtension
  rw [hs]
  by_cases hsI : s ∈ Icc a b <;> by_cases hsE : s ∈ E <;>
    simp [Set.indicator, hsI, hsE]

private lemma hardyPrimitiveFn_indicatorConst (a b t : ℝ)
    (ht : t ∈ Icc a b) (E : Set ℝ) (hE : MeasurableSet E)
    (hfin : compactTimeMeasure a b E ≠ ⊤) (f : L2) :
    hardyPrimitiveFn a b (indicatorConstLp 1 hE hfin f) t =
      cumulativeCoeff a b E t • f := by
  rw [hardyPrimitiveFn, intervalIntegral.integral_of_le ht.1]
  have hz := timeZeroExtension_indicatorConst_ae a b E hE hfin f
  calc
    (∫ s in Ioc a t,
        timeZeroExtension a b (indicatorConstLp 1 hE hfin f) s) =
        ∫ s in Ioc a t, (Icc a b ∩ E).indicator (fun _ : ℝ => f) s := by
      exact integral_congr_ae (ae_restrict_of_ae hz)
    _ = (volume.restrict (Ioc a t)).real (Icc a b ∩ E) • f := by
      exact integral_indicator_const f (measurableSet_Icc.inter hE)
    _ = cumulativeCoeff a b E t • f := by
      rw [cumulativeCoeff_measure_eq_interval a b t ht E hE]
      rfl

private lemma physicalRetardedCLM_indicatorConst
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E)
    (hfin : compactTimeMeasure a b E ≠ ⊤) (f : L2) :
    physicalRetardedCLM chi a b (indicatorConstLp 1 hE hfin f) =
      cumulativeCoeffLp a b E hE •
        localizedPhysicalFreeCurveLp chi a b f := by
  apply Lp.ext
  filter_upwards [evolveCutoffLp_coe chi a b
      (hardyPrimitiveLp a b (indicatorConstLp 1 hE hfin f)),
    hardyPrimitiveLp_coe a b (indicatorConstLp 1 hE hfin f),
    coe_cumulativeCoeffLp a b E hE,
    MemLp.coeFn_toLp (localizedPhysicalFree_memLp_two_Icc chi f a b),
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (cumulativeCoeffLp a b E hE)
      (localizedPhysicalFreeCurveLp chi a b f),
    ae_restrict_mem measurableSet_Icc]
      with t hout hprim hc hfree hsmul ht
  rw [show (physicalRetardedCLM chi a b
      (indicatorConstLp 1 hE hfin f) : ℝ → L2) t =
      evolveCutoffFn chi a b
        (hardyPrimitiveLp a b (indicatorConstLp 1 hE hfin f)) t by
      exact hout,
    show ((cumulativeCoeffLp a b E hE •
        localizedPhysicalFreeCurveLp chi a b f :
          Lp L2 2 (compactTimeMeasure a b)) : ℝ → L2) t =
      (cumulativeCoeffLp a b E hE : ℝ → ℂ) t •
        (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t by exact hsmul,
    hc]
  have hfree' :
      (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t =
        localizedPhysicalFree chi f t := hfree
  rw [hfree']
  unfold evolveCutoffFn localizedPhysicalFree
  rw [hprim, hardyPrimitiveFn_indicatorConst a b t ht E hE hfin f,
    freeProp_smul, map_smul]

/-- Realize the retarded `H^{1/2}` curve as a physical `L²` curve. -/
def realizedRetardedSmoothingCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp L2 1 (compactTimeMeasure a b) →L[ℝ]
      Lp L2 2 (compactTimeMeasure a b) :=
  ((hsHalfToL2CLM.restrictScalars ℝ).compLpL 2
      (compactTimeMeasure a b)).comp (retardedSmoothingCLM chi a b)

private lemma realizedRetardedSmoothingCLM_indicatorConst
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (E : Set ℝ)
    (hE : MeasurableSet E)
    (hfin : compactTimeMeasure a b E ≠ ⊤) (f : L2) :
    realizedRetardedSmoothingCLM chi a b
        (indicatorConstLp 1 hE hfin f) =
      cumulativeCoeffLp a b E hE •
        localizedPhysicalFreeCurveLp chi a b f := by
  rw [realizedRetardedSmoothingCLM, ContinuousLinearMap.comp_apply,
    retardedSmoothingCLM_indicatorConst chi a b E hE f]
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (hsHalfToL2CLM.restrictScalars ℝ)
      (cumulativeCoeffLp a b E hE • localizedFreeCurveCLM chi a b f),
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (cumulativeCoeffLp a b E hE) (localizedFreeCurveCLM chi a b f),
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (cumulativeCoeffLp a b E hE)
      (localizedPhysicalFreeCurveLp chi a b f),
    ContinuousLinearMap.coeFn_compLpL
      (hsHalfToL2CLM.restrictScalars ℝ)
      (localizedFreeCurveCLM chi a b f)]
      with t hleft hinput hout hreal
  rw [hleft, hinput, hout]
  change hsHalfToL2CLM
      ((cumulativeCoeffLp a b E hE : ℝ → ℂ) t •
        (localizedFreeCurveCLM chi a b f : ℝ → Hs (1 / 2 : ℝ)) t) =
    (cumulativeCoeffLp a b E hE : ℝ → ℂ) t •
      (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t
  rw [map_smul]
  have hcurve := congrArg
    (fun q : Lp L2 2 (compactTimeMeasure a b) => (q : ℝ → L2))
    (realizedLocalizedFreeCurveCLM_apply chi a b f)
  apply congrArg ((cumulativeCoeffLp a b E hE : ℝ → ℂ) t • ·)
  calc
    hsHalfToL2CLM
        ((localizedFreeCurveCLM chi a b f : ℝ → Hs (1 / 2 : ℝ)) t) =
        (realizedLocalizedFreeCurveCLM chi a b f : ℝ → L2) t := hreal.symm
    _ = (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t :=
      congrFun hcurve t

/-- The density extension of retarded local smoothing is represented by the
actual chronological Duhamel integral. -/
theorem realizedRetardedSmoothingCLM_eq_physical
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    realizedRetardedSmoothingCLM chi a b = physicalRetardedCLM chi a b := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.induction (p := (1 : ℝ≥0∞)) (by norm_num)
    (motive := fun q => realizedRetardedSmoothingCLM chi a b q =
      physicalRetardedCLM chi a b q)
  · intro f E hE hEfin
    change realizedRetardedSmoothingCLM chi a b
        (indicatorConstLp 1 hE hEfin.ne f) =
      physicalRetardedCLM chi a b (indicatorConstLp 1 hE hEfin.ne f)
    rw [realizedRetardedSmoothingCLM_indicatorConst chi a b E hE hEfin.ne f,
      physicalRetardedCLM_indicatorConst chi a b E hE hEfin.ne f]
  · intro f h hf hg _ hfg hgg
    simpa only [map_add] using congrArg₂ (· + ·) hfg hgg
  · exact isClosed_eq (realizedRetardedSmoothingCLM chi a b).continuous
      (physicalRetardedCLM chi a b).continuous

theorem realizedRetardedSmoothingCLM_apply
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (g : Lp L2 1 (compactTimeMeasure a b)) :
    realizedRetardedSmoothingCLM chi a b g = physicalRetardedCLM chi a b g := by
  rw [realizedRetardedSmoothingCLM_eq_physical]

end CubicNLSPhaseRetrieval
