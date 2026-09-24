import Lean_Code.CurrentAlmostEverywhere
import Lean_Code.HsOneMultiplier
import Lean_Code.EndpointControl
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# A common full-measure set for the localized critical current

The current is first recovered for each smooth compactly supported test.
Separability and continuity in an `H¹` coefficient turn the countably many
exceptional sets into one exceptional set.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology ComplexConjugate

noncomputable section
namespace CubicNLSPhaseRetrieval

def IsAdmissibleCurrentTest (χ φ : SchwartzMap ℝ ℂ) : Prop :=
  HasCompactSupport (φ : ℝ → ℂ) ∧
    ∀ x : ℝ, φ x ≠ 0 →
      χ x = 1 ∧ deriv (χ : ℝ → ℂ) x = 0

abbrev admissibleCurrentRange (χ : SchwartzMap ℝ ℂ) : Type :=
  {a : Hs (1 : ℝ) // ∃ φ : SchwartzMap ℝ ℂ,
    IsAdmissibleCurrentTest χ φ ∧ schwartzHsOne φ = a}

private noncomputable instance fact_two_le : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

private noncomputable instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) :=
  ⟨by norm_num⟩

private noncomputable instance : SecondCountableTopology (Hs (1 : ℝ)) :=
  inferInstance

private noncomputable instance (χ : SchwartzMap ℝ ℂ) :
    SecondCountableTopology (admissibleCurrentRange χ) := inferInstance

private noncomputable instance (χ : SchwartzMap ℝ ℂ) :
    Nonempty (admissibleCurrentRange χ) :=
  ⟨⟨schwartzHsOne 0, ⟨0,
    ⟨HasCompactSupport.zero, by simp [IsAdmissibleCurrentTest]⟩, rfl⟩⟩⟩

def admissibleCurrentDense (χ : SchwartzMap ℝ ℂ) :
    ℕ → admissibleCurrentRange χ :=
  TopologicalSpace.denseSeq (admissibleCurrentRange χ)

lemma denseRange_admissibleCurrentDense (χ : SchwartzMap ℝ ℂ) :
    DenseRange (admissibleCurrentDense χ) :=
  TopologicalSpace.denseRange_denseSeq (admissibleCurrentRange χ)

def admissibleCurrentTestSeq (χ : SchwartzMap ℝ ℂ) (n : ℕ) :
    SchwartzMap ℝ ℂ :=
  Classical.choose (admissibleCurrentDense χ n).property

lemma admissibleCurrentTestSeq_spec (χ : SchwartzMap ℝ ℂ) (n : ℕ) :
    IsAdmissibleCurrentTest χ (admissibleCurrentTestSeq χ n) ∧
      schwartzHsOne (admissibleCurrentTestSeq χ n) =
        (admissibleCurrentDense χ n).val :=
  Classical.choose_spec (admissibleCurrentDense χ n).property

/-- Equality on the countable dense family implies equality for every
admissible smooth test at a bounded critical slice. -/
theorem criticalCurrent_eq_all_admissible_of_seq
    (χ : SchwartzMap ℝ ℂ) (f g : BoundedCritical)
    (hseq : ∀ n : ℕ,
      criticalQuadraticCurrent f.val (admissibleCurrentTestSeq χ n) =
        criticalQuadraticCurrent g.val (admissibleCurrentTestSeq χ n)) :
    ∀ φ : SchwartzMap ℝ ℂ, IsAdmissibleCurrentTest χ φ →
      criticalQuadraticCurrent f.val φ = criticalQuadraticCurrent g.val φ := by
  intro φ hφ
  let z : admissibleCurrentRange χ :=
    ⟨schwartzHsOne φ, ⟨φ, hφ, rfl⟩⟩
  have heq :
      (fun a : admissibleCurrentRange χ =>
        boundedQuadraticCurrentHsOneCLM f a.val) =
      (fun a : admissibleCurrentRange χ =>
        boundedQuadraticCurrentHsOneCLM g a.val) := by
    apply (denseRange_admissibleCurrentDense χ).equalizer
    · exact (boundedQuadraticCurrentHsOneCLM f).continuous.comp
        continuous_subtype_val
    · exact (boundedQuadraticCurrentHsOneCLM g).continuous.comp
        continuous_subtype_val
    · funext n
      have hn := hseq n
      rw [criticalQuadraticCurrent_eq_hsOne,
        criticalQuadraticCurrent_eq_hsOne] at hn
      rw [(admissibleCurrentTestSeq_spec χ n).2] at hn
      exact hn
  have hz := congrFun heq z
  simpa only [z, criticalQuadraticCurrent_eq_hsOne] using hz

private lemma localizedRepresentative_toL2
    (χ : SchwartzMap ℝ ℂ) (σ : ℝ) (u : GlobalSolution σ)
    {A B t : ℝ} (hAB : A ≤ B)
    (ht : Hs.toTempered (1 / 2 : ℝ)
      ((localizedSolutionHsCurve χ σ u A B hAB :
        ℝ → Hs (1 / 2 : ℝ)) t) =
      MeasureTheory.Lp.toTemperedDistribution (cutoffL2CLM χ (u.u t))) :
    Hs.toL2 (by norm_num)
      ((localizedSolutionHsCurve χ σ u A B hAB :
        ℝ → Hs (1 / 2 : ℝ)) t) = cutoffL2CLM χ (u.u t) := by
  rw [Hs.toTempered_toL2 (s := (1 / 2 : ℝ)) (by norm_num)] at ht
  have hinj : Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2 :
        FourierL2 →L[ℂ] TemperedDistribution ℝ ℂ) :=
    LinearMap.ker_eq_bot.mp (by
      simpa using
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := ℂ) (E := ℝ) (μ := volume) (p := (2 : ℝ≥0∞))))
  exact hinj ht

private lemma cutoff_eLpNorm_top_lt_top
    (χ : SchwartzMap ℝ ℂ) (f : L2)
    (hf : eLpNorm (f : ℝ → ℂ) ⊤ volume < ⊤) :
    eLpNorm (cutoffL2CLM χ f : ℝ → ℂ) ⊤ volume < ⊤ := by
  rw [eLpNorm_congr_ae (coe_cutoffL2CLM χ f)]
  have hprod :
      (fun x : ℝ => χ x * (f : ℝ → ℂ) x) =ᵐ[volume]
        fun x : ℝ => (χ.toLp 2 volume : ℝ → ℂ) x * (f : ℝ → ℂ) x := by
    filter_upwards [χ.coeFn_toLp 2 volume] with x hx
    rw [hx]
  rw [eLpNorm_congr_ae hprod]
  apply lt_of_le_of_lt
    (eLpNorm_le_eLpNorm_mul_eLpNorm_top ⊤
      (Lp.aestronglyMeasurable (χ.toLp 2 volume)) (f : ℝ → ℂ)
      (fun x y : ℂ => x * y) 1
      (Filter.Eventually.of_forall fun x => by simp))
  have hχ : eLpNorm (χ.toLp 2 volume : ℝ → ℂ) ⊤ volume < ⊤ := by
    rw [eLpNorm_congr_ae (χ.coeFn_toLp 2 volume)]
    exact (χ.memLp ⊤ volume).2
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hχ) hf

/-- On a compact subinterval there is one full-measure set on which the
localized slices are bounded, have the same modulus, and have equal current
against every admissible smooth coefficient. -/
theorem localizedCriticalCurrent_common_ae
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (χ : SchwartzMap ℝ ℂ) {A B : ℝ} (hAB : A < B)
    (hABI : Icc A B ⊆ I) :
    ∀ᵐ t : ℝ ∂timeMeasure A B,
      ∃ f g : BoundedCritical,
        f.val = (localizedSolutionHsCurve χ σ u A B hAB.le :
          ℝ → Hs (1 / 2 : ℝ)) t ∧
        g.val = (localizedSolutionHsCurve χ σ v A B hAB.le :
          ℝ → Hs (1 / 2 : ℝ)) t ∧
        f.toL2 = cutoffL2CLM χ (u.u t) ∧
        g.toL2 = cutoffL2CLM χ (v.u t) ∧
        (∀ᵐ x : ℝ ∂volume,
          ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖) ∧
        ∀ φ : SchwartzMap ℝ ℂ, IsAdmissibleCurrentTest χ φ →
          criticalQuadraticCurrent f.val φ =
            criticalQuadraticCurrent g.val φ := by
  let Hu := localizedSolutionHsCurve χ σ u A B hAB.le
  let Hv := localizedSolutionHsCurve χ σ v A B hAB.le
  have hseq : ∀ n : ℕ, ∀ᵐ t : ℝ ∂timeMeasure A B,
      criticalQuadraticCurrent (Hu t) (admissibleCurrentTestSeq χ n) =
        criticalQuadraticCurrent (Hv t) (admissibleCurrentTestSeq χ n) := by
    intro n
    exact localizedCriticalCurrent_ae_eq σ u v I hI hmod χ
      (admissibleCurrentTestSeq χ n)
      (admissibleCurrentTestSeq_spec χ n).1.2 hAB hABI
  have hseqAll : ∀ᵐ t : ℝ ∂timeMeasure A B, ∀ n : ℕ,
      criticalQuadraticCurrent (Hu t) (admissibleCurrentTestSeq χ n) =
        criticalQuadraticCurrent (Hv t) (admissibleCurrentTestSeq χ n) :=
    ae_all_iff.2 hseq
  have hrepU := localizedSolutionHsCurve_represents χ σ u A B hAB.le
  have hrepV := localizedSolutionHsCurve_represents χ σ v A B hAB.le
  have htopU := (endpoint_control σ u (Icc A B) measurableSet_Icc
    isCompact_Icc.isBounded).2.2
  have htopV := (endpoint_control σ v (Icc A B) measurableSet_Icc
    isCompact_Icc.isBounded).2.2
  filter_upwards [hseqAll, hrepU, hrepV, htopU, htopV,
      ae_restrict_mem measurableSet_Icc] with t hcur hru hrv htu htv htIcc
  have htIn : t ∈ I := hABI htIcc
  have huTop : eLpNorm (u.u t : ℝ → ℂ) ⊤ volume < ⊤ := by
    simpa [sectionENorm, curveRepresentative] using htu
  have hvTop : eLpNorm (v.u t : ℝ → ℂ) ⊤ volume < ⊤ := by
    simpa [sectionENorm, curveRepresentative] using htv
  have hLu : Hs.toL2 (by norm_num) (Hu t) = cutoffL2CLM χ (u.u t) :=
    localizedRepresentative_toL2 χ σ u hAB.le (by
      rw [toTemperedDistribution_cutoffL2CLM]
      exact hru)
  have hLv : Hs.toL2 (by norm_num) (Hv t) = cutoffL2CLM χ (v.u t) :=
    localizedRepresentative_toL2 χ σ v hAB.le (by
      rw [toTemperedDistribution_cutoffL2CLM]
      exact hrv)
  let f : BoundedCritical :=
    ⟨Hu t, by rw [hLu]; exact cutoff_eLpNorm_top_lt_top χ (u.u t) huTop⟩
  let g : BoundedCritical :=
    ⟨Hv t, by rw [hLv]; exact cutoff_eLpNorm_top_lt_top χ (v.u t) hvTop⟩
  have hmoduv : ∀ᵐ x : ℝ ∂volume,
      ‖(u.u t : ℝ → ℂ) x‖ = ‖(v.u t : ℝ → ℂ) x‖ := by
    have hsquare := density_on_open σ u v I hI hmod t htIn
    filter_upwards [hsquare] with x hx
    nlinarith [norm_nonneg ((u.u t : ℝ → ℂ) x),
      norm_nonneg ((v.u t : ℝ → ℂ) x)]
  have hmodfg : ∀ᵐ x : ℝ ∂volume,
      ‖(f.toL2 : ℝ → ℂ) x‖ = ‖(g.toL2 : ℝ → ℂ) x‖ := by
    filter_upwards [coe_cutoffL2CLM χ (u.u t),
      coe_cutoffL2CLM χ (v.u t), hmoduv] with x hcu hcv hm
    change ‖(Hs.toL2 (by norm_num) (Hu t) : ℝ → ℂ) x‖ =
      ‖(Hs.toL2 (by norm_num) (Hv t) : ℝ → ℂ) x‖
    have hLux := congrFun (congrArg (fun q : L2 => (q : ℝ → ℂ)) hLu) x
    have hLvx := congrFun (congrArg (fun q : L2 => (q : ℝ → ℂ)) hLv) x
    rw [hLux, hLvx, hcu, hcv, norm_mul, norm_mul, hm]
  refine ⟨f, g, rfl, rfl, hLu, hLv, hmodfg, ?_⟩
  exact criticalCurrent_eq_all_admissible_of_seq χ f g hcur

end CubicNLSPhaseRetrieval
