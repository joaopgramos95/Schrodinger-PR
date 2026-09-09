import Lean_Code.LocalSmoothingExtension

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

set_option maxHeartbeats 1000000

abbrev timeMeasure (a b : ℝ) : Measure ℝ := volume.restrict (Icc a b)

def timeZeroExtension (a b : ℝ) (g : Lp L2 1 (timeMeasure a b))
    (s : ℝ) : L2 :=
  (Icc a b).indicator (g : ℝ → L2) s

lemma timeZeroExtension_integrable (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    Integrable (timeZeroExtension a b g) volume := by
  rw [← memLp_one_iff_integrable]
  exact (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp g)

def hardyPrimitiveFn (a b : ℝ) (g : Lp L2 1 (timeMeasure a b))
    (t : ℝ) : L2 :=
  ∫ s in a..t, timeZeroExtension a b g s

lemma continuous_hardyPrimitiveFn (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    Continuous (hardyPrimitiveFn a b g) := by
  exact intervalIntegral.continuous_primitive
    (fun _ _ => (timeZeroExtension_integrable a b g).intervalIntegrable) a

lemma norm_hardyPrimitiveFn_le (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖hardyPrimitiveFn a b g t‖ ≤ ‖g‖ := by
  let G := timeZeroExtension a b g
  have hG : Integrable G volume := timeZeroExtension_integrable a b g
  have hat : a ≤ t := ht.1
  rw [hardyPrimitiveFn, intervalIntegral.integral_of_le hat]
  calc
    ‖∫ s in Ioc a t, G s‖ ≤ ∫ s in Ioc a t, ‖G s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s, ‖G s‖ := by
      simpa only [Measure.restrict_univ] using
        setIntegral_mono_set (s := Ioc a t) (t := Set.univ)
          hG.norm.integrableOn
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (Filter.Eventually.of_forall fun x hx => Set.mem_univ x)
    _ = ‖g‖ := by
      rw [L1.norm_eq_integral_norm]
      change (∫ s, ‖(Icc a b).indicator (g : ℝ → L2) s‖ ∂volume) =
        ∫ s, ‖(g : ℝ → L2) s‖ ∂(volume.restrict (Icc a b))
      rw [show (fun s => ‖(Icc a b).indicator (g : ℝ → L2) s‖) =
          (Icc a b).indicator (fun s => ‖(g : ℝ → L2) s‖) by
        funext s
        by_cases hs : s ∈ Icc a b <;> simp [Set.indicator, hs]]
      rw [integral_indicator measurableSet_Icc]

lemma hardyPrimitiveFn_memLp_two (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    MemLp (hardyPrimitiveFn a b g) 2 (timeMeasure a b) := by
  apply MemLp.of_bound
    (continuous_hardyPrimitiveFn a b g).aestronglyMeasurable
    ‖g‖
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact norm_hardyPrimitiveFn_le a b g t ht

def hardyPrimitiveLp (a b : ℝ) (g : Lp L2 1 (timeMeasure a b)) :
    Lp L2 2 (timeMeasure a b) :=
  (hardyPrimitiveFn_memLp_two a b g).toLp (hardyPrimitiveFn a b g)

lemma hardyPrimitiveLp_coe (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    (hardyPrimitiveLp a b g : ℝ → L2) =ᵐ[timeMeasure a b]
      hardyPrimitiveFn a b g := MemLp.coeFn_toLp _

lemma hardyPrimitiveFn_add (a b : ℝ)
    (g h : Lp L2 1 (timeMeasure a b)) (t : ℝ) :
    hardyPrimitiveFn a b (g + h) t =
      hardyPrimitiveFn a b g t + hardyPrimitiveFn a b h t := by
  unfold hardyPrimitiveFn
  rw [← intervalIntegral.integral_add
    (timeZeroExtension_integrable a b g).intervalIntegrable
    (timeZeroExtension_integrable a b h).intervalIntegrable]
  apply intervalIntegral.integral_congr_ae
  have hind := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1
    (Lp.coeFn_add g h)
  filter_upwards [hind] with s hs hsI
  by_cases hmem : s ∈ Icc a b <;>
    simp [timeZeroExtension, Set.indicator, hmem] at hs ⊢
  exact hs

lemma hardyPrimitiveFn_smul (a b : ℝ) (c : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) (t : ℝ) :
    hardyPrimitiveFn a b (c • g) t = c • hardyPrimitiveFn a b g t := by
  unfold hardyPrimitiveFn
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_ae
  have hind := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1
    (Lp.coeFn_smul c g)
  filter_upwards [hind] with s hs hsI
  by_cases hmem : s ∈ Icc a b <;>
    simp [timeZeroExtension, Set.indicator, hmem, Pi.smul_apply] at hs ⊢
  exact hs

lemma hardyPrimitiveLp_add (a b : ℝ)
    (g h : Lp L2 1 (timeMeasure a b)) :
    hardyPrimitiveLp a b (g + h) =
      hardyPrimitiveLp a b g + hardyPrimitiveLp a b h := by
  apply Lp.ext
  filter_upwards [hardyPrimitiveLp_coe a b (g + h),
    hardyPrimitiveLp_coe a b g, hardyPrimitiveLp_coe a b h,
    Lp.coeFn_add (hardyPrimitiveLp a b g) (hardyPrimitiveLp a b h)]
      with t hsum hg hh hout
  rw [hsum, hout]
  simp only [Pi.add_apply]
  rw [hg, hh, hardyPrimitiveFn_add]

lemma hardyPrimitiveLp_smul (a b : ℝ) (c : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    hardyPrimitiveLp a b (c • g) = c • hardyPrimitiveLp a b g := by
  apply Lp.ext
  filter_upwards [hardyPrimitiveLp_coe a b (c • g),
    hardyPrimitiveLp_coe a b g,
    Lp.coeFn_smul c (hardyPrimitiveLp a b g)] with t hleft hg hout
  rw [hleft, hout]
  simp only [Pi.smul_apply]
  rw [hg, hardyPrimitiveFn_smul]

def hardyPrimitiveLinear (a b : ℝ) :
    Lp L2 1 (timeMeasure a b) →ₗ[ℝ] Lp L2 2 (timeMeasure a b) where
  toFun := hardyPrimitiveLp a b
  map_add' := hardyPrimitiveLp_add a b
  map_smul' := hardyPrimitiveLp_smul a b

def hardyBound (a b : ℝ) : ℝ :=
  ((measureUnivNNReal (timeMeasure a b) ^
    (2 : ℝ≥0∞).toReal⁻¹ : NNReal) : ℝ)

lemma norm_hardyPrimitiveLp_le (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    ‖hardyPrimitiveLp a b g‖ ≤ hardyBound a b * ‖g‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg g)
  filter_upwards [hardyPrimitiveLp_coe a b g,
    ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  exact norm_hardyPrimitiveFn_le a b g t hmem

def hardyPrimitiveCLM (a b : ℝ) :
    Lp L2 1 (timeMeasure a b) →L[ℝ] Lp L2 2 (timeMeasure a b) :=
  (hardyPrimitiveLinear a b).mkContinuous (hardyBound a b)
    (norm_hardyPrimitiveLp_le a b)

/-- Apply the time-dependent free group and a fixed spatial cutoff to an
`L²_tL²_x` curve. -/
def evolveCutoffFn (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) (t : ℝ) : L2 :=
  cutoffL2CLM chi (freeProp t ((P : ℝ → L2) t))

private lemma evolveCutoffFn_aestronglyMeasurable
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) :
    AEStronglyMeasurable (evolveCutoffFn chi a b P) (timeMeasure a b) := by
  have hpair : AEStronglyMeasurable
      (fun t : ℝ => (t, (P : ℝ → L2) t)) (timeMeasure a b) :=
    measurable_id.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable P)
  have hfree : AEStronglyMeasurable
      (fun t : ℝ => freeProp t ((P : ℝ → L2) t)) (timeMeasure a b) :=
    Continuous.comp_aestronglyMeasurable
      (f := fun t : ℝ => (t, (P : ℝ → L2) t))
      (g := fun q : ℝ × L2 => freeProp q.1 q.2)
      continuous_freeProp_joint hpair
  exact Continuous.comp_aestronglyMeasurable
    (f := fun t : ℝ => freeProp t ((P : ℝ → L2) t))
    (g := cutoffL2CLM chi) (cutoffL2CLM chi).continuous hfree

private lemma norm_evolveCutoffFn_le
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) (t : ℝ) :
    ‖evolveCutoffFn chi a b P t‖ ≤
      schwartzCutoffBound chi * ‖(P : ℝ → L2) t‖ := by
  exact (norm_cutoffL2CLM_le chi
    (freeProp t ((P : ℝ → L2) t))).trans_eq (by rw [norm_freeProp])

lemma evolveCutoffFn_memLp (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) :
    MemLp (evolveCutoffFn chi a b P) 2 (timeMeasure a b) := by
  exact (Lp.memLp P).of_le_mul
    (evolveCutoffFn_aestronglyMeasurable chi a b P)
    (Filter.Eventually.of_forall (norm_evolveCutoffFn_le chi a b P))

def evolveCutoffLp (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) : Lp L2 2 (timeMeasure a b) :=
  (evolveCutoffFn_memLp chi a b P).toLp (evolveCutoffFn chi a b P)

lemma evolveCutoffLp_coe (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) :
    (evolveCutoffLp chi a b P : ℝ → L2) =ᵐ[timeMeasure a b]
      evolveCutoffFn chi a b P := MemLp.coeFn_toLp _

lemma evolveCutoffLp_add (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P Q : Lp L2 2 (timeMeasure a b)) :
    evolveCutoffLp chi a b (P + Q) =
      evolveCutoffLp chi a b P + evolveCutoffLp chi a b Q := by
  apply Lp.ext
  filter_upwards [evolveCutoffLp_coe chi a b (P + Q),
    evolveCutoffLp_coe chi a b P, evolveCutoffLp_coe chi a b Q,
    Lp.coeFn_add P Q,
    Lp.coeFn_add (evolveCutoffLp chi a b P) (evolveCutoffLp chi a b Q)]
      with t hleft hp hq hpq hout
  rw [hleft, hout]
  simp only [Pi.add_apply]
  rw [hp, hq]
  unfold evolveCutoffFn
  rw [hpq]
  simp only [Pi.add_apply]
  rw [freeProp_add_apply, map_add]

lemma evolveCutoffLp_smul (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (c : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) :
    evolveCutoffLp chi a b (c • P) = c • evolveCutoffLp chi a b P := by
  apply Lp.ext
  filter_upwards [evolveCutoffLp_coe chi a b (c • P),
    evolveCutoffLp_coe chi a b P, Lp.coeFn_smul c P,
    Lp.coeFn_smul c (evolveCutoffLp chi a b P)]
      with t hleft hp hcp hout
  rw [hleft, hout]
  simp only [Pi.smul_apply]
  rw [hp]
  unfold evolveCutoffFn
  have hcp' : ((c • P : Lp L2 2 (timeMeasure a b)) : ℝ → L2) t =
      (c : ℂ) • (P : ℝ → L2) t := by
    rw [hcp]
    exact RCLike.real_smul_eq_coe_smul c ((P : ℝ → L2) t)
  rw [hcp', freeProp_smul, map_smul]
  rfl

def evolveCutoffLinear (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp L2 2 (timeMeasure a b) →ₗ[ℝ] Lp L2 2 (timeMeasure a b) where
  toFun := evolveCutoffLp chi a b
  map_add' := evolveCutoffLp_add chi a b
  map_smul' := evolveCutoffLp_smul chi a b

lemma norm_evolveCutoffLp_le (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (P : Lp L2 2 (timeMeasure a b)) :
    ‖evolveCutoffLp chi a b P‖ ≤ schwartzCutoffBound chi * ‖P‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [evolveCutoffLp_coe chi a b P] with t ht
  rw [ht]
  exact norm_cutoffL2CLM_le chi (freeProp t ((P : ℝ → L2) t)) |>.trans_eq
    (by rw [norm_freeProp])

def evolveCutoffCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp L2 2 (timeMeasure a b) →L[ℝ] Lp L2 2 (timeMeasure a b) :=
  (evolveCutoffLinear chi a b).mkContinuous (schwartzCutoffBound chi)
    (norm_evolveCutoffLp_le chi a b)

/-- The actual retarded physical curve associated to an interaction-picture
forcing. -/
def physicalRetardedCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp L2 1 (timeMeasure a b) →L[ℝ] Lp L2 2 (timeMeasure a b) :=
  (evolveCutoffCLM chi a b).comp (hardyPrimitiveCLM a b)

theorem physicalRetardedCLM_coe (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (g : Lp L2 1 (timeMeasure a b)) :
    (physicalRetardedCLM chi a b g : ℝ → L2) =ᵐ[timeMeasure a b]
      fun t => cutoffL2CLM chi (freeProp t (hardyPrimitiveFn a b g t)) := by
  filter_upwards [evolveCutoffLp_coe chi a b (hardyPrimitiveLp a b g),
    hardyPrimitiveLp_coe a b g] with t hout hprim
  rw [show (physicalRetardedCLM chi a b g : ℝ → L2) t =
      evolveCutoffFn chi a b (hardyPrimitiveLp a b g) t by exact hout]
  unfold evolveCutoffFn
  rw [hprim]

end CubicNLSPhaseRetrieval
