import Lean_Code.RegularizedMass

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- Spatial resolvent smoothing lifted pointwise to a Bochner `L¹` curve. -/
def frequencySmoothLpOne (n : ℕ) (mu : Measure ℝ) :
    Lp L2 1 mu →L[ℂ] Lp L2 1 mu :=
  (frequencySmoothCLM n).compLpL 1 mu

lemma frequencySmoothLpOne_coe (n : ℕ) (mu : Measure ℝ)
    (F : Lp L2 1 mu) :
    (frequencySmoothLpOne n mu F : ℝ → L2) =ᵐ[mu]
      fun t => frequencySmoothCLM n (F t) := by
  exact ContinuousLinearMap.coeFn_compLpL (frequencySmoothCLM n) F

/-- Uniform contractions converging strongly on the fiber converge strongly
on every Bochner `L¹` curve. -/
theorem frequencySmoothLpOne_tendsto (mu : Measure ℝ) (F : Lp L2 1 mu) :
    Tendsto (fun n : ℕ => frequencySmoothLpOne n mu F) atTop (nhds F) := by
  let D : ℕ → ℝ → L2 := fun n t => frequencySmoothCLM n (F t) - F t
  have hDmeas (n : ℕ) : AEStronglyMeasurable (D n) mu :=
    ((frequencySmoothCLM n).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable F)).sub (Lp.aestronglyMeasurable F)
  have hbound (n : ℕ) : ∀ᵐ t ∂mu, ‖D n t‖ ≤ 2 * ‖F t‖ := by
    filter_upwards with t
    calc
      ‖D n t‖ ≤ ‖frequencySmoothCLM n (F t)‖ + ‖F t‖ := norm_sub_le _ _
      _ ≤ ‖F t‖ + ‖F t‖ := by gcongr; exact norm_frequencySmoothCLM_le n (F t)
      _ = 2 * ‖F t‖ := by ring
  have hboundInt : Integrable (fun t => 2 * ‖F t‖) mu :=
    (memLp_one_iff_integrable.mp (Lp.memLp F)).norm.const_mul 2
  have hpoint : ∀ᵐ t ∂mu,
      Tendsto (fun n => ‖D n t‖) atTop (nhds 0) := by
    filter_upwards with t
    have hz : Tendsto (fun n => D n t) atTop (nhds 0) := by
      simpa [D] using (frequencySmoothCLM_tendsto (F t)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => F t) atTop (nhds (F t)))
    exact tendsto_zero_iff_norm_tendsto_zero.mp hz
  have hint : Tendsto (fun n => ∫ t, ‖D n t‖ ∂mu) atTop (nhds 0) := by
    have hbound' (n : ℕ) : ∀ᵐ t ∂mu,
        ‖‖D n t‖‖ ≤ 2 * ‖F t‖ := by
      filter_upwards [hbound n] with t ht
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (D n t))] using ht
    simpa using tendsto_integral_of_dominated_convergence
      (fun t => 2 * ‖F t‖)
      (fun n => (hDmeas n).norm) hboundInt hbound' hpoint
  have hnorm (n : ℕ) :
      ‖frequencySmoothLpOne n mu F - F‖ = ∫ t, ‖D n t‖ ∂mu := by
    rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    have he : (∫⁻ t, ‖((frequencySmoothLpOne n mu F - F :
        Lp L2 1 mu) : ℝ → L2) t‖ₑ ∂mu) =
        ∫⁻ t, ‖D n t‖ₑ ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (frequencySmoothLpOne n mu F) F,
        frequencySmoothLpOne_coe n mu F] with t hsub hs
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [hs]
    rw [he, ← integral_norm_eq_lintegral_enorm (hDmeas n)]
  rw [← tendsto_sub_nhds_zero_iff]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hnorm] using hint

/-- Complex-linear realization of a critical Sobolev time curve. -/
def realizeHsCurveCLM (mu : Measure ℝ) :
    Lp (Hs (1 / 2 : ℝ)) 2 mu →L[ℂ] Lp L2 2 mu :=
  hsHalfToL2CLM.compLpL 2 mu

lemma realize_localizedFreeCurve (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (f : L2) :
    realizeHsCurveCLM (timeMeasure a b) (localizedFreeCurveCLM chi a b f) =
      localizedPhysicalFreeCurveLp chi a b f := by
  have h := realizedLocalizedFreeCurveCLM_apply chi a b f
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL hsHalfToL2CLM
      (localizedFreeCurveCLM chi a b f),
    ContinuousLinearMap.coeFn_compLpL (hsHalfToL2CLM.restrictScalars ℝ)
      (localizedFreeCurveCLM chi a b f)] with t hc hr
  have hp := congrArg
    (fun q : Lp L2 2 (timeMeasure a b) => (q : ℝ → L2) t) h
  exact hc.trans (hr.symm.trans hp)

lemma realize_retardedSmoothing (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (F : Lp L2 1 (timeMeasure a b)) :
    realizeHsCurveCLM (timeMeasure a b) (retardedSmoothingCLM chi a b F) =
      physicalRetardedCLM chi a b F := by
  have h := realizedRetardedSmoothingCLM_apply chi a b F
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL hsHalfToL2CLM
      (retardedSmoothingCLM chi a b F),
    ContinuousLinearMap.coeFn_compLpL (hsHalfToL2CLM.restrictScalars ℝ)
      (retardedSmoothingCLM chi a b F)] with t hc hr
  have hp := congrArg
    (fun q : Lp L2 2 (timeMeasure a b) => (q : ℝ → L2) t) h
  exact hc.trans (hr.symm.trans hp)

/-- Local smoothing curve for arbitrary interaction-picture data and forcing. -/
def localizedMildHsCurve (chi : SchwartzMap ℝ ℂ) (a b : ℝ)
    (c : ℂ) (f : L2) (F : Lp L2 1 (timeMeasure a b)) :
    Lp (Hs (1 / 2 : ℝ)) 2 (timeMeasure a b) :=
  localizedFreeCurveCLM chi a b f -
    c • retardedSmoothingCLM chi a b F

lemma realize_localizedMildHsCurve (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (c : ℂ) (f : L2) (F : Lp L2 1 (timeMeasure a b)) :
    realizeHsCurveCLM (timeMeasure a b)
        (localizedMildHsCurve chi a b c f F) =
      localizedPhysicalFreeCurveLp chi a b f -
        c • physicalRetardedCLM chi a b F := by
  rw [localizedMildHsCurve, map_sub, map_smul,
    realize_localizedFreeCurve, realize_retardedSmoothing]

/-- The local-smoothing curve of the spatially regularized mild solution. -/
def localizedRegularizedSolutionHsCurve (n : ℕ)
    (chi : SchwartzMap ℝ ℂ) (σ : ℝ) (u : GlobalSolution σ)
    (a b : ℝ) (hab : a ≤ b) :
    Lp (Hs (1 / 2 : ℝ)) 2 (timeMeasure a b) :=
  localizedMildHsCurve chi a b (Complex.I * (σ : ℂ))
    (frequencySmoothCLM n (freeProp (-a) (u.u a)))
    (frequencySmoothLpOne n (timeMeasure a b)
      (interactionForcingLp σ u a b hab))

theorem localizedRegularizedSolutionHsCurve_tendsto
    (chi : SchwartzMap ℝ ℂ) (σ : ℝ) (u : GlobalSolution σ)
    (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun n : ℕ =>
      localizedRegularizedSolutionHsCurve n chi σ u a b hab) atTop
      (nhds (localizedSolutionHsCurve chi σ u a b hab)) := by
  have hf := (localizedFreeCurveCLM chi a b).continuous.continuousAt.tendsto.comp
    (frequencySmoothCLM_tendsto (freeProp (-a) (u.u a)))
  have hF := (retardedSmoothingCLM chi a b).continuous.continuousAt.tendsto.comp
    (frequencySmoothLpOne_tendsto (timeMeasure a b)
      (interactionForcingLp σ u a b hab))
  simpa [localizedRegularizedSolutionHsCurve, localizedMildHsCurve,
    localizedSolutionHsCurve] using
    hf.sub (hF.const_smul (Complex.I * (σ : ℂ)))

lemma hardyPrimitiveFn_frequencySmoothLpOne (n : ℕ) (a b : ℝ)
    (F : Lp L2 1 (timeMeasure a b)) (t : ℝ) :
    hardyPrimitiveFn a b
        (frequencySmoothLpOne n (timeMeasure a b) F) t =
      frequencySmoothCLM n (hardyPrimitiveFn a b F t) := by
  have hcoe := frequencySmoothLpOne_coe n (timeMeasure a b) F
  have hind : timeZeroExtension a b
      (frequencySmoothLpOne n (timeMeasure a b) F) =ᵐ[volume]
      fun s => frequencySmoothCLM n (timeZeroExtension a b F s) := by
    have hi := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 hcoe
    filter_upwards [hi] with s hs
    change (Set.Icc a b).indicator
        ((frequencySmoothLpOne n (timeMeasure a b) F :
          Lp L2 1 (timeMeasure a b)) : ℝ → L2) s = _
    rw [hs]
    by_cases hmem : s ∈ Set.Icc a b
    · simp [timeZeroExtension, hmem]
    · simp [timeZeroExtension, hmem]
  unfold hardyPrimitiveFn
  rw [intervalIntegral.integral_congr_ae (by
    filter_upwards [hind] with s hs hmem
    exact hs)]
  exact (frequencySmoothCLM n).intervalIntegral_comp_comm
    (timeZeroExtension_integrable a b F).intervalIntegrable

def regularizedPhysicalLocalizedSolution (n : ℕ)
    (chi : SchwartzMap ℝ ℂ) {σ : ℝ} (u : GlobalSolution σ)
    (t : ℝ) : L2 :=
  cutoffL2CLM chi (frequencySmoothCLM n (u.u t))

lemma continuous_regularizedPhysicalLocalizedSolution (n : ℕ)
    (chi : SchwartzMap ℝ ℂ) {σ : ℝ} (u : GlobalSolution σ) :
    Continuous (regularizedPhysicalLocalizedSolution n chi u) :=
  (cutoffL2CLM chi).continuous.comp
    ((frequencySmoothCLM n).continuous.comp u.continuous)

lemma regularizedPhysicalLocalizedSolution_memLp (n : ℕ)
    (chi : SchwartzMap ℝ ℂ) {σ : ℝ} (u : GlobalSolution σ)
    (a b : ℝ) : MemLp (regularizedPhysicalLocalizedSolution n chi u) 2
      (timeMeasure a b) := by
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    (continuous_regularizedPhysicalLocalizedSolution n chi u).norm.continuousOn
  exact MemLp.of_bound
    (continuous_regularizedPhysicalLocalizedSolution n chi u).aestronglyMeasurable C
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hC ⟨t, ht, rfl⟩)

def regularizedPhysicalLocalizedSolutionLp (n : ℕ)
    (chi : SchwartzMap ℝ ℂ) {σ : ℝ} (u : GlobalSolution σ)
    (a b : ℝ) : Lp L2 2 (timeMeasure a b) :=
  (regularizedPhysicalLocalizedSolution_memLp n chi u a b).toLp
    (regularizedPhysicalLocalizedSolution n chi u)

lemma regularizedPhysicalLocalizedSolutionLp_coe (n : ℕ)
    (chi : SchwartzMap ℝ ℂ) {σ : ℝ} (u : GlobalSolution σ)
    (a b : ℝ) :
    (regularizedPhysicalLocalizedSolutionLp n chi u a b : ℝ → L2) =ᵐ[timeMeasure a b]
      regularizedPhysicalLocalizedSolution n chi u := MemLp.coeFn_toLp _

lemma frequencySmooth_interaction_reconstruct (n : ℕ) (σ : ℝ)
    (u : GlobalSolution σ) (a t : ℝ) :
    frequencySmoothCLM n (u.u t) =
      freeProp t (frequencySmoothCLM n (freeProp (-a) (u.u a))) -
        (Complex.I * (σ : ℂ)) • freeProp t
          (frequencySmoothCLM n
            (∫ s in a..t, freeProp (-s) (u.nonlin s))) := by
  have h := congrArg (frequencySmoothCLM n)
    (interaction_reconstruct σ u a t)
  simpa only [map_sub, map_smul, frequencySmoothCLM_comm_freeProp] using h

theorem localizedRegularizedSolutionHsCurve_realizes
    (n : ℕ) (chi : SchwartzMap ℝ ℂ) (σ : ℝ)
    (u : GlobalSolution σ) (a b : ℝ) (hab : a ≤ b) :
    realizeHsCurveCLM (timeMeasure a b)
        (localizedRegularizedSolutionHsCurve n chi σ u a b hab) =
      regularizedPhysicalLocalizedSolutionLp n chi u a b := by
  rw [localizedRegularizedSolutionHsCurve,
    realize_localizedMildHsCurve]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (localizedPhysicalFree_memLp_two_Icc chi
        (frequencySmoothCLM n (freeProp (-a) (u.u a))) a b),
    physicalRetardedCLM_coe chi a b
      (frequencySmoothLpOne n (timeMeasure a b)
        (interactionForcingLp σ u a b hab)),
    Lp.coeFn_sub
      (localizedPhysicalFreeCurveLp chi a b
        (frequencySmoothCLM n (freeProp (-a) (u.u a))))
      ((Complex.I * (σ : ℂ)) • physicalRetardedCLM chi a b
        (frequencySmoothLpOne n (timeMeasure a b)
          (interactionForcingLp σ u a b hab))),
    Lp.coeFn_smul (Complex.I * (σ : ℂ))
      (physicalRetardedCLM chi a b
        (frequencySmoothLpOne n (timeMeasure a b)
          (interactionForcingLp σ u a b hab))),
    regularizedPhysicalLocalizedSolutionLp_coe n chi u a b,
    ae_restrict_mem measurableSet_Icc] with t hfree hret hsub hsmul hout ht
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply]
  have hfree' :
      (localizedPhysicalFreeCurveLp chi a b
        (frequencySmoothCLM n (freeProp (-a) (u.u a))) : ℝ → L2) t =
      localizedPhysicalFree chi
        (frequencySmoothCLM n (freeProp (-a) (u.u a))) t := by
    simpa [localizedPhysicalFreeCurveLp] using hfree
  rw [hfree', hret, hout]
  change cutoffL2CLM chi
      (freeProp t (frequencySmoothCLM n (freeProp (-a) (u.u a)))) -
      (Complex.I * (σ : ℂ)) • cutoffL2CLM chi
        (freeProp t (hardyPrimitiveFn a b
          (frequencySmoothLpOne n (timeMeasure a b)
            (interactionForcingLp σ u a b hab)) t)) =
    cutoffL2CLM chi (frequencySmoothCLM n (u.u t))
  rw [hardyPrimitiveFn_frequencySmoothLpOne,
    hardyPrimitiveFn_interactionForcing σ u a b hab t ht]
  rw [← map_smul, ← map_sub]
  congr 1
  exact (frequencySmooth_interaction_reconstruct n σ u a t).symm

end CubicNLSPhaseRetrieval
