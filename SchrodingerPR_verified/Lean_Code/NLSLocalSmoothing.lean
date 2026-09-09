import Lean_Code.RetardedLocalSmoothing
import Lean_Code.WeakMild

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

def interactionForcingLp (sigma : ℝ) (u : GlobalSolution sigma)
    (a b : ℝ) (hab : a ≤ b) : Lp L2 1 (timeMeasure a b) := by
  have hint : Integrable (fun s => freeProp (-s) (u.nonlin s))
      (timeMeasure a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (interaction_forcing_intervalIntegrable sigma u a b)
  exact (memLp_one_iff_integrable.mpr hint).toLp
    (fun s => freeProp (-s) (u.nonlin s))

lemma interactionForcingLp_coe (sigma : ℝ) (u : GlobalSolution sigma)
    (a b : ℝ) (hab : a ≤ b) :
    (interactionForcingLp sigma u a b hab : ℝ → L2) =ᵐ[timeMeasure a b]
      fun s => freeProp (-s) (u.nonlin s) := by
  unfold interactionForcingLp
  exact MemLp.coeFn_toLp _

lemma timeZeroExtension_interactionForcing_ae
    (sigma : ℝ) (u : GlobalSolution sigma)
    (a b : ℝ) (hab : a ≤ b) :
    timeZeroExtension a b (interactionForcingLp sigma u a b hab) =ᵐ[volume]
      (Icc a b).indicator (fun s => freeProp (-s) (u.nonlin s)) := by
  exact (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1
    (interactionForcingLp_coe sigma u a b hab)

lemma hardyPrimitiveFn_interactionForcing
    (sigma : ℝ) (u : GlobalSolution sigma)
    (a b : ℝ) (hab : a ≤ b) (t : ℝ) (ht : t ∈ Icc a b) :
    hardyPrimitiveFn a b (interactionForcingLp sigma u a b hab) t =
      ∫ s in a..t, freeProp (-s) (u.nonlin s) := by
  unfold hardyPrimitiveFn
  apply intervalIntegral.integral_congr_ae
  have hz := timeZeroExtension_interactionForcing_ae sigma u a b hab
  filter_upwards [hz] with s hs hsint
  rw [hs]
  apply Set.indicator_of_mem
  have hs' : s ∈ Ioc a t := by
    simpa [uIoc_of_le ht.1] using hsint
  exact ⟨hs'.1.le, hs'.2.trans ht.2⟩

def localizedSolutionHsCurve (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (a b : ℝ) (hab : a ≤ b) :
    Lp (Hs (1 / 2 : ℝ)) 2 (timeMeasure a b) :=
  localizedFreeCurveCLM chi a b (freeProp (-a) (u.u a)) -
    (Complex.I * (sigma : ℂ)) •
      retardedSmoothingCLM chi a b (interactionForcingLp sigma u a b hab)

def realizedLocalizedSolutionCurve (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (a b : ℝ) (hab : a ≤ b) :
    Lp L2 2 (timeMeasure a b) :=
  (hsHalfToL2CLM.restrictScalars ℝ).compLpL 2 (timeMeasure a b)
    (localizedSolutionHsCurve chi sigma u a b hab)

def physicalLocalizedSolution (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (t : ℝ) : L2 :=
  cutoffL2CLM chi (u.u t)

lemma continuous_physicalLocalizedSolution (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) :
    Continuous (physicalLocalizedSolution chi sigma u) :=
  (cutoffL2CLM chi).continuous.comp u.continuous

lemma physicalLocalizedSolution_memLp (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (a b : ℝ) :
    MemLp (physicalLocalizedSolution chi sigma u) 2 (timeMeasure a b) := by
  have hcompact : IsCompact (Icc a b) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    (continuous_physicalLocalizedSolution chi sigma u).norm.continuousOn
  apply MemLp.of_bound
    (continuous_physicalLocalizedSolution chi sigma u).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC ⟨t, ht, rfl⟩

def physicalLocalizedSolutionLp (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (a b : ℝ) :
    Lp L2 2 (timeMeasure a b) :=
  (physicalLocalizedSolution_memLp chi sigma u a b).toLp
    (physicalLocalizedSolution chi sigma u)

lemma physicalLocalizedSolutionLp_coe (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (a b : ℝ) :
    (physicalLocalizedSolutionLp chi sigma u a b : ℝ → L2) =ᵐ[timeMeasure a b]
      physicalLocalizedSolution chi sigma u := MemLp.coeFn_toLp _

lemma interaction_reconstruct (sigma : ℝ) (u : GlobalSolution sigma)
    (a t : ℝ) :
    u.u t = freeProp t (freeProp (-a) (u.u a)) -
      (Complex.I * (sigma : ℂ)) •
        freeProp t (∫ s in a..t, freeProp (-s) (u.nonlin s)) := by
  have hm := congrArg (freeProp t) (interaction_mild sigma u t a)
  rw [freeProp_sub, freeProp_smul] at hm
  have hcancel : freeProp t (freeProp (-t) (u.u t)) = u.u t := by
    rw [show freeProp t (freeProp (-t) (u.u t)) =
        freeProp (t + -t) (u.u t) by
      simpa using (propagator_unitary.2.1 (-t) t (u.u t))]
    rw [add_neg_cancel, propagator_unitary.2.2.1]
  rw [hcancel] at hm
  exact hm

lemma physicalLocalizedSolution_identity (chi : SchwartzMap ℝ ℂ)
    (sigma : ℝ) (u : GlobalSolution sigma) (a t : ℝ) :
    physicalLocalizedSolution chi sigma u t =
      localizedPhysicalFree chi (freeProp (-a) (u.u a)) t -
        (Complex.I * (sigma : ℂ)) •
          cutoffL2CLM chi
            (freeProp t (∫ s in a..t, freeProp (-s) (u.nonlin s))) := by
  have hm := congrArg (cutoffL2CLM chi) (interaction_reconstruct sigma u a t)
  simpa only [physicalLocalizedSolution, localizedPhysicalFree, map_sub,
    map_smul] using hm

theorem realizedLocalizedSolutionCurve_eq_physical
    (chi : SchwartzMap ℝ ℂ) (sigma : ℝ) (u : GlobalSolution sigma)
    (a b : ℝ) (hab : a ≤ b) :
    realizedLocalizedSolutionCurve chi sigma u a b hab =
      physicalLocalizedSolutionLp chi sigma u a b := by
  let c : ℂ := Complex.I * (sigma : ℂ)
  let freeHs := localizedFreeCurveCLM chi a b (freeProp (-a) (u.u a))
  let retHs := retardedSmoothingCLM chi a b
    (interactionForcingLp sigma u a b hab)
  let freePhys := localizedPhysicalFreeCurveLp chi a b (freeProp (-a) (u.u a))
  let retPhys := physicalRetardedCLM chi a b
    (interactionForcingLp sigma u a b hab)
  have hfreeEq : realizedLocalizedFreeCurveCLM chi a b (freeProp (-a) (u.u a)) =
      freePhys := realizedLocalizedFreeCurveCLM_apply chi a b _
  have hretEq :
      ((hsHalfToL2CLM.restrictScalars ℝ).compLpL 2 (timeMeasure a b)) retHs =
        retPhys := by
    exact realizedRetardedSmoothingCLM_apply chi a b
      (interactionForcingLp sigma u a b hab)
  have hfreeAe :
      (realizedLocalizedFreeCurveCLM chi a b (freeProp (-a) (u.u a)) :
          ℝ → L2) =ᵐ[timeMeasure a b] (freePhys : ℝ → L2) :=
    Filter.Eventually.of_forall fun t => congrFun
      (congrArg (fun q : Lp L2 2 (timeMeasure a b) => (q : ℝ → L2)) hfreeEq) t
  have hretAe :
      (((hsHalfToL2CLM.restrictScalars ℝ).compLpL 2
          (timeMeasure a b)) retHs : ℝ → L2) =ᵐ[timeMeasure a b]
        (retPhys : ℝ → L2) :=
    Filter.Eventually.of_forall fun t => congrFun
      (congrArg (fun q : Lp L2 2 (timeMeasure a b) => (q : ℝ → L2)) hretEq) t
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (hsHalfToL2CLM.restrictScalars ℝ)
      (localizedSolutionHsCurve chi sigma u a b hab),
    Lp.coeFn_sub freeHs (c • retHs),
    Lp.coeFn_smul c retHs,
    ContinuousLinearMap.coeFn_compLpL
      (hsHalfToL2CLM.restrictScalars ℝ) freeHs,
    ContinuousLinearMap.coeFn_compLpL
      (hsHalfToL2CLM.restrictScalars ℝ) retHs,
    hfreeAe, hretAe,
    MemLp.coeFn_toLp (localizedPhysicalFree_memLp_two_Icc chi
      (freeProp (-a) (u.u a)) a b),
    physicalRetardedCLM_coe chi a b (interactionForcingLp sigma u a b hab),
    physicalLocalizedSolutionLp_coe chi sigma u a b,
    ae_restrict_mem measurableSet_Icc]
      with t hwhole hsub hsmul hfreeReal hretReal hfreeEq_t hretEq_t
        hfreePhys hretPhys hsolution ht
  rw [show (realizedLocalizedSolutionCurve chi sigma u a b hab : ℝ → L2) t =
      hsHalfToL2CLM
        ((localizedSolutionHsCurve chi sigma u a b hab :
          ℝ → Hs (1 / 2 : ℝ)) t) by exact hwhole,
    show (localizedSolutionHsCurve chi sigma u a b hab :
        ℝ → Hs (1 / 2 : ℝ)) t =
      (freeHs : ℝ → Hs (1 / 2 : ℝ)) t -
        c • (retHs : ℝ → Hs (1 / 2 : ℝ)) t by
      change ((freeHs - c • retHs :
        Lp (Hs (1 / 2 : ℝ)) 2 (timeMeasure a b)) :
          ℝ → Hs (1 / 2 : ℝ)) t = _
      rw [hsub]
      change (freeHs : ℝ → Hs (1 / 2 : ℝ)) t -
        ((c • retHs : Lp (Hs (1 / 2 : ℝ)) 2 (timeMeasure a b)) :
          ℝ → Hs (1 / 2 : ℝ)) t = _
      rw [hsmul]
      rfl,
    map_sub, map_smul]
  have hfreePoint : hsHalfToL2CLM
      ((freeHs : ℝ → Hs (1 / 2 : ℝ)) t) =
      localizedPhysicalFree chi (freeProp (-a) (u.u a)) t := by
    calc
      _ = (realizedLocalizedFreeCurveCLM chi a b
          (freeProp (-a) (u.u a)) : ℝ → L2) t := hfreeReal.symm
      _ = (freePhys : ℝ → L2) t := hfreeEq_t
      _ = _ := hfreePhys
  have hretPoint : hsHalfToL2CLM
      ((retHs : ℝ → Hs (1 / 2 : ℝ)) t) =
      cutoffL2CLM chi
        (freeProp t (∫ s in a..t, freeProp (-s) (u.nonlin s))) := by
    calc
      _ = (((hsHalfToL2CLM.restrictScalars ℝ).compLpL 2
          (timeMeasure a b)) retHs : ℝ → L2) t := hretReal.symm
      _ = (retPhys : ℝ → L2) t := hretEq_t
      _ = cutoffL2CLM chi
          (freeProp t (hardyPrimitiveFn a b
            (interactionForcingLp sigma u a b hab) t)) := hretPhys
      _ = _ := by rw [hardyPrimitiveFn_interactionForcing sigma u a b hab t ht]
  rw [hfreePoint, hretPoint, hsolution,
    physicalLocalizedSolution_identity chi sigma u a t]

/-- Every compact spatial localization of an `L²` cubic NLS solution belongs
to `L²_t H^{1/2}_x` on a compact time interval. -/
theorem localizedSolutionHsCurve_represents
    (chi : SchwartzMap ℝ ℂ) (sigma : ℝ) (u : GlobalSolution sigma)
    (a b : ℝ) (hab : a ≤ b) :
    IsLocalizedHsRepresentative chi (Icc a b) u.u
      (localizedSolutionHsCurve chi sigma u a b hab :
        ℝ → Hs (1 / 2 : ℝ)) := by
  have hreal := ContinuousLinearMap.coeFn_compLpL
    (hsHalfToL2CLM.restrictScalars ℝ)
    (localizedSolutionHsCurve chi sigma u a b hab)
  have hphys := physicalLocalizedSolutionLp_coe chi sigma u a b
  have heq := congrArg
    (fun q : Lp L2 2 (timeMeasure a b) => (q : ℝ → L2))
    (realizedLocalizedSolutionCurve_eq_physical chi sigma u a b hab)
  filter_upwards [hreal, hphys] with t hreal_t hphys_t
  rw [Hs.toTempered_toL2 (s := (1 / 2 : ℝ)) (by norm_num)]
  rw [← hsHalfToL2CLM_apply]
  have hL2 : hsHalfToL2CLM
      ((localizedSolutionHsCurve chi sigma u a b hab :
        ℝ → Hs (1 / 2 : ℝ)) t) = cutoffL2CLM chi (u.u t) := by
    calc
      _ = (realizedLocalizedSolutionCurve chi sigma u a b hab : ℝ → L2) t :=
        hreal_t.symm
      _ = (physicalLocalizedSolutionLp chi sigma u a b : ℝ → L2) t :=
        congrFun heq t
      _ = cutoffL2CLM chi (u.u t) := hphys_t
  rw [hL2]
  exact toTemperedDistribution_cutoffL2CLM chi (u.u t)

end CubicNLSPhaseRetrieval
