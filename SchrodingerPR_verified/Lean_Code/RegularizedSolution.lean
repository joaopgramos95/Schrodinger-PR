import Lean_Code.RegularizedFreeCurve

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- The interaction-picture solution after spatial resolvent smoothing. -/
def regularizedInteraction (n : ℕ) {σ : ℝ} (u : GlobalSolution σ)
    (t : ℝ) : L2 :=
  frequencySmoothCLM n (freeProp (-t) (u.u t))

lemma regularizedInteraction_eq (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (t : ℝ) :
    regularizedInteraction n u t =
      freeProp (-t) (frequencySmoothCLM n (u.u t)) := by
  exact frequencySmoothCLM_comm_freeProp n (-t) (u.u t)

lemma freeProp_regularizedInteraction (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (t : ℝ) :
    freeProp t (regularizedInteraction n u t) =
      frequencySmoothCLM n (u.u t) := by
  rw [regularizedInteraction_eq]
  rw [show freeProp t (freeProp (-t) (frequencySmoothCLM n (u.u t))) =
      freeProp (t + (-t)) (frequencySmoothCLM n (u.u t)) by
    simpa using (propagator_unitary.2.1 (-t) t
      (frequencySmoothCLM n (u.u t)))]
  simp [propagator_unitary.2.2.1]

/-- Spatial resolvent smoothing upgrades the continuous mild solution to an
absolutely continuous physical `L²` curve on every compact interval. -/
lemma frequencySmooth_solution_absolutelyContinuousOnInterval
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => frequencySmoothCLM n (u.u t)) a b := by
  let R : (L2 →L[ℂ] L2) →L[ℝ] (L2 →L[ℝ] L2) :=
    ContinuousLinearMap.restrictScalarsL ℂ L2 L2 ℝ ℝ
  have hA0 := regularizedFreeCLM_absolutelyContinuousOnInterval n a b
  have hA : AbsolutelyContinuousOnInterval
      (fun t => R (regularizedFreeCLM n t)) a b :=
    AbsolutelyContinuousOnInterval.comp_continuousLinearMap hA0 R
  have hz := interaction_curve_absolutelyContinuousOnInterval σ u a b
  have hout := AbsolutelyContinuousOnInterval.clm_apply hz hA
    (ContinuousLinearMap.apply ℝ L2)
  have heq : (fun t =>
      (R (regularizedFreeCLM n t)) (freeProp (-t) (u.u t))) =
      fun t => frequencySmoothCLM n (u.u t) := by
    funext t
    change freeProp t (frequencySmoothCLM n (freeProp (-t) (u.u t))) = _
    rw [frequencySmoothCLM_comm_freeProp]
    rw [show freeProp t (freeProp (-t) (frequencySmoothCLM n (u.u t))) =
        freeProp (t + (-t)) (frequencySmoothCLM n (u.u t)) by
      simpa using (propagator_unitary.2.1 (-t) t
        (frequencySmoothCLM n (u.u t)))]
    simp [propagator_unitary.2.2.1]
  rw [← heq]
  exact hout

lemma regularizedInteraction_generator_memLp (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (t : ℝ) :
    MemLp (fun ξ : ℝ => schrodingerGenerator ξ *
      (fourierL2 (regularizedInteraction n u t) : ℝ → ℂ) ξ) 2 volume := by
  exact frequencySmooth_generator_memLp n (freeProp (-t) (u.u t))

lemma regularizedInteraction_ae_hasDerivAt (n : ℕ) (σ : ℝ)
    (u : GlobalSolution σ) (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt (regularizedInteraction n u)
        (frequencySmoothCLM n
          (-(Complex.I * (σ : ℂ)) • freeProp (-t) (u.nonlin t))) t := by
  have hu := interaction_curve_ae_hasDerivAt σ u a b
  filter_upwards [hu] with t ht htI
  have h := ht htI
  let Pℝ : L2 →L[ℝ] L2 := (frequencySmoothCLM n).restrictScalars ℝ
  have hout := Pℝ.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt
    (fun s => frequencySmoothCLM n (freeProp (-s) (u.u s))) _ t
  simpa [Pℝ, Function.comp_def] using hout

lemma freeProp_regularizedInteraction_derivative_forcing (n : ℕ) (σ : ℝ)
    (u : GlobalSolution σ) (t : ℝ) :
    freeProp t (frequencySmoothCLM n
      (-(Complex.I * (σ : ℂ)) • freeProp (-t) (u.nonlin t))) =
      -(Complex.I * (σ : ℂ)) • frequencySmoothCLM n (u.nonlin t) := by
  rw [map_smul, freeProp_smul]
  rw [frequencySmoothCLM_comm_freeProp]
  rw [show freeProp t (freeProp (-t) (frequencySmoothCLM n (u.nonlin t))) =
      freeProp (t + (-t)) (frequencySmoothCLM n (u.nonlin t)) by
    simpa using (propagator_unitary.2.1 (-t) t
      (frequencySmoothCLM n (u.nonlin t)))]
  simp [propagator_unitary.2.2.1]

/-- Almost-everywhere strong equation for the spatially regularized physical
solution. -/
lemma frequencySmooth_solution_ae_hasDerivAt (n : ℕ) (σ : ℝ)
    (u : GlobalSolution σ) (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt (fun s => frequencySmoothCLM n (u.u s))
        (freePropDerivative (regularizedInteraction n u t)
            (regularizedInteraction_generator_memLp n u t) t -
          (Complex.I * (σ : ℂ)) • frequencySmoothCLM n (u.nonlin t)) t := by
  have hy := regularizedInteraction_ae_hasDerivAt n σ u a b
  filter_upwards [hy] with t ht htI
  have hprod := hasDerivAt_freeProp_comp (ht htI)
    (regularizedInteraction_generator_memLp n u t)
  rw [show (fun s => freeProp s (regularizedInteraction n u s)) =
      fun s => frequencySmoothCLM n (u.u s) by
    funext s
    exact freeProp_regularizedInteraction n u s] at hprod
  rw [freeProp_regularizedInteraction_derivative_forcing] at hprod
  simpa [sub_eq_add_neg] using hprod

end CubicNLSPhaseRetrieval
