import Lean_Code.Setup
import Lean_Code.BanachFTC

/-!
# Interaction-picture weak formulation for mild solutions

The rough free orbit is not differentiated in `L²`.  Instead we first pass to
`S(-t)u(t)`, whose evolution is an ordinary Bochner integral.  This identity
is the starting point for the local one-particle and exterior-product weak
equations.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The Duhamel formula after conjugation by the inverse free group. -/
theorem interaction_mild (sigma : ℝ) (u : GlobalSolution sigma) (t t0 : ℝ) :
    freeProp (-t) (u.u t) = freeProp (-t0) (u.u t0) -
      (Complex.I * (sigma : ℂ)) •
        ∫ s in t0..t, freeProp (-s) (u.nonlin s) := by
  rw [u.mild t t0]
  rw [freeProp_sub, freeProp_smul]
  have hfree : freeProp (-t) (freeProp (t - t0) (u.u t0)) =
      freeProp (-t0) (u.u t0) := by
    rw [show freeProp (-t) (freeProp (t - t0) (u.u t0)) =
        freeProp ((-t) + (t - t0)) (u.u t0) by
      simpa using (propagator_unitary.2.1 (t - t0) (-t) (u.u t0))]
    congr 1
    ring
  rw [hfree]
  let S : L2 →L[ℂ] L2 :=
    (freePropLIE (-t)).toContinuousLinearEquiv.toContinuousLinearMap
  have hmap := S.intervalIntegral_comp_comm (u.forcing_integrable t0 t)
  have hint : freeProp (-t)
        (∫ s in t0..t, freeProp (t - s) (u.nonlin s)) =
      ∫ s in t0..t, freeProp (-s) (u.nonlin s) := by
    change S (∫ s in t0..t, freeProp (t - s) (u.nonlin s)) = _
    rw [← hmap]
    apply intervalIntegral.integral_congr
    intro s hs
    change freeProp (-t) (freeProp (t - s) (u.nonlin s)) =
      freeProp (-s) (u.nonlin s)
    rw [show freeProp (-t) (freeProp (t - s) (u.nonlin s)) =
        freeProp ((-t) + (t - s)) (u.nonlin s) by
      simpa using (propagator_unitary.2.1 (t - s) (-t) (u.nonlin s))]
    congr 1
    ring
  rw [hint]

/-- The interaction-picture forcing is Bochner-integrable on every compact
time interval. -/
theorem interaction_forcing_intervalIntegrable (sigma : ℝ)
    (u : GlobalSolution sigma) (a b : ℝ) :
    IntervalIntegrable (fun s => freeProp (-s) (u.nonlin s)) volume a b := by
  let S : L2 →L[ℂ] L2 :=
    (freePropLIE (-b)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := u.forcing_integrable a b
  have hS : IntervalIntegrable
      (fun s => S (freeProp (b - s) (u.nonlin s))) volume a b :=
    ⟨S.integrable_comp h.1, S.integrable_comp h.2⟩
  apply hS.congr
  intro s hs
  change freeProp (-b) (freeProp (b - s) (u.nonlin s)) =
    freeProp (-s) (u.nonlin s)
  rw [show freeProp (-b) (freeProp (b - s) (u.nonlin s)) =
      freeProp ((-b) + (b - s)) (u.nonlin s) by
    simpa using (propagator_unitary.2.1 (b - s) (-b) (u.nonlin s))]
  congr 1
  ring

/-- The interaction-picture solution curve is absolutely continuous on every
compact interval. -/
theorem interaction_curve_absolutelyContinuousOnInterval (sigma : ℝ)
    (u : GlobalSolution sigma) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => freeProp (-t) (u.u t)) a b := by
  let c : ℂ := Complex.I * (sigma : ℂ)
  let w0 : L2 := freeProp (-a) (u.u a)
  let g : ℝ → L2 := fun t => freeProp (-t) (u.nonlin t)
  let G : ℝ → L2 := fun t => ∫ s in a..t, g s
  have hg : IntervalIntegrable g volume a b :=
    interaction_forcing_intervalIntegrable sigma u a b
  have hG : AbsolutelyContinuousOnInterval G a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_apply hg
      Set.left_mem_uIcc
  have hright : AbsolutelyContinuousOnInterval (fun t => c • G t) a b :=
    hG.const_smul c
  have hform : (fun t => freeProp (-t) (u.u t)) = fun t => w0 - c • G t := by
    funext t
    simpa [c, w0, g, G] using interaction_mild sigma u t a
  rw [hform]
  exact (absolutelyContinuousOnInterval_const w0 a b).sub hright

/-- Almost-everywhere derivative of the interaction-picture solution. -/
theorem interaction_curve_ae_hasDerivAt (sigma : ℝ)
    (u : GlobalSolution sigma) (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt (fun s => freeProp (-s) (u.u s))
        (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (u.nonlin t)) t := by
  let c : ℂ := Complex.I * (sigma : ℂ)
  let w0 : L2 := freeProp (-a) (u.u a)
  let g : ℝ → L2 := fun t => freeProp (-t) (u.nonlin t)
  let G : ℝ → L2 := fun t => ∫ s in a..t, g s
  have hg : IntervalIntegrable g volume a b :=
    interaction_forcing_intervalIntegrable sigma u a b
  have hform : (fun t => freeProp (-t) (u.u t)) = fun t => w0 - c • G t := by
    funext t
    simpa [c, w0, g, G] using interaction_mild sigma u t a
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht htmem
  have hG : HasDerivAt G (g t) t := ht htmem a Set.left_mem_uIcc
  have hconst : HasDerivAt (fun _ : ℝ => w0) 0 t := hasDerivAt_const t w0
  rw [hform]
  change HasDerivAt ((fun _ : ℝ => w0) - c • G)
    (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (u.nonlin t)) t
  simpa [Pi.smul_apply, c, g, G] using hconst.sub (hG.const_smul c)

/-- Weak fundamental theorem for a Banach-valued indefinite integral.  The
Schwartz endpoint assumptions are exactly the form used after enclosing a
compactly supported spacetime test in a finite time interval. -/
theorem intervalIntegral_primitive_smul_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [CompleteSpace E] [IsScalarTower ℝ ℂ E]
    {g : ℝ → E} (eta : SchwartzMap ℝ ℂ) {a b : ℝ}
    (hab : a < b) (hg : IntervalIntegrable g volume a b)
    (hetab : eta b = 0) :
    (∫ t in a..b, deriv eta t • (∫ s in a..t, g s)) =
      -∫ t in a..b, eta t • g t := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc a b)
  let coef : ℝ × ℝ → ℂ := fun p => if p.2 ≤ p.1 then deriv eta p.1 else 0
  let K : ℝ × ℝ → E := fun p => coef p • g p.2
  have hderivc : Continuous (deriv (eta : ℝ → ℂ)) := by
    simpa only [iteratedDeriv_one] using
      (eta.smooth ⊤).continuous_iteratedDeriv 1 (by simp)
  have hcoefmeas : AEStronglyMeasurable coef (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    dsimp [coef]
    apply Measurable.ite
    · exact measurableSet_le measurable_snd measurable_fst
    · exact hderivc.measurable.comp measurable_fst
    · exact measurable_const
  let C : ℝ := SchwartzMap.seminorm ℂ 0 1 eta
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hderivbound (t : ℝ) : ‖deriv (eta : ℝ → ℂ) t‖ ≤ C := by
    have heval : deriv (eta : ℝ → ℂ) t =
        fderiv ℝ (eta : ℝ → ℂ) t 1 := by
      simpa using (eta.differentiableAt.hasDerivAt.deriv :
        deriv (eta : ℝ → ℂ) t = _)
    rw [heval]
    calc
      ‖fderiv ℝ (eta : ℝ → ℂ) t 1‖ ≤
          ‖fderiv ℝ (eta : ℝ → ℂ) t‖ := by
        simpa using ContinuousLinearMap.le_opNorm
          (fderiv ℝ (eta : ℝ → ℂ) t) (1 : ℝ)
      _ ≤ C := by
        simpa [C] using
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ eta 1 t
  have hcoefbound : ∀ᵐ p ∂(mu.prod mu), ‖coef p‖ ≤ C := by
    filter_upwards with p
    dsimp [coef]
    split_ifs with hle
    · exact hderivbound p.1
    · simpa using hC0
  have hgmu : Integrable g mu :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hg
  have hbase : Integrable (fun p : ℝ × ℝ => g p.2) (mu.prod mu) :=
    hgmu.comp_snd mu
  have hK : Integrable K (mu.prod mu) :=
    hbase.bdd_smul C hcoefmeas hcoefbound
  have hswap := (MeasureTheory.integral_prod K hK).symm.trans
    (MeasureTheory.integral_prod_symm K hK)
  have hinner_left (t : ℝ) (ht : t ∈ Set.Ioc a b) :
      (∫ s, K (t, s) ∂mu) = deriv (eta : ℝ → ℂ) t •
        (∫ s in a..t, g s) := by
    have hfun : (fun s => K (t, s)) =
        Set.indicator (Set.Iic t)
          (fun s => deriv (eta : ℝ → ℂ) t • g s) := by
      funext s
      simp only [K, coef, Set.indicator, Set.mem_Iic]
      split_ifs <;> simp
    rw [hfun, integral_indicator measurableSet_Iic, integral_smul]
    congr 1
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hset : Set.Iic t ∩ Set.Ioc a b = Set.Ioc a t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨hst, has, hsb⟩
        exact ⟨has, hst⟩
      · rintro ⟨has, hst⟩
        exact ⟨hst, has, hst.trans ht.2⟩
    rw [hset, ← intervalIntegral.integral_of_le ht.1.le]
  have hleft : (∫ t, ∫ s, K (t, s) ∂mu ∂mu) =
      ∫ t in a..b, deriv (eta : ℝ → ℂ) t • (∫ s in a..t, g s) := by
    rw [intervalIntegral.integral_of_le hab.le]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hinner_left t ht
  have hinner_right (s : ℝ) (hs : s ∈ Set.Ioc a b) :
      (∫ t, K (t, s) ∂mu) = -eta s • g s := by
    have hfun : (fun t => K (t, s)) =
        Set.indicator (Set.Ici s)
          (fun t => deriv (eta : ℝ → ℂ) t • g s) := by
      funext t
      simp only [K, coef, Set.indicator, Set.mem_Ici]
      split_ifs <;> simp_all
    rw [hfun, integral_indicator measurableSet_Ici, integral_smul_const]
    have hmeasure : mu.restrict (Set.Ici s) =
        volume.restrict (Set.Ioc s b) := by
      dsimp [mu]
      rw [Measure.restrict_restrict measurableSet_Ici]
      have hset : Set.Ici s ∩ Set.Ioc a b = Set.Icc s b := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
        constructor
        · rintro ⟨hst, hat, htb⟩
          exact ⟨hst, htb⟩
        · rintro ⟨hst, htb⟩
          exact ⟨hst, hs.1.trans_le hst, htb⟩
      rw [hset, Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    rw [hmeasure, ← intervalIntegral.integral_of_le hs.2]
    have hinter : (∫ t in s..b, deriv (eta : ℝ → ℂ) t) =
        eta b - eta s := by
      apply intervalIntegral.integral_deriv_eq_sub
      · intro t ht
        exact eta.differentiableAt
      · exact hderivc.continuousOn.intervalIntegrable
    rw [hinter, hetab]
    simp
  have hright : (∫ s, ∫ t, K (t, s) ∂mu ∂mu) =
      -∫ s in a..b, eta s • g s := by
    rw [intervalIntegral.integral_of_le hab.le, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [hinner_right s hs]
    simp
  rw [hleft, hright] at hswap
  exact hswap

/-- Distributional evolution of the interaction-picture curve on a finite
interval. -/
theorem interaction_weak_identity (sigma : ℝ) (u : GlobalSolution sigma)
    (eta : SchwartzMap ℝ ℂ) {a b : ℝ} (hab : a < b)
    (hetaa : eta a = 0) (hetab : eta b = 0) :
    (∫ t in a..b, deriv eta t • freeProp (-t) (u.u t)) =
      (Complex.I * (sigma : ℂ)) •
        ∫ t in a..b, eta t • freeProp (-t) (u.nonlin t) := by
  let c : ℂ := Complex.I * (sigma : ℂ)
  let w0 : L2 := freeProp (-a) (u.u a)
  let g : ℝ → L2 := fun t => freeProp (-t) (u.nonlin t)
  let G : ℝ → L2 := fun t => ∫ s in a..t, g s
  have hg : IntervalIntegrable g volume a b :=
    interaction_forcing_intervalIntegrable sigma u a b
  have hGcont : ContinuousOn G (Set.uIcc a b) := by
    exact intervalIntegral.continuousOn_primitive_interval' hg
      (Set.left_mem_uIcc)
  have hderivc : Continuous (deriv (eta : ℝ → ℂ)) := by
    simpa only [iteratedDeriv_one] using
      (eta.smooth ⊤).continuous_iteratedDeriv 1 (by simp)
  have hfirst : IntervalIntegrable
      (fun t => deriv (eta : ℝ → ℂ) t • w0) volume a b :=
    hderivc.continuousOn.intervalIntegrable.smul_continuousOn continuousOn_const
  have hsecond : IntervalIntegrable
      (fun t => deriv (eta : ℝ → ℂ) t • (c • G t)) volume a b :=
    hderivc.continuousOn.intervalIntegrable.smul_continuousOn
      ((show ContinuousOn (fun _ : ℝ => c) (Set.uIcc a b) from
        continuousOn_const).smul hGcont)
  have hrewrite (t : ℝ) :
      deriv (eta : ℝ → ℂ) t • freeProp (-t) (u.u t) =
        deriv (eta : ℝ → ℂ) t • w0 -
          deriv (eta : ℝ → ℂ) t • (c • G t) := by
    rw [interaction_mild sigma u t a]
    simp only [w0, c, G, g, smul_sub, smul_smul]
  rw [intervalIntegral.integral_congr (fun t ht => hrewrite t),
    intervalIntegral.integral_sub hfirst hsecond,
    intervalIntegral.integral_smul_const]
  have hdint : (∫ t in a..b, deriv (eta : ℝ → ℂ) t) = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun t ht => eta.differentiableAt)
      hderivc.continuousOn.intervalIntegrable, hetab, hetaa, sub_self]
  rw [hdint, zero_smul, zero_sub]
  have hfactor :
      (∫ t in a..b, deriv (eta : ℝ → ℂ) t • (c • G t)) =
        c • ∫ t in a..b, deriv (eta : ℝ → ℂ) t • G t := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    change deriv (eta : ℝ → ℂ) t • (c • G t) =
      c • (deriv (eta : ℝ → ℂ) t • G t)
    simp only [smul_smul, mul_comm]
  rw [hfactor, intervalIntegral_primitive_smul_deriv eta hab hg hetab,
    smul_neg, neg_neg]

end CubicNLSPhaseRetrieval
