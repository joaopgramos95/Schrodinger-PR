import Lean_Code.CarlemanFourier2D
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Weak ODEs with values in a Banach space

This file supplies the time-regularization step used in the frequency-localized
Carleman argument.  It deliberately works with scalar Schwartz tests, which is
the distributional interface produced by the PDE.
-/

open Filter Function MeasureTheory
open scoped Convolution SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- A Banach-valued first-order ODE, tested distributionally in time. -/
def IsWeakVectorODE (A : E →L[ℂ] E) (y g : ℝ → E) : Prop :=
  ∀ η : 𝓢(ℝ, ℂ), HasCompactSupport (η : ℝ → ℂ) →
    (∫ t, (-deriv (η : ℝ → ℂ) t) • y t - η t • A (y t)) =
      ∫ t, η t • g t

private lemma realKernelTest_deriv
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ 1 κ) (t s : ℝ) :
    deriv (fun r : ℝ => ((κ (t - r) : ℝ) : ℂ)) s =
      -((deriv κ (t - s) : ℝ) : ℂ) := by
  have hsub : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
    exact (hasDerivAt_id s).const_sub t
  have hk := (hκ.differentiable (by norm_num) (t - s)).hasDerivAt.comp s hsub
  have hc := hk.ofReal_comp
  convert hc.deriv using 1 <;> norm_num

private lemma realKernelTest_contDiff
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => ((κ (t - s) : ℝ) : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp (hκ.comp (by fun_prop))

private lemma realKernelTest_hasCompactSupport
    (κ : ℝ → ℝ) (hκ : HasCompactSupport κ) (t : ℝ) :
    HasCompactSupport (fun s : ℝ => ((κ (t - s) : ℝ) : ℂ)) := by
  have hcomp : HasCompactSupport (κ ∘ (Homeomorph.subLeft t : ℝ → ℝ)) :=
    hκ.comp_homeomorph (Homeomorph.subLeft t)
  change HasCompactSupport
    ((fun x : ℝ => (x : ℂ)) ∘ (κ ∘ (Homeomorph.subLeft t : ℝ → ℝ)))
  exact hcomp.comp_left (by norm_num)

/-- Convolution in time turns a weak vector ODE into a classical one. -/
theorem IsWeakVectorODE.hasDerivAt_convolution
    (A : E →L[ℂ] E) (y g : ℝ → E)
    (hy : LocallyIntegrable y volume) (hg : LocallyIntegrable g volume)
    (hweak : IsWeakVectorODE A y g)
    (κ : ℝ → ℝ)
    (hκdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hκsupp : HasCompactSupport κ) (t : ℝ) :
    HasDerivAt (y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ)
      (A ((y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t) +
        (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t) t := by
  have hκone : ContDiff ℝ 1 κ := hκdiff.of_le (by norm_num)
  have hderiv := hκsupp.hasDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hy hκone t
  let η : 𝓢(ℝ, ℂ) :=
    (realKernelTest_hasCompactSupport κ hκsupp t).toSchwartzMap
      (realKernelTest_contDiff κ hκdiff t)
  have hη : (η : ℝ → ℂ) = fun s => ((κ (t - s) : ℝ) : ℂ) := rfl
  have hw := hweak η (realKernelTest_hasCompactSupport κ hκsupp t)
  have hderivη (s : ℝ) : deriv (η : ℝ → ℂ) s =
      -((deriv κ (t - s) : ℝ) : ℂ) := by
    rw [hη]
    exact realKernelTest_deriv κ hκone t s
  have hconvA :
      A ((y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t) =
        ∫ s, κ (t - s) • A (y s) := by
    rw [MeasureTheory.convolution_def]
    rw [← A.integral_comp_comm
      ((hκsupp.convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ).flip hy hκdiff.continuous t).integrable)]
    apply integral_congr_ae
    filter_upwards with s
    exact A.map_smul_of_tower (κ (t - s)) (y s)
  have heq :
      ((y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] deriv κ) t) =
        A ((y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t) +
          (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t := by
    change (∫ s, (deriv κ (t - s)) • y s) = _
    rw [hconvA, MeasureTheory.convolution_def]
    change (∫ s, (deriv κ (t - s)) • y s) =
      (∫ s, κ (t - s) • A (y s)) + ∫ s, κ (t - s) • g s
    have hw' :
        (∫ s, (deriv κ (t - s)) • y s - κ (t - s) • A (y s)) =
          ∫ s, κ (t - s) • g s := by
      have hw'' := hw
      have hηval (s : ℝ) : η s = ((κ (t - s) : ℝ) : ℂ) := by
        exact congrFun hη s
      simp_rw [hderivη, hηval, neg_neg] at hw''
      change (∫ s, ((deriv κ (t - s) : ℝ) : ℂ) • y s -
          ((κ (t - s) : ℝ) : ℂ) • A (y s)) =
        ∫ s, ((κ (t - s) : ℝ) : ℂ) • g s at hw''
      calc
        (∫ s, (deriv κ (t - s)) • y s - κ (t - s) • A (y s)) =
            ∫ s, ((deriv κ (t - s) : ℝ) : ℂ) • y s -
              ((κ (t - s) : ℝ) : ℂ) • A (y s) := by
          apply integral_congr_ae
          filter_upwards with s
          exact congrArg₂ (· - ·)
            (RCLike.real_smul_eq_coe_smul (K := ℂ)
              (deriv κ (t - s)) (y s))
            (RCLike.real_smul_eq_coe_smul (K := ℂ)
              (κ (t - s)) (A (y s)))
        _ = ∫ s, ((κ (t - s) : ℝ) : ℂ) • g s := hw''
        _ = ∫ s, κ (t - s) • g s := by
          apply integral_congr_ae
          filter_upwards with s
          exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
            (κ (t - s)) (g s)).symm
    rw [← hw']
    have hAyloc : LocallyIntegrable (fun s => A (y s)) volume := by
      intro x
      exact A.integrableAtFilter_comp (hy x)
    have hintA : Integrable (fun s => κ (t - s) • A (y s)) volume := by
      simpa using ((hκsupp.convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ).flip hAyloc hκdiff.continuous t).integrable)
    have hκdDiff : Continuous (deriv κ) := by
      simpa only [iteratedDeriv_one] using
        (hκdiff.continuous_iteratedDeriv 1 (by
          change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top))
    have hintD : Integrable (fun s => deriv κ (t - s) • y s) volume := by
      simpa using ((hκsupp.deriv.convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ).flip hy hκdDiff t).integrable)
    rw [integral_sub hintD hintA]
    abel
  exact hderiv.congr_deriv heq

/-- Forward Duhamel estimate for a differentiable Banach-valued ODE and a
contractive semigroup. -/
theorem vectorODE_forward_estimate
    (A : E →L[ℝ] E) (S : ℝ → E →L[ℝ] E)
    (hSderiv : ∀ τ : ℝ,
      HasDerivAt S (A.comp (S τ)) τ)
    (hSzero : S 0 = ContinuousLinearMap.id ℝ E)
    (hScomm : ∀ τ : ℝ, (S τ).comp A = A.comp (S τ))
    (hSnorm : ∀ τ : ℝ, 0 ≤ τ → ∀ x : E, ‖S τ x‖ ≤ ‖x‖)
    (Y G : ℝ → E)
    (hY : ∀ s : ℝ, HasDerivAt Y (A (Y s) + G s) s)
    (hG : Continuous G) (c t : ℝ) (hct : c ≤ t) (hYc : Y c = 0) :
    ‖Y t‖ ≤ ∫ s in c..t, ‖G s‖ := by
  let F : ℝ → E := fun s => S (t - s) (Y s)
  have hF (s : ℝ) : HasDerivAt F (S (t - s) (G s)) s := by
    have hsub : HasDerivAt (fun r : ℝ => t - r) (-1) s :=
      (hasDerivAt_id s).const_sub t
    have hSc := (hSderiv (t - s)).scomp s hsub
    have happ := hSc.clm_apply (hY s)
    apply happ.congr_deriv
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, neg_one_smul]
    rw [map_add]
    have hc : S (t - s) (A (Y s)) = A (S (t - s) (Y s)) := by
      exact congrArg (fun L : E →L[ℝ] E => L (Y s)) (hScomm (t - s))
    rw [hc]
    change -(A (S (t - s) (Y s))) +
      (A (S (t - s) (Y s)) + S (t - s) (G s)) = S (t - s) (G s)
    abel
  have hSint : IntervalIntegrable (fun s => S (t - s) (G s)) volume c t := by
    have hScont : Continuous S := continuous_iff_continuousAt.2 fun r =>
      (hSderiv r).continuousAt
    exact (hScont.comp (by fun_prop)).clm_apply hG |>.intervalIntegrable c t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := c) (b := t) (f := F) (f' := fun s => S (t - s) (G s))
    (fun s _ => hF s) hSint
  have hFt : F t = Y t := by simp [F, hSzero]
  have hFc : F c = 0 := by simp [F, hYc]
  have hformula : Y t = ∫ s in c..t, S (t - s) (G s) := by
    rw [hFTC, hFt, hFc, sub_zero]
  rw [hformula]
  apply intervalIntegral.norm_integral_le_of_norm_le hct
  · filter_upwards with s hs
    exact hSnorm (t - s) (sub_nonneg.mpr hs.2) (G s)
  · exact hG.norm.intervalIntegrable c t

/-- Backward Duhamel estimate for the opposite contractive branch. -/
theorem vectorODE_backward_estimate
    (A : E →L[ℝ] E) (S : ℝ → E →L[ℝ] E)
    (hSderiv : ∀ τ : ℝ,
      HasDerivAt S (A.comp (S τ)) τ)
    (hSzero : S 0 = ContinuousLinearMap.id ℝ E)
    (hScomm : ∀ τ : ℝ, (S τ).comp A = A.comp (S τ))
    (hSnorm : ∀ τ : ℝ, τ ≤ 0 → ∀ x : E, ‖S τ x‖ ≤ ‖x‖)
    (Y G : ℝ → E)
    (hY : ∀ s : ℝ, HasDerivAt Y (A (Y s) + G s) s)
    (hG : Continuous G) (t c : ℝ) (htc : t ≤ c) (hYc : Y c = 0) :
    ‖Y t‖ ≤ ∫ s in t..c, ‖G s‖ := by
  let F : ℝ → E := fun s => S (t - s) (Y s)
  have hF (s : ℝ) : HasDerivAt F (S (t - s) (G s)) s := by
    have hsub : HasDerivAt (fun r : ℝ => t - r) (-1) s :=
      (hasDerivAt_id s).const_sub t
    have hSc := (hSderiv (t - s)).scomp s hsub
    have happ := hSc.clm_apply (hY s)
    apply happ.congr_deriv
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, neg_one_smul]
    rw [map_add]
    have hc : S (t - s) (A (Y s)) = A (S (t - s) (Y s)) := by
      exact congrArg (fun L : E →L[ℝ] E => L (Y s)) (hScomm (t - s))
    rw [hc]
    change -(A (S (t - s) (Y s))) +
      (A (S (t - s) (Y s)) + S (t - s) (G s)) = S (t - s) (G s)
    abel
  have hSint : IntervalIntegrable (fun s => S (t - s) (G s)) volume t c := by
    have hScont : Continuous S := continuous_iff_continuousAt.2 fun r =>
      (hSderiv r).continuousAt
    exact (hScont.comp (by fun_prop)).clm_apply hG |>.intervalIntegrable t c
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t) (b := c) (f := F) (f' := fun s => S (t - s) (G s))
    (fun s _ => hF s) hSint
  have hFt : F t = Y t := by simp [F, hSzero]
  have hFc : F c = 0 := by simp [F, hYc]
  have hformula : Y t = -(∫ s in t..c, S (t - s) (G s)) := by
    rw [hFTC, hFc, hFt]
    abel
  rw [hformula, norm_neg]
  apply intervalIntegral.norm_integral_le_of_norm_le htc
  · filter_upwards with s hs
    exact hSnorm (t - s) (sub_nonpos.mpr hs.1.le) (G s)
  · exact hG.norm.intervalIntegrable t c

/-- Convolution on the right by a nonnegative scalar kernel of mass one is
an `L¹` contraction for Banach-valued functions. -/
theorem integral_norm_convolution_right_le
    (g : ℝ → E) (hg : Integrable g volume)
    (κ : ℝ → ℝ) (hκ : Integrable κ volume)
    (hκnonneg : ∀ s, 0 ≤ κ s) (hκone : ∫ s, κ s = 1) :
    (∫ t, ‖(g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t‖) ≤
      ∫ t, ‖g t‖ := by
  let M : ℝ → ℝ :=
    (fun s => ‖g s‖) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ
  have hgNorm : Integrable (fun s => ‖g s‖) volume := hg.norm
  have hMint : Integrable M volume :=
    hgNorm.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hκ
  have hpoint : ∀ᵐ t ∂volume,
      ‖(g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t‖ ≤ M t := by
    have hprod := hgNorm.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hκ
    filter_upwards [hprod.prod_right_ae] with t hint
    rw [MeasureTheory.convolution_def]
    have hnorm : ∀ᵐ s ∂volume,
        ‖((ContinuousLinearMap.lsmul ℝ ℝ).flip (g s)) (κ (t - s))‖ ≤
          ‖g s‖ * κ (t - s) := by
      filter_upwards with s
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (hκnonneg (t - s))]
      exact le_of_eq (mul_comm (κ (t - s)) ‖g s‖)
    refine (norm_integral_le_of_norm_le hint hnorm).trans_eq ?_
    · change (∫ s, ‖g s‖ * κ (t - s)) = M t
      dsimp [M]
      rw [MeasureTheory.convolution_def]
      rfl
  calc
    (∫ t, ‖(g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ) t‖) ≤
        ∫ t, M t := integral_mono_of_nonneg
          (Eventually.of_forall fun _ => norm_nonneg _) hMint hpoint
    _ = (∫ s, ‖g s‖) * ∫ s, κ s := by
      exact integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hgNorm hκ
    _ = ∫ s, ‖g s‖ := by rw [hκone, mul_one]

private def vectorODEApproxBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := ((1 : ℝ) / (n + 1)) / 2
  rOut := (1 : ℝ) / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply half_lt_self
    positivity

private lemma vectorODEApproxBump_rOut_tendsto :
    Tendsto (fun n => (vectorODEApproxBump n).rOut) atTop (𝓝 0) := by
  simpa [vectorODEApproxBump] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma vectorODEApproxBump_ratio :
    ∀ n, (vectorODEApproxBump n).rOut ≤
      2 * (vectorODEApproxBump n).rIn := by
  intro n
  change (1 : ℝ) / (n + 1) ≤ 2 * ((1 : ℝ) / (n + 1) / 2)
  ring_nf
  exact le_rfl

/-- Sharp weak-ODE estimate for a branch whose semigroup is contractive for
positive time increments. -/
theorem weakVectorODE_ae_norm_le_forward
    (A : E →L[ℂ] E) (S : ℝ → E →L[ℝ] E)
    (hSderiv : ∀ τ : ℝ,
      HasDerivAt S ((A.restrictScalars ℝ).comp (S τ)) τ)
    (hSzero : S 0 = ContinuousLinearMap.id ℝ E)
    (hScomm : ∀ τ : ℝ,
      (S τ).comp (A.restrictScalars ℝ) =
        (A.restrictScalars ℝ).comp (S τ))
    (hSnorm : ∀ τ : ℝ, 0 ≤ τ → ∀ x : E, ‖S τ x‖ ≤ ‖x‖)
    (y g : ℝ → E) (a b : ℝ)
    (hy : LocallyIntegrable y volume) (hg : Integrable g volume)
    (hsupp : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → y t = 0)
    (hweak : IsWeakVectorODE A y g) :
    ∀ᵐ t ∂volume, ‖y t‖ ≤ ∫ s, ‖g s‖ := by
  let κ : ℕ → ℝ → ℝ := fun n => (vectorODEApproxBump n).normed volume
  let Y : ℕ → ℝ → E := fun n =>
    y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ n
  let G : ℕ → ℝ → E := fun n =>
    g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ n
  have hconvLeft := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := vectorODEApproxBump)
    vectorODEApproxBump_rOut_tendsto
    (Eventually.of_forall vectorODEApproxBump_ratio) hy
  have hconv : ∀ᵐ t ∂volume, Tendsto (fun n => Y n t) atTop (𝓝 (y t)) := by
    filter_upwards [hconvLeft] with t ht
    apply ht.congr'
    filter_upwards with n
    dsimp only [Y, κ]
    rw [MeasureTheory.convolution_lsmul_swap,
      MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with s
    rfl
  have hbound (n : ℕ) (t : ℝ) : ‖Y n t‖ ≤ ∫ s, ‖g s‖ := by
    have hκdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (κ n) :=
      (vectorODEApproxBump n).contDiff_normed
    have hκsupp : HasCompactSupport (κ n) :=
      (vectorODEApproxBump n).hasCompactSupport_normed
    have hκint : Integrable (κ n) volume :=
      hκdiff.continuous.integrable_of_hasCompactSupport hκsupp
    have hGint : Integrable (G n) volume := by
      exact hg.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ).flip hκint
    have hGcont : Continuous (G n) := by
      exact hκsupp.continuous_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ).flip hg.locallyIntegrable hκdiff.continuous
    have hYderiv (s : ℝ) : HasDerivAt (Y n)
        ((A.restrictScalars ℝ) (Y n s) + G n s) s := by
      simpa only [Y, G, κ, ContinuousLinearMap.coe_restrictScalars'] using
        hweak.hasDerivAt_convolution A y g hy hg.locallyIntegrable
          (κ n) hκdiff hκsupp s
    let c : ℝ := a - (vectorODEApproxBump n).rOut
    have hYc : Y n c = 0 := by
      dsimp only [Y]
      rw [MeasureTheory.convolution_def]
      apply integral_eq_zero_of_ae
      filter_upwards [hsupp] with s hs
      by_cases hsa : s ∈ Set.Icc a b
      · have hout : c - s ∉ Metric.ball (0 : ℝ)
            (vectorODEApproxBump n).rOut := by
          rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
          have hle : c - s ≤ -(vectorODEApproxBump n).rOut := by
            dsimp [c]
            linarith [hsa.1]
          exact (show (vectorODEApproxBump n).rOut ≤ -(c - s) by linarith).trans
            (neg_le_abs (c - s))
        have hz : κ n (c - s) = 0 := by
          change (vectorODEApproxBump n).normed volume (c - s) = 0
          rw [← notMem_support, (vectorODEApproxBump n).support_normed_eq]
          exact hout
        simp [hz]
      · rw [hs hsa]
        simp
    have hct : c ≤ t ∨ t < c := le_or_gt c t
    rcases hct with hct | htc
    · have hest := vectorODE_forward_estimate
        (A.restrictScalars ℝ) S hSderiv hSzero hScomm hSnorm
        (Y n) (G n) hYderiv hGcont c t hct hYc
      calc
        ‖Y n t‖ ≤ ∫ s in c..t, ‖G n s‖ := hest
        _ ≤ ∫ s, ‖G n s‖ := by
          rw [intervalIntegral.integral_of_le hct]
          exact integral_mono_measure Measure.restrict_le_self
            (Eventually.of_forall fun _ => norm_nonneg _) hGint.norm
        _ ≤ ∫ s, ‖g s‖ := integral_norm_convolution_right_le
          g hg (κ n) hκint (vectorODEApproxBump n).nonneg_normed
          (vectorODEApproxBump n).integral_normed
    · have hzero : Y n t = 0 := by
        dsimp only [Y]
        rw [MeasureTheory.convolution_def]
        apply integral_eq_zero_of_ae
        filter_upwards [hsupp] with s hs
        by_cases hsa : s ∈ Set.Icc a b
        · have hout : t - s ∉ Metric.ball (0 : ℝ)
              (vectorODEApproxBump n).rOut := by
            rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
            have hle : t - s < -(vectorODEApproxBump n).rOut := by
              dsimp [c] at htc
              linarith [hsa.1]
            exact (show (vectorODEApproxBump n).rOut ≤ -(t - s) by linarith).trans
              (neg_le_abs (t - s))
          have hz : κ n (t - s) = 0 := by
            change (vectorODEApproxBump n).normed volume (t - s) = 0
            rw [← notMem_support, (vectorODEApproxBump n).support_normed_eq]
            exact hout
          simp [hz]
        · rw [hs hsa]
          simp
      rw [hzero, norm_zero]
      exact integral_nonneg fun _ => norm_nonneg _
  filter_upwards [hconv] with t ht
  exact le_of_tendsto ht.norm (Eventually.of_forall fun n => hbound n t)

/-- Sharp weak-ODE estimate for a branch whose semigroup is contractive for
negative time increments. -/
theorem weakVectorODE_ae_norm_le_backward
    (A : E →L[ℂ] E) (S : ℝ → E →L[ℝ] E)
    (hSderiv : ∀ τ : ℝ,
      HasDerivAt S ((A.restrictScalars ℝ).comp (S τ)) τ)
    (hSzero : S 0 = ContinuousLinearMap.id ℝ E)
    (hScomm : ∀ τ : ℝ,
      (S τ).comp (A.restrictScalars ℝ) =
        (A.restrictScalars ℝ).comp (S τ))
    (hSnorm : ∀ τ : ℝ, τ ≤ 0 → ∀ x : E, ‖S τ x‖ ≤ ‖x‖)
    (y g : ℝ → E) (a b : ℝ)
    (hy : LocallyIntegrable y volume) (hg : Integrable g volume)
    (hsupp : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → y t = 0)
    (hweak : IsWeakVectorODE A y g) :
    ∀ᵐ t ∂volume, ‖y t‖ ≤ ∫ s, ‖g s‖ := by
  let κ : ℕ → ℝ → ℝ := fun n => (vectorODEApproxBump n).normed volume
  let Y : ℕ → ℝ → E := fun n =>
    y ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ n
  let G : ℕ → ℝ → E := fun n =>
    g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ n
  have hconvLeft := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := vectorODEApproxBump)
    vectorODEApproxBump_rOut_tendsto
    (Eventually.of_forall vectorODEApproxBump_ratio) hy
  have hconv : ∀ᵐ t ∂volume, Tendsto (fun n => Y n t) atTop (𝓝 (y t)) := by
    filter_upwards [hconvLeft] with t ht
    apply ht.congr'
    filter_upwards with n
    dsimp only [Y, κ]
    rw [MeasureTheory.convolution_lsmul_swap,
      MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with s
    rfl
  have hbound (n : ℕ) (t : ℝ) : ‖Y n t‖ ≤ ∫ s, ‖g s‖ := by
    have hκdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (κ n) :=
      (vectorODEApproxBump n).contDiff_normed
    have hκsupp : HasCompactSupport (κ n) :=
      (vectorODEApproxBump n).hasCompactSupport_normed
    have hκint : Integrable (κ n) volume :=
      hκdiff.continuous.integrable_of_hasCompactSupport hκsupp
    have hGint : Integrable (G n) volume :=
      hg.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ).flip hκint
    have hGcont : Continuous (G n) :=
      hκsupp.continuous_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ).flip hg.locallyIntegrable hκdiff.continuous
    have hYderiv (s : ℝ) : HasDerivAt (Y n)
        ((A.restrictScalars ℝ) (Y n s) + G n s) s := by
      simpa only [Y, G, κ, ContinuousLinearMap.coe_restrictScalars'] using
        hweak.hasDerivAt_convolution A y g hy hg.locallyIntegrable
          (κ n) hκdiff hκsupp s
    let c : ℝ := b + (vectorODEApproxBump n).rOut
    have hYc : Y n c = 0 := by
      dsimp only [Y]
      rw [MeasureTheory.convolution_def]
      apply integral_eq_zero_of_ae
      filter_upwards [hsupp] with s hs
      by_cases hsb : s ∈ Set.Icc a b
      · have hout : c - s ∉ Metric.ball (0 : ℝ)
            (vectorODEApproxBump n).rOut := by
          rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
          have hle : (vectorODEApproxBump n).rOut ≤ c - s := by
            dsimp [c]
            linarith [hsb.2]
          exact hle.trans (le_abs_self (c - s))
        have hz : κ n (c - s) = 0 := by
          change (vectorODEApproxBump n).normed volume (c - s) = 0
          rw [← notMem_support, (vectorODEApproxBump n).support_normed_eq]
          exact hout
        simp [hz]
      · rw [hs hsb]
        simp
    rcases le_or_gt t c with htc | hct
    · have hest := vectorODE_backward_estimate
        (A.restrictScalars ℝ) S hSderiv hSzero hScomm hSnorm
        (Y n) (G n) hYderiv hGcont t c htc hYc
      calc
        ‖Y n t‖ ≤ ∫ s in t..c, ‖G n s‖ := hest
        _ ≤ ∫ s, ‖G n s‖ := by
          rw [intervalIntegral.integral_of_le htc]
          exact integral_mono_measure Measure.restrict_le_self
            (Eventually.of_forall fun _ => norm_nonneg _) hGint.norm
        _ ≤ ∫ s, ‖g s‖ := integral_norm_convolution_right_le
          g hg (κ n) hκint (vectorODEApproxBump n).nonneg_normed
          (vectorODEApproxBump n).integral_normed
    · have hzero : Y n t = 0 := by
        dsimp only [Y]
        rw [MeasureTheory.convolution_def]
        apply integral_eq_zero_of_ae
        filter_upwards [hsupp] with s hs
        by_cases hsb : s ∈ Set.Icc a b
        · have hout : t - s ∉ Metric.ball (0 : ℝ)
              (vectorODEApproxBump n).rOut := by
            rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
            have hle : (vectorODEApproxBump n).rOut < t - s := by
              dsimp [c] at hct
              linarith [hsb.2]
            exact hle.le.trans (le_abs_self (t - s))
          have hz : κ n (t - s) = 0 := by
            change (vectorODEApproxBump n).normed volume (t - s) = 0
            rw [← notMem_support, (vectorODEApproxBump n).support_normed_eq]
            exact hout
          simp [hz]
        · rw [hs hsb]
          simp
      rw [hzero, norm_zero]
      exact integral_nonneg fun _ => norm_nonneg _
  filter_upwards [hconv] with t ht
  exact le_of_tendsto ht.norm (Eventually.of_forall fun n => hbound n t)

end CubicNLSPhaseRetrieval
