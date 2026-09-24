import Lean_Code.TwoParticleFree
import Lean_Code.ExteriorLocalData

/-!
# The physical weak exterior equation

This file transports the absolutely-continuous interaction-picture exterior
curve through the two-particle free group.  It supplies the distributional
PDE used by the diagonal jump calculation.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology
open LineDeriv

noncomputable section

set_option maxHeartbeats 5000000

namespace CubicNLSPhaseRetrieval

lemma twoFreeProp_exteriorProductL2 (t : ℝ) (f g : L2) :
    twoFreeProp t (exteriorProductL2 f g) =
      exteriorProductL2 (freeProp t f) (freeProp t g) := by
  unfold exteriorProductL2
  change twoFreeProp t (tensorProductL2 f g - tensorProductL2 g f) =
    tensorProductL2 (freeProp t f) (freeProp t g) -
      tensorProductL2 (freeProp t g) (freeProp t f)
  rw [twoFreeProp_sub, twoFreeProp_tensor, twoFreeProp_tensor]

lemma interactionExterior_eq_twoFreeProp (t : ℝ) (f g : L2) :
    exteriorProductL2 (freeProp (-t) f) (freeProp (-t) g) =
      twoFreeProp (-t) (exteriorProductL2 f g) := by
  exact (twoFreeProp_exteriorProductL2 (-t) f g).symm

/-- The bundled exterior product has the expected scalar distribution
pairing against a Schwartz test. -/
theorem bilinearL2Two_exteriorProductL2 (u v : ℝ → L2) (t : ℝ)
    (q : SchwartzMap (ℝ × ℝ) ℂ) :
    bilinearL2Two (exteriorProductL2 (u t) (v t))
        (q.toLp 2 (volume.prod volume)) =
      ∫ z : ℝ × ℝ, exteriorProduct u v (t, z) * q z
        ∂(volume.prod volume) := by
  rw [bilinearL2Two_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_exteriorProductL2 (u t) (v t),
    q.coeFn_toLp 2 (volume.prod volume)] with z hF hq
  rw [hF, hq]
  rfl

/-- The measurable scalar source represents the bundled source curve in
every separated spatial pairing, for almost every time. -/
theorem bilinearL2Two_exteriorSourceCurve_ae (sigma : ℝ)
    (u v : GlobalSolution sigma) (q : SchwartzMap (ℝ × ℝ) ℂ) :
    ∀ᵐ t : ℝ ∂volume,
      bilinearL2Two (exteriorSourceCurve sigma u v t)
          (q.toLp 2 (volume.prod volume)) =
        ∫ z : ℝ × ℝ, measurableExteriorSource sigma u v (t, z) * q z
          ∂(volume.prod volume) := by
  filter_upwards [measurableExteriorSource_slice sigma u v] with t ht
  rw [bilinearL2Two_eq_integral]
  apply integral_congr_ae
  filter_upwards [ht, q.coeFn_toLp 2 (volume.prod volume)] with z hS hq
  rw [hS, hq]

private lemma twoFreeProp_exteriorSourceCurve (sigma : ℝ)
    (u v : GlobalSolution sigma) (t : ℝ) :
    twoFreeProp (-t) (exteriorSourceCurve sigma u v t) =
      (sigma : ℂ) •
        ((tensorProductL2 (freeProp (-t) (u.nonlin t))
              (freeProp (-t) (v.u t)) +
            tensorProductL2 (freeProp (-t) (u.u t))
              (freeProp (-t) (v.nonlin t))) -
          tensorProductL2 (freeProp (-t) (v.nonlin t))
              (freeProp (-t) (u.u t)) -
          tensorProductL2 (freeProp (-t) (v.u t))
              (freeProp (-t) (u.nonlin t))) := by
  unfold exteriorSourceCurve
  rw [twoFreeProp_smul, twoFreeProp_sub, twoFreeProp_sub,
    twoFreeProp_add, twoFreeProp_tensor, twoFreeProp_tensor,
    twoFreeProp_tensor, twoFreeProp_tensor]

/-- The interaction exterior derivative is the inverse free transport of the
physical nonlinear source. -/
theorem interaction_exterior_ae_hasDerivAt_source (sigma : ℝ)
    (u v : GlobalSolution sigma) (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt
        (fun s => twoFreeProp (-s) (exteriorProductL2 (u.u s) (v.u s)))
        (-Complex.I • twoFreeProp (-t) (exteriorSourceCurve sigma u v t)) t := by
  filter_upwards [interaction_exterior_ae_hasDerivAt sigma u v a b]
      with t ht hmem
  have h := ht hmem
  have hcurve :
      (fun s => exteriorProductL2 (freeProp (-s) (u.u s))
        (freeProp (-s) (v.u s))) =
      (fun s => twoFreeProp (-s) (exteriorProductL2 (u.u s) (v.u s))) := by
    funext s
    exact interactionExterior_eq_twoFreeProp s (u.u s) (v.u s)
  rw [hcurve] at h
  convert h using 1
  rw [twoFreeProp_exteriorSourceCurve]
  simp only [smul_sub, smul_add, smul_smul]
  simp only [tensorProductRealCLM_eq_tensorProductL2,
    tensorProductL2_smul_left, tensorProductL2_smul_right]
  module

/-! ## The transpose free flow for the bilinear distribution pairing -/

/-- The pair Fourier transform is self-transpose for the complex-bilinear
`L²` pairing. -/
theorem bilinearL2Two_fourier_self (f g : TwoParticleL2) :
    bilinearL2Two (fourierL2Two f) g =
      bilinearL2Two f (fourierL2Two g) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := ℂ)
    (E := ℝ × ℝ) (p := (2 : ℝ≥0∞))
      (μ := volume.prod volume) (by norm_num)
  have hfun : (fun h : TwoParticleL2 =>
      bilinearL2Two (fourierL2Two f) h) =
      (fun h : TwoParticleL2 => bilinearL2Two f (fourierL2Two h)) := by
    apply hdense.equalizer
    · exact (bilinearL2TwoCLM (fourierL2Two f)).continuous
    · exact (bilinearL2TwoCLM f).continuous.comp fourierL2Two.continuous
    · funext q
      change bilinearL2Two (fourierL2Two f)
          (q.toLp 2 (volume.prod volume)) =
        bilinearL2Two f
          (fourierL2Two (q.toLp 2 (volume.prod volume)))
      rw [bilinearL2Two_fourier_left, fourierL2Two_toLp]
  exact congrFun hfun g

/-- The inverse pair Fourier transform is likewise self-transpose. -/
theorem bilinearL2Two_fourierInv_self (f g : TwoParticleL2) :
    bilinearL2Two (fourierL2Two.symm f) g =
      bilinearL2Two f (fourierL2Two.symm g) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := ℂ)
    (E := ℝ × ℝ) (p := (2 : ℝ≥0∞))
      (μ := volume.prod volume) (by norm_num)
  have hfun : (fun h : TwoParticleL2 =>
      bilinearL2Two (fourierL2Two.symm f) h) =
      (fun h : TwoParticleL2 => bilinearL2Two f (fourierL2Two.symm h)) := by
    apply hdense.equalizer
    · exact (bilinearL2TwoCLM (fourierL2Two.symm f)).continuous
    · exact (bilinearL2TwoCLM f).continuous.comp fourierL2Two.symm.continuous
    · funext q
      change bilinearL2Two (fourierL2Two.symm f)
          (q.toLp 2 (volume.prod volume)) =
        bilinearL2Two f
          (fourierL2Two.symm (q.toLp 2 (volume.prod volume)))
      rw [fourierL2Two_symm_toLp]
      exact (bilinearL2Two_fourierInv_right f q).symm
  exact congrFun hfun g

private theorem bilinearL2Two_twoMultSymbol_self
    (t : ℝ) (f g : TwoParticleL2) :
    bilinearL2Two (twoMultSymbol t f) g =
      bilinearL2Two f (twoMultSymbol t g) := by
  rw [bilinearL2Two_eq_integral, bilinearL2Two_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_twoMultSymbol t f, coe_twoMultSymbol t g]
      with xi hf hg
  rw [hf, hg]
  ring

/-- The transpose of the physical free flow with respect to `∫ f g`. -/
def twoFreeTranspose (t : ℝ) (q : TwoParticleL2) : TwoParticleL2 :=
  fourierL2Two (twoMultSymbol t (fourierL2Two.symm q))

private lemma twoFreeTranspose_add (t : ℝ) (q r : TwoParticleL2) :
    twoFreeTranspose t (q + r) =
      twoFreeTranspose t q + twoFreeTranspose t r := by
  unfold twoFreeTranspose
  rw [map_add, twoMultSymbol_add, map_add]

private lemma twoFreeTranspose_smul (c : ℂ) (t : ℝ) (q : TwoParticleL2) :
    twoFreeTranspose t (c • q) = c • twoFreeTranspose t q := by
  unfold twoFreeTranspose
  rw [map_smul, twoMultSymbol_smul, map_smul]

private lemma twoFreeTranspose_real_smul (c : ℝ) (t : ℝ)
    (q : TwoParticleL2) :
    twoFreeTranspose t (c • q) = c • twoFreeTranspose t q := by
  change twoFreeTranspose t ((c : ℂ) • q) =
    (c : ℂ) • twoFreeTranspose t q
  exact twoFreeTranspose_smul (c : ℂ) t q

private lemma twoFreeTranspose_sub (t : ℝ) (q r : TwoParticleL2) :
    twoFreeTranspose t (q - r) =
      twoFreeTranspose t q - twoFreeTranspose t r := by
  rw [sub_eq_add_neg, sub_eq_add_neg, twoFreeTranspose_add]
  rw [show -r = (-1 : ℂ) • r by simp, twoFreeTranspose_smul]
  simp

private lemma norm_twoFreeTranspose (t : ℝ) (q : TwoParticleL2) :
    ‖twoFreeTranspose t q‖ = ‖q‖ := by
  unfold twoFreeTranspose
  rw [LinearIsometryEquiv.norm_map, norm_twoMultSymbol,
    LinearIsometryEquiv.norm_map]

private theorem continuous_twoMultSymbol_joint :
    Continuous (fun p : ℝ × TwoParticleL2 => twoMultSymbol p.1 p.2) := by
  have hinside : Continuous (fun p : ℝ × TwoParticleL2 =>
      (p.1, fourierL2Two.symm p.2)) :=
    continuous_fst.prodMk (fourierL2Two.symm.continuous.comp continuous_snd)
  have hfree := continuous_twoFreeProp_joint.comp hinside
  have hfourier := fourierL2Two.continuous.comp hfree
  convert hfourier using 1
  funext p
  simp [Function.comp_apply, twoFreeProp]

private theorem continuous_twoFreeTranspose_joint :
    Continuous (fun p : ℝ × TwoParticleL2 => twoFreeTranspose p.1 p.2) := by
  unfold twoFreeTranspose
  exact fourierL2Two.continuous.comp
    (continuous_twoMultSymbol_joint.comp
      (continuous_fst.prodMk
        (fourierL2Two.symm.continuous.comp continuous_snd)))

theorem bilinearL2Two_twoFreeProp_transpose
    (t : ℝ) (f q : TwoParticleL2) :
    bilinearL2Two (twoFreeProp t f) q =
      bilinearL2Two f (twoFreeTranspose t q) := by
  unfold twoFreeProp twoFreeTranspose
  rw [bilinearL2Two_fourierInv_self,
    bilinearL2Two_twoMultSymbol_self,
    bilinearL2Two_fourier_self]

private theorem bilinearL2Two_transport_cancel
    (t : ℝ) (f q : TwoParticleL2) :
    bilinearL2Two (twoFreeProp (-t) f) (twoFreeTranspose t q) =
      bilinearL2Two f q := by
  rw [← bilinearL2Two_twoFreeProp_transpose t (twoFreeProp (-t) f) q,
    twoFreeProp_group]
  simpa using congrArg (fun z => bilinearL2Two z q) (twoFreeProp_zero f)

private theorem pairSchwartzFourierInv_laplacian_apply
    (q : SchwartzMap (ℝ × ℝ) ℂ) (xi : ℝ × ℝ) :
    pairSchwartzFourierInv (pairLaplacian q) xi =
      ((-(4 * Real.pi ^ 2 * (xi.1 ^ 2 + xi.2 ^ 2)) : ℝ) : ℂ) *
        pairSchwartzFourierInv q xi := by
  unfold pairLaplacian
  rw [pairSchwartzFourierInv_add,
    pairSchwartzFourierInv_pairPartial0,
    pairSchwartzFourierInv_pairPartial0,
    pairSchwartzFourierInv_pairPartial1,
    pairSchwartzFourierInv_pairPartial1]
  simp only [add_apply]
  rw [pairFrequencyDeriv0_apply, pairFrequencyDeriv0_apply,
    pairFrequencyDeriv1_apply, pairFrequencyDeriv1_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma inverseSchwartz_twoGenerator_memLp
    (q : SchwartzMap (ℝ × ℝ) ℂ) :
    MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi *
        (fourierL2Two.symm (q.toLp 2 (volume.prod volume)) :
          ℝ × ℝ → ℂ) xi) 2 (volume.prod volume) := by
  let qinv := pairSchwartzFourierInv q
  let w := pairFrequencyConjugatedAdjoint 0 qinv
  have hw : MemLp (w : ℝ × ℝ → ℂ) 2 (volume.prod volume) :=
    w.memLp 2 (volume.prod volume)
  have hraw : MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi * qinv xi) 2
      (volume.prod volume) := by
    refine hw.congr_norm
      (continuous_twoSchrodingerGenerator.aestronglyMeasurable.mul
        qinv.continuous.aestronglyMeasurable) ?_
    filter_upwards with xi
    rw [pairFrequencyConjugatedAdjoint_apply]
    dsimp [w, qinv, twoSchrodingerGenerator, twoSchrodingerFrequency]
    norm_num
  refine hraw.congr_norm
    (continuous_twoSchrodingerGenerator.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable
        (fourierL2Two.symm (q.toLp 2 (volume.prod volume))))) ?_
  have hcoe :
      (fourierL2Two.symm (q.toLp 2 (volume.prod volume)) :
        ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
        fun xi => qinv xi := by
    rw [fourierL2Two_symm_toLp]
    exact qinv.coeFn_toLp 2 (volume.prod volume)
  filter_upwards [hcoe] with xi hxi
  rw [hxi]

/-- The transpose free orbit has the expected physical derivative. -/
theorem twoFreeTranspose_schwartz_derivative
    (q : SchwartzMap (ℝ × ℝ) ℂ) (t : ℝ) :
    HasDerivAt
      (fun s => twoFreeTranspose s (q.toLp 2 (volume.prod volume)))
      (Complex.I • twoFreeTranspose t
        ((pairLaplacian q).toLp 2 (volume.prod volume))) t := by
  let g : TwoParticleL2 :=
    fourierL2Two.symm (q.toLp 2 (volume.prod volume))
  let dq : ℝ × ℝ → ℂ := fun xi =>
    twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi *
      (g : ℝ × ℝ → ℂ) xi
  have hgen : MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi * (g : ℝ × ℝ → ℂ) xi) 2
      (volume.prod volume) := inverseSchwartz_twoGenerator_memLp q
  have hdq : MemLp dq 2 (volume.prod volume) :=
    twoGenerator_symbol_mul_memLp g hgen t
  have hm : HasDerivAt (fun s => twoMultSymbol s g) (hdq.toLp dq) t := by
    simpa [dq] using hasDerivAt_twoMultSymbol g hgen t
  let U : TwoParticleL2 →L[ℝ] TwoParticleL2 :=
    (fourierL2Two.toContinuousLinearEquiv.restrictScalars ℝ).toContinuousLinearMap
  have hcomp := U.hasFDerivAt.comp_hasDerivAt t hm
  have horbit : HasDerivAt
      (fun s => twoFreeTranspose s (q.toLp 2 (volume.prod volume)))
      (fourierL2Two (hdq.toLp dq)) t := by
    simpa [twoFreeTranspose, g, U, Function.comp_def] using hcomp
  have htarget : fourierL2Two (hdq.toLp dq) =
      Complex.I • twoFreeTranspose t
        ((pairLaplacian q).toLp 2 (volume.prod volume)) := by
    apply fourierL2Two.symm.injective
    rw [LinearIsometryEquiv.symm_apply_apply, map_smul]
    unfold twoFreeTranspose
    rw [LinearIsometryEquiv.symm_apply_apply]
    apply Lp.ext
    have hq :
        (fourierL2Two.symm (q.toLp 2 (volume.prod volume)) :
          ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
          fun z => pairSchwartzFourierInv q z := by
      rw [fourierL2Two_symm_toLp]
      exact (pairSchwartzFourierInv q).coeFn_toLp 2 (volume.prod volume)
    have hlapq :
        (fourierL2Two.symm
            ((pairLaplacian q).toLp 2 (volume.prod volume)) :
          ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
          fun z => pairSchwartzFourierInv (pairLaplacian q) z := by
      rw [fourierL2Two_symm_toLp]
      exact (pairSchwartzFourierInv (pairLaplacian q)).coeFn_toLp 2
        (volume.prod volume)
    filter_upwards [hdq.coeFn_toLp,
      Lp.coeFn_smul Complex.I
        (twoMultSymbol t (fourierL2Two.symm
          ((pairLaplacian q).toLp 2 (volume.prod volume)))),
      coe_twoMultSymbol t (fourierL2Two.symm
        ((pairLaplacian q).toLp 2 (volume.prod volume))),
      hlapq, hq] with xi hd hsmul hmult hlap hqxi
    rw [hd, hsmul]
    simp only [Pi.smul_apply]
    rw [hmult, hlap, pairSchwartzFourierInv_laplacian_apply]
    dsimp [dq, g]
    rw [hqxi]
    unfold twoSchrodingerGenerator twoSchrodingerFrequency
    push_cast
    ring
  rw [htarget] at horbit
  exact horbit

/-! ## The physical weak identity for separated tests -/

private noncomputable def bilinearL2TwoRealLinear :
    TwoParticleL2 →ₗ[ℝ] TwoParticleL2 →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ bilinearL2Two
    (fun f₁ f₂ q => by rw [bilinearL2Two_add_left])
    (fun c f q => by
      change bilinearL2Two ((c : ℂ) • f) q =
        (c : ℂ) • bilinearL2Two f q
      rw [bilinearL2Two_smul_left]
      rfl)
    (fun f q₁ q₂ => by rw [bilinearL2Two_add_right])
    (fun c f q => by
      change bilinearL2Two f ((c : ℂ) • q) =
        (c : ℂ) • bilinearL2Two f q
      rw [bilinearL2Two_smul_right]
      rfl)

private noncomputable def bilinearL2TwoRealCLM :
    TwoParticleL2 →L[ℝ] TwoParticleL2 →L[ℝ] ℂ :=
  bilinearL2TwoRealLinear.mkContinuous₂ 1 (fun f q => by
    change ‖bilinearL2Two f q‖ ≤ 1 * ‖f‖ * ‖q‖
    simpa only [one_mul] using norm_bilinearL2Two_le f q)

@[simp] private theorem bilinearL2TwoRealCLM_apply
    (f q : TwoParticleL2) :
    bilinearL2TwoRealCLM f q = bilinearL2Two f q := rfl

private theorem contDiff_twoFreeTranspose_schwartz
    (q : SchwartzMap (ℝ × ℝ) ℂ) :
    ContDiff ℝ 1
      (fun t => twoFreeTranspose t (q.toLp 2 (volume.prod volume))) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (twoFreeTranspose_schwartz_derivative q t).differentiableAt,
    ?_⟩
  have hderiv (t : ℝ) :
      deriv (fun s => twoFreeTranspose s
        (q.toLp 2 (volume.prod volume))) t =
        Complex.I • twoFreeTranspose t
          ((pairLaplacian q).toLp 2 (volume.prod volume)) :=
    (twoFreeTranspose_schwartz_derivative q t).deriv
  rw [show deriv (fun s => twoFreeTranspose s
      (q.toLp 2 (volume.prod volume))) =
      fun t => Complex.I • twoFreeTranspose t
        ((pairLaplacian q).toLp 2 (volume.prod volume)) by
    funext t
    exact hderiv t]
  have hc : Continuous (fun t : ℝ =>
      twoFreeTranspose t
        ((pairLaplacian q).toLp 2 (volume.prod volume))) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (twoFreeTranspose_schwartz_derivative (pairLaplacian q) t).continuousAt
  exact (continuous_const : Continuous (fun _ : ℝ => Complex.I)).smul hc

private theorem separatedTranspose_contDiff
    (eta : SchwartzMap ℝ ℂ) (q : SchwartzMap (ℝ × ℝ) ℂ) :
    ContDiff ℝ 1 (fun t =>
      eta t • twoFreeTranspose t (q.toLp 2 (volume.prod volume))) := by
  exact (eta.smooth 1).smul
    (contDiff_twoFreeTranspose_schwartz q)

private theorem separatedTranspose_derivative
    (eta : SchwartzMap ℝ ℂ) (q : SchwartzMap (ℝ × ℝ) ℂ) (t : ℝ) :
    HasDerivAt
      ((eta : ℝ → ℂ) • fun s =>
        twoFreeTranspose s (q.toLp 2 (volume.prod volume)))
      (eta t • Complex.I • twoFreeTranspose t
          ((pairLaplacian q).toLp 2 (volume.prod volume)) +
        deriv (eta : ℝ → ℂ) t •
          twoFreeTranspose t (q.toLp 2 (volume.prod volume))) t := by
  exact eta.differentiableAt.hasDerivAt.smul
    (twoFreeTranspose_schwartz_derivative q t)

/-! ## Compact spacetime tests as differentiable `L²` sections -/

/-- Restrict a spacetime Schwartz function to one time slice. -/
private def spacetimeTestSection
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (t : ℝ) : 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun z : ℝ × ℝ => (t, z)) (by
    let L : (ℝ × ℝ) →L[ℝ] ℝ × (ℝ × ℝ) :=
      (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (ℝ × ℝ))
    have hL := L.hasTemperateGrowth.add
      (show Function.HasTemperateGrowth
          (fun _ : ℝ × ℝ => (t, (0, 0))) by fun_prop)
    convert hL using 1 <;> ext z <;> simp [L]) (by
    refine ⟨1, 1, fun z => ?_⟩
    simp only [Real.norm_eq_abs, pow_one, one_mul, Prod.norm_def]
    calc
      max |z.1| |z.2| ≤ max |t| (max |z.1| |z.2|) := le_max_right _ _
      _ ≤ 1 + max |t| (max |z.1| |z.2|) :=
        le_add_of_nonneg_left (by norm_num)) Psi

@[simp] private lemma spacetimeTestSection_apply
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (t : ℝ) (z : ℝ × ℝ) :
    spacetimeTestSection Psi t z = Psi (t, z) := rfl

private def spacetimeTimePartial (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  ∂_{((1, (0, 0)) : ℝ × (ℝ × ℝ))} Psi

private def spacetimePartial0 (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  ∂_{((0, (1, 0)) : ℝ × (ℝ × ℝ))} Psi

private def spacetimePartial1 (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  ∂_{((0, (0, 1)) : ℝ × (ℝ × ℝ))} Psi

private def spacetimeSpatialLaplacian (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  spacetimePartial0 (spacetimePartial0 Psi) +
    spacetimePartial1 (spacetimePartial1 Psi)

private lemma lineDeriv_hasCompactSupport
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ))
    (m : ℝ × (ℝ × ℝ)) :
    HasCompactSupport
      (((∂_{m} Psi : SchwartzMap (ℝ × (ℝ × ℝ)) ℂ)) :
        ℝ × (ℝ × ℝ) → ℂ) := by
  exact hPsi.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (SchwartzMap.tsupport_lineDerivOp_subset m Psi)

private lemma spacetimeTimePartial_hasCompactSupport
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport (spacetimeTimePartial Psi : ℝ × (ℝ × ℝ) → ℂ) :=
  lineDeriv_hasCompactSupport Psi hPsi _

private lemma spacetimeSpatialLaplacian_hasCompactSupport
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport
      (spacetimeSpatialLaplacian Psi : ℝ × (ℝ × ℝ) → ℂ) := by
  have hx := lineDeriv_hasCompactSupport Psi hPsi
    ((0, (1, 0)) : ℝ × (ℝ × ℝ))
  have hxx := lineDeriv_hasCompactSupport (spacetimePartial0 Psi) hx
    ((0, (1, 0)) : ℝ × (ℝ × ℝ))
  have hy := lineDeriv_hasCompactSupport Psi hPsi
    ((0, (0, 1)) : ℝ × (ℝ × ℝ))
  have hyy := lineDeriv_hasCompactSupport (spacetimePartial1 Psi) hy
    ((0, (0, 1)) : ℝ × (ℝ × ℝ))
  exact hxx.add hyy

private lemma deriv_spacetimeTestSection
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (t : ℝ) (z : ℝ × ℝ) :
    deriv (fun s : ℝ => Psi (s, z)) t = spacetimeTimePartial Psi (t, z) := by
  have hg : HasDerivAt (fun s : ℝ => (s, z))
      ((1, (0, 0)) : ℝ × (ℝ × ℝ)) t := by
    convert (hasDerivAt_id t).prodMk (hasDerivAt_const t z) using 1 <;> simp
  have hc := (Psi.hasFDerivAt (t, z)).comp_hasDerivAt t hg
  change deriv ((Psi : ℝ × (ℝ × ℝ) → ℂ) ∘ fun s : ℝ => (s, z)) t = _
  rw [hc.deriv]
  simp only [spacetimeTimePartial, SchwartzMap.lineDerivOp_apply_eq_fderiv]

private lemma spacetimeTestSection_spatialLaplacian
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (t : ℝ) :
    spacetimeTestSection (spacetimeSpatialLaplacian Psi) t =
      pairLaplacian (spacetimeTestSection Psi t) := by
  ext z
  rcases z with ⟨x, y⟩
  simp only [spacetimeTestSection_apply, spacetimeSpatialLaplacian,
    spacetimePartial0, spacetimePartial1, add_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, pairLaplacian,
    pairPartial0_apply, pairPartial1_apply]
  have hx (Phi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
      deriv (fun r : ℝ => Phi (t, (r, y))) x =
        fderiv ℝ (Phi : ℝ × (ℝ × ℝ) → ℂ) (t, (x, y))
          ((0, (1, 0)) : ℝ × (ℝ × ℝ)) := by
    have hg : HasDerivAt (fun r : ℝ => (t, (r, y)))
        ((0, (1, 0)) : ℝ × (ℝ × ℝ)) x := by
      simpa only [id_eq] using (hasDerivAt_const x t).prodMk
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    exact ((Phi.hasFDerivAt (t, (x, y))).comp_hasDerivAt x hg).deriv
  have hy (Phi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
      deriv (fun r : ℝ => Phi (t, (x, r))) y =
        fderiv ℝ (Phi : ℝ × (ℝ × ℝ) → ℂ) (t, (x, y))
          ((0, (0, 1)) : ℝ × (ℝ × ℝ)) := by
    have hg : HasDerivAt (fun r : ℝ => (t, (x, r)))
        ((0, (0, 1)) : ℝ × (ℝ × ℝ)) y := by
      simpa only [id_eq] using (hasDerivAt_const y t).prodMk
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    exact ((Phi.hasFDerivAt (t, (x, y))).comp_hasDerivAt y hg).deriv
  have hxall (r : ℝ) :
      deriv (fun q : ℝ => Psi (t, (q, y))) r =
        fderiv ℝ (Psi : ℝ × (ℝ × ℝ) → ℂ) (t, (r, y))
          ((0, (1, 0)) : ℝ × (ℝ × ℝ)) := by
    have hg : HasDerivAt (fun q : ℝ => (t, (q, y)))
        ((0, (1, 0)) : ℝ × (ℝ × ℝ)) r := by
      simpa only [id_eq] using (hasDerivAt_const r t).prodMk
        ((hasDerivAt_id r).prodMk (hasDerivAt_const r y))
    exact ((Psi.hasFDerivAt (t, (r, y))).comp_hasDerivAt r hg).deriv
  have hyall (r : ℝ) :
      deriv (fun q : ℝ => Psi (t, (x, q))) r =
        fderiv ℝ (Psi : ℝ × (ℝ × ℝ) → ℂ) (t, (x, r))
          ((0, (0, 1)) : ℝ × (ℝ × ℝ)) := by
    have hg : HasDerivAt (fun q : ℝ => (t, (x, q)))
        ((0, (0, 1)) : ℝ × (ℝ × ℝ)) r := by
      simpa only [id_eq] using (hasDerivAt_const r t).prodMk
        ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
    exact ((Psi.hasFDerivAt (t, (x, r))).comp_hasDerivAt r hg).deriv
  change fderiv ℝ (spacetimePartial0 Psi : ℝ × (ℝ × ℝ) → ℂ)
      (t, (x, y)) (0, (1, 0)) +
    fderiv ℝ (spacetimePartial1 Psi : ℝ × (ℝ × ℝ) → ℂ)
      (t, (x, y)) (0, (0, 1)) = _
  rw [← hx (spacetimePartial0 Psi), ← hy (spacetimePartial1 Psi)]
  congr 1
  · congr 1
    funext r
    simpa [spacetimePartial0,
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using (hxall r).symm
  · congr 1
    funext r
    simpa [spacetimePartial1,
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using (hyall r).symm

/-- A compactly supported smooth spacetime test is a differentiable curve of
spatial `L²` tests.  This is the arbitrary-test replacement for a general
tensor-product density theorem. -/
private theorem spacetimeTestSection_hasDerivAt_toLp
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ)) (t0 : ℝ) :
    HasDerivAt
      (fun t => (spacetimeTestSection Psi t).toLp 2 (volume.prod volume))
      ((spacetimeTestSection (spacetimeTimePartial Psi) t0).toLp 2
        (volume.prod volume)) t0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let q : ℝ → TwoParticleL2 := fun t =>
    (spacetimeTestSection Psi t).toLp 2 (volume.prod volume)
  let qdot : TwoParticleL2 :=
    (spacetimeTestSection (spacetimeTimePartial Psi) t0).toLp 2
      (volume.prod volume)
  let raw : ℝ → (ℝ × ℝ) → ℂ := fun h z =>
    ((h : ℂ)⁻¹) * (Psi (t0 + h, z) - Psi (t0, z)) -
      spacetimeTimePartial Psi (t0, z)
  have hraw (h : ℝ) (hh : h ≠ 0) :
      eLpNorm ((((↑h)⁻¹ • (q (t0 + h) - q t0) - qdot :
        TwoParticleL2) : ℝ × ℝ → ℂ)) 2 (volume.prod volume) =
        eLpNorm (raw h) 2 (volume.prod volume) := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_smul (↑h)⁻¹ (q (t0 + h) - q t0),
      Lp.coeFn_sub (q (t0 + h)) (q t0),
      (spacetimeTestSection Psi (t0 + h)).coeFn_toLp 2 (volume.prod volume),
      (spacetimeTestSection Psi t0).coeFn_toLp 2 (volume.prod volume),
      Lp.coeFn_sub ((↑h)⁻¹ • (q (t0 + h) - q t0)) qdot,
      (spacetimeTestSection (spacetimeTimePartial Psi) t0).coeFn_toLp 2
        (volume.prod volume)] with z hsmul hsub h1 h0 hout hdot
    rw [hout]
    simp only [Pi.sub_apply]
    rw [hsmul]
    simp only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [h1, h0, hdot]
    simp only [spacetimeTestSection_apply]
    dsimp only [raw]
    exact congrArg (fun c : ℂ =>
      c * (Psi (t0 + h, z) - Psi (t0, z)) -
        spacetimeTimePartial Psi (t0, z)) (Complex.ofReal_inv h)
  obtain ⟨R, hR⟩ :=
    hPsi.isCompact.isBounded.subset_closedBall (0 : ℝ × (ℝ × ℝ))
  let C : ℝ := SchwartzMap.seminorm ℂ 0 1 Psi
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hderiv_bound (s : ℝ) (z : ℝ × ℝ) :
      ‖deriv (fun r : ℝ => Psi (r, z)) s‖ ≤ C := by
    rw [deriv_spacetimeTestSection]
    dsimp only [spacetimeTimePartial, C]
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    calc
      ‖fderiv ℝ (Psi : ℝ × (ℝ × ℝ) → ℂ) (s, z)
          ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖ ≤
          ‖fderiv ℝ (Psi : ℝ × (ℝ × ℝ) → ℂ) (s, z)‖ := by
        simpa [Prod.norm_def] using ContinuousLinearMap.le_opNorm
          (fderiv ℝ (Psi : ℝ × (ℝ × ℝ) → ℂ) (s, z))
          ((1, (0, 0)) : ℝ × (ℝ × ℝ))
      _ ≤ SchwartzMap.seminorm ℂ 0 1 Psi := by
        simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ Psi 1 (s, z)
  have hslope_bound (h : ℝ) (hh : h ≠ 0) (z : ℝ × ℝ) :
      ‖((h : ℂ)⁻¹) * (Psi (t0 + h, z) - Psi (t0, z))‖ ≤ C := by
    have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun s _ => Psi.differentiableAt.comp s
        (differentiableAt_id.prodMk (differentiableAt_const (c := z))))
      (fun s _ => hderiv_bound s z) (Set.mem_univ t0)
      (Set.mem_univ (t0 + h))
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have hmvt' : ‖Psi (t0 + h, z) - Psi (t0, z)‖ ≤ C * |h| := by
      simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
        show t0 + h - t0 = h by ring] using hmvt
    calc
      |h|⁻¹ * ‖Psi (t0 + h, z) - Psi (t0, z)‖ ≤
          |h|⁻¹ * (C * |h|) :=
        mul_le_mul_of_nonneg_left hmvt' (inv_nonneg.mpr (abs_nonneg h))
      _ = C := by field_simp [abs_ne_zero.mpr hh]
  have hdot_bound (z : ℝ × ℝ) :
      ‖spacetimeTimePartial Psi (t0, z)‖ ≤ C := by
    simpa [deriv_spacetimeTestSection] using hderiv_bound t0 z
  have hraw_bound (h : ℝ) (hh : h ≠ 0) (z : ℝ × ℝ) :
      ‖raw h z‖ ≤ 2 * C := by
    dsimp only [raw]
    calc
      _ ≤ ‖((h : ℂ)⁻¹) * (Psi (t0 + h, z) - Psi (t0, z))‖ +
          ‖spacetimeTimePartial Psi (t0, z)‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hslope_bound h hh z) (hdot_bound z)
      _ = 2 * C := by ring
  have hzero_out (h : ℝ) (z : ℝ × ℝ)
      (hz : z ∉ Metric.closedBall (0 : ℝ × ℝ) R) : raw h z = 0 := by
    have hzfull (s : ℝ) : (s, z) ∉ tsupport (Psi : ℝ × (ℝ × ℝ) → ℂ) := by
      intro hs
      have hsR := hR hs
      have hzle : ‖z‖ ≤ ‖(s, z)‖ := by simp [Prod.norm_def]
      have hzr : ‖z‖ ≤ R := hzle.trans (by
        simpa [Metric.mem_closedBall, dist_zero_right] using hsR)
      exact hz (by simpa [Metric.mem_closedBall, dist_zero_right] using hzr)
    have h1 : Psi (t0 + h, z) = 0 := by
      by_contra hn
      exact hzfull (t0 + h) (subset_tsupport _ hn)
    have h0 : Psi (t0, z) = 0 := by
      by_contra hn
      exact hzfull t0 (subset_tsupport _ hn)
    have hd : spacetimeTimePartial Psi (t0, z) = 0 := by
      by_contra hn
      have hs := SchwartzMap.tsupport_lineDerivOp_subset
        ((1, (0, 0)) : ℝ × (ℝ × ℝ)) Psi (subset_tsupport _ hn)
      exact hzfull t0 hs
    simp [raw, h1, h0, hd]
  let bound : (ℝ × ℝ) → ℝ≥0∞ :=
    (Metric.closedBall (0 : ℝ × ℝ) R).indicator
      (fun _ => ENNReal.ofReal (2 * C) ^ (2 : ℝ))
  have hbound_fin : (∫⁻ z, bound z ∂(volume.prod volume)) ≠ ⊤ := by
    rw [show bound = (Metric.closedBall (0 : ℝ × ℝ) R).indicator
        (fun _ => ENNReal.ofReal (2 * C) ^ (2 : ℝ)) by rfl,
      lintegral_indicator Metric.isClosed_closedBall.measurableSet,
      setLIntegral_const]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      (measure_closedBall_lt_top.ne)
  have hmeas (h : ℝ) : AEMeasurable
      (fun z => ‖raw h z‖ₑ ^ (2 : ℝ)) (volume.prod volume) := by
    exact (((((Psi.continuous.comp
      ((continuous_const : Continuous (fun _ : ℝ × ℝ => t0 + h)).prodMk
        continuous_id)).aestronglyMeasurable.sub
      (Psi.continuous.comp
        ((continuous_const : Continuous (fun _ : ℝ × ℝ => t0)).prodMk
          continuous_id)).aestronglyMeasurable).const_mul
          ((h : ℂ)⁻¹)).sub
      ((spacetimeTimePartial Psi).continuous.comp
        ((continuous_const : Continuous (fun _ : ℝ × ℝ => t0)).prodMk
          continuous_id)).aestronglyMeasurable).enorm.pow_const 2)
  have hdom (h : ℝ) (hh : h ≠ 0) :
      ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
        ‖raw h z‖ₑ ^ (2 : ℝ) ≤ bound z := by
    filter_upwards with z
    by_cases hz : z ∈ Metric.closedBall (0 : ℝ × ℝ) R
    · simp only [bound, Set.indicator_of_mem hz]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hraw_bound h hh z)
    · simp [bound, hz, hzero_out h z hz]
  have hpoint (z : ℝ × ℝ) : Tendsto
      (fun h => ‖raw h z‖ₑ ^ (2 : ℝ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hd : HasDerivAt (fun s : ℝ => Psi (s, z))
        (spacetimeTimePartial Psi (t0, z)) t0 := by
      rw [← deriv_spacetimeTestSection Psi t0 z]
      exact (Psi.differentiableAt.comp t0
        (differentiableAt_id.prodMk
          (differentiableAt_const (c := z)))).hasDerivAt
    have hs : Tendsto
        (fun h : ℝ => ((h : ℝ)⁻¹ : ℝ) •
          (Psi (t0 + h, z) - Psi (t0, z)))
        (nhdsWithin 0 {0}ᶜ)
        (nhds (spacetimeTimePartial Psi (t0, z))) := by
      exact hasDerivAt_iff_tendsto_slope_zero.mp hd
    have hs' : Tendsto (fun h => raw h z)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have hc : Tendsto (fun _ : ℝ => spacetimeTimePartial Psi (t0, z))
          (nhdsWithin 0 {0}ᶜ)
          (nhds (spacetimeTimePartial Psi (t0, z))) := tendsto_const_nhds
      simpa [raw, RCLike.real_smul_eq_coe_mul, Complex.ofReal_inv] using hs.sub hc
    convert (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
      hs'.enorm using 1 <;> simp [Function.comp_def]
  have hint := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := volume.prod volume) (l := nhdsWithin (0 : ℝ) {0}ᶜ)
    (F := fun h z => ‖raw h z‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) bound
    (by filter_upwards with h; exact hmeas h)
    (by filter_upwards [self_mem_nhdsWithin] with h hh;
        exact hdom h (by simpa using hh))
    hbound_fin (Filter.Eventually.of_forall hpoint)
  simp only [lintegral_zero] at hint
  have hnorm : Tendsto (fun h => eLpNorm (raw h) 2 (volume.prod volume))
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    convert (ENNReal.continuous_rpow_const
      (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hint using 1 <;>
      simp [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
  apply hnorm.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  calc
    eLpNorm (raw h) 2 (volume.prod volume) =
        eLpNorm (((((h : ℝ)⁻¹) • (q (t0 + h) - q t0) - qdot :
          TwoParticleL2) : ℝ × ℝ → ℂ)) 2 (volume.prod volume) :=
      (hraw h (by simpa using hh)).symm
    _ = eLpNorm
        ((((((h : ℝ)⁻¹) • (q (t0 + h) - q t0) : TwoParticleL2) :
            ℝ × ℝ → ℂ) - (qdot : ℝ × ℝ → ℂ)))
          2 (volume.prod volume) := by
      exact eLpNorm_congr_ae (Lp.coeFn_sub
        (((h : ℝ)⁻¹) • (q (t0 + h) - q t0)) qdot)

private theorem twoFreeTranspose_spacetimeTestSection_derivative
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ)) (t : ℝ) :
    HasDerivAt
      (fun s => twoFreeTranspose s
        ((spacetimeTestSection Psi s).toLp 2 (volume.prod volume)))
      (Complex.I • twoFreeTranspose t
          ((pairLaplacian (spacetimeTestSection Psi t)).toLp 2
            (volume.prod volume)) +
        twoFreeTranspose t
          ((spacetimeTestSection (spacetimeTimePartial Psi) t).toLp 2
            (volume.prod volume))) t := by
  let q : ℝ → TwoParticleL2 := fun s =>
    (spacetimeTestSection Psi s).toLp 2 (volume.prod volume)
  let qdot : TwoParticleL2 :=
    (spacetimeTestSection (spacetimeTimePartial Psi) t).toLp 2
      (volume.prod volume)
  have hq : HasDerivAt q qdot t := by
    simpa [q, qdot] using spacetimeTestSection_hasDerivAt_toLp Psi hPsi t
  have hstatic := twoFreeTranspose_schwartz_derivative
    (spacetimeTestSection Psi t) t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hqslope := hasDerivAt_iff_tendsto_slope_zero.mp hq
  have htime : Tendsto (fun h : ℝ => t + h)
      (nhdsWithin 0 {0}ᶜ) (nhds t) := by
    have htime0 : Tendsto (fun h : ℝ => t + h) (nhds 0) (nhds t) := by
      simpa only [id_eq, add_zero] using
        (tendsto_const_nhds.add (tendsto_id : Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)))
    exact htime0.mono_left inf_le_left
  have hpair : Tendsto (fun h : ℝ =>
      (t + h, (h : ℝ)⁻¹ • (q (t + h) - q t)))
      (nhdsWithin 0 {0}ᶜ) (nhds (t, qdot)) := htime.prodMk_nhds hqslope
  let A : ℝ × TwoParticleL2 → TwoParticleL2 := fun p =>
    twoFreeTranspose p.1 p.2
  have hAcont : Continuous A := by
    simpa only [A] using continuous_twoFreeTranspose_joint
  have hA : Tendsto (fun h : ℝ =>
      twoFreeTranspose (t + h) ((h : ℝ)⁻¹ • (q (t + h) - q t)))
      (nhdsWithin 0 {0}ᶜ) (nhds (twoFreeTranspose t qdot)) := by
    change Tendsto
      (A ∘ fun h : ℝ => (t + h, (h : ℝ)⁻¹ • (q (t + h) - q t)))
      (nhdsWithin 0 {0}ᶜ) (nhds (A (t, qdot)))
    exact hAcont.continuousAt.tendsto.comp hpair
  have hB := hasDerivAt_iff_tendsto_slope_zero.mp hstatic
  convert hB.add hA using 1
  · funext h
    dsimp only [q]
    rw [twoFreeTranspose_real_smul]
    rw [twoFreeTranspose_sub]
    simp only [smul_sub]
    abel

/-- Physical exterior identity for an arbitrary compactly supported smooth
spacetime test, expressed through its spatial `L²` sections. -/
theorem physical_exterior_spacetime_interval (sigma : ℝ)
    (u v : GlobalSolution sigma) (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ))
    {a b : ℝ} (hPsia : ∀ z, Psi (a, z) = 0)
    (hPsib : ∀ z, Psi (b, z) = 0) :
    (∫ t in a..b,
      bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
        ((-Complex.I) •
            (spacetimeTestSection (spacetimeTimePartial Psi) t).toLp 2
              (volume.prod volume) +
          (pairLaplacian (spacetimeTestSection Psi t)).toLp 2
            (volume.prod volume))) =
      ∫ t in a..b, bilinearL2Two (exteriorSourceCurve sigma u v t)
        ((spacetimeTestSection Psi t).toLp 2 (volume.prod volume)) := by
  let q : ℝ → TwoParticleL2 := fun t =>
    (spacetimeTestSection Psi t).toLp 2 (volume.prod volume)
  let qt : ℝ → TwoParticleL2 := fun t =>
    (spacetimeTestSection (spacetimeTimePartial Psi) t).toLp 2
      (volume.prod volume)
  let qlap : ℝ → TwoParticleL2 := fun t =>
    (pairLaplacian (spacetimeTestSection Psi t)).toLp 2
      (volume.prod volume)
  let W : ℝ → TwoParticleL2 := fun t =>
    twoFreeProp (-t) (exteriorProductL2 (u.u t) (v.u t))
  let B : ℝ → TwoParticleL2 := fun t => twoFreeTranspose t (q t)
  let H : ℝ → ℂ := fun t => bilinearL2Two (W t) (B t)
  have htimeComp := spacetimeTimePartial_hasCompactSupport Psi hPsi
  have hlapComp := spacetimeSpatialLaplacian_hasCompactSupport Psi hPsi
  have hsectionCont (Phi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
      (hPhi : HasCompactSupport (Phi : ℝ × (ℝ × ℝ) → ℂ)) :
      Continuous (fun t =>
        (spacetimeTestSection Phi t).toLp 2 (volume.prod volume)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (spacetimeTestSection_hasDerivAt_toLp Phi hPhi t).continuousAt
  have hqcont : Continuous q := hsectionCont Psi hPsi
  have hqtcont : Continuous qt := hsectionCont (spacetimeTimePartial Psi) htimeComp
  have hlapcont : Continuous qlap := by
    have h := hsectionCont (spacetimeSpatialLaplacian Psi) hlapComp
    convert h using 1
    funext t
    rw [spacetimeTestSection_spatialLaplacian]
  have hBderiv (t : ℝ) : HasDerivAt B
      (Complex.I • twoFreeTranspose t (qlap t) +
        twoFreeTranspose t (qt t)) t := by
    simpa [B, q, qt, qlap] using
      twoFreeTranspose_spacetimeTestSection_derivative Psi hPsi t
  have hBdiff : ContDiff ℝ 1 B := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hBderiv t).differentiableAt, ?_⟩
    rw [show deriv B = fun t =>
        Complex.I • twoFreeTranspose t (qlap t) +
          twoFreeTranspose t (qt t) by
      funext t
      exact (hBderiv t).deriv]
    let A : ℝ × TwoParticleL2 → TwoParticleL2 := fun p =>
      twoFreeTranspose p.1 p.2
    have hAcont : Continuous A := by
      simpa only [A] using continuous_twoFreeTranspose_joint
    have hLapPair : Continuous (fun t : ℝ => (t, qlap t)) :=
      continuous_id.prodMk hlapcont
    have hTimePair : Continuous (fun t : ℝ => (t, qt t)) :=
      continuous_id.prodMk hqtcont
    have hLapT : Continuous (fun t => twoFreeTranspose t (qlap t)) := by
      change Continuous (A ∘ fun t : ℝ => (t, qlap t))
      exact hAcont.comp hLapPair
    have hTimeT : Continuous (fun t => twoFreeTranspose t (qt t)) := by
      change Continuous (A ∘ fun t : ℝ => (t, qt t))
      exact hAcont.comp hTimePair
    have hISmul : Continuous (fun t : ℝ =>
        (Complex.I : ℂ) • twoFreeTranspose t (qlap t)) :=
      (continuous_const : Continuous (fun _ : ℝ => (Complex.I : ℂ))).smul hLapT
    exact hISmul.add hTimeT
  have hWac : AbsolutelyContinuousOnInterval W a b := by
    have h := interaction_exterior_absolutelyContinuousOnInterval sigma u v a b
    convert h using 1
    funext t
    rw [← twoFreeProp_exteriorProductL2]
  have hBac : AbsolutelyContinuousOnInterval B a b :=
    hBdiff.contDiffOn.absolutelyContinuousOnInterval
  have hHac : AbsolutelyContinuousOnInterval H a b :=
    AbsolutelyContinuousOnInterval.clm_apply hWac hBac bilinearL2TwoRealCLM
  have hWderiv : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt W
        (-Complex.I • twoFreeProp (-t)
          (exteriorSourceCurve sigma u v t)) t := by
    simpa [W] using interaction_exterior_ae_hasDerivAt_source sigma u v a b
  have hHderiv : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt H
        (bilinearL2Two
            (-Complex.I • twoFreeProp (-t)
              (exteriorSourceCurve sigma u v t)) (B t) +
          bilinearL2Two (W t)
            (Complex.I • twoFreeTranspose t (qlap t) +
              twoFreeTranspose t (qt t))) t := by
    filter_upwards [hWderiv] with t ht htI
    change HasDerivAt
      (fun s => bilinearL2TwoRealCLM (W s) (B s)) _ t
    exact (bilinearL2TwoRealCLM.hasFDerivAt.comp_hasDerivAt t
      (ht htI)).clm_apply (hBderiv t)
  have hqzero_a : q a = 0 := by
    apply Lp.ext
    filter_upwards [(spacetimeTestSection Psi a).coeFn_toLp 2
      (volume.prod volume), Lp.coeFn_zero ℂ 2 (volume.prod volume)] with z hz h0
    rw [hz, h0, spacetimeTestSection_apply, hPsia]
    simp
  have hqzero_b : q b = 0 := by
    apply Lp.ext
    filter_upwards [(spacetimeTestSection Psi b).coeFn_toLp 2
      (volume.prod volume), Lp.coeFn_zero ℂ 2 (volume.prod volume)] with z hz h0
    rw [hz, h0, spacetimeTestSection_apply, hPsib]
    simp
  have htransposeZero (t : ℝ) : twoFreeTranspose t 0 = 0 := by
    simpa using twoFreeTranspose_smul (0 : ℂ) t (0 : TwoParticleL2)
  have hzero : H a = 0 ∧ H b = 0 := by
    constructor
    · dsimp [H, B]
      rw [hqzero_a, htransposeZero]
      exact map_zero (bilinearL2TwoCLM (W a))
    · dsimp [H, B]
      rw [hqzero_b, htransposeZero]
      exact map_zero (bilinearL2TwoCLM (W b))
  have hrealAc : AbsolutelyContinuousOnInterval (fun t => (H t).re) a b := by
    let R : ℂ →L[ℝ] ℝ := Complex.reCLM
    have hR : AbsolutelyContinuousOnInterval (fun _ : ℝ => R) a b :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => R)).contDiffOn
        |>.absolutelyContinuousOnInterval
    simpa [R] using AbsolutelyContinuousOnInterval.clm_apply hHac hR
      (ContinuousLinearMap.apply ℝ ℝ)
  have himagAc : AbsolutelyContinuousOnInterval (fun t => (H t).im) a b := by
    let R : ℂ →L[ℝ] ℝ := Complex.imCLM
    have hR : AbsolutelyContinuousOnInterval (fun _ : ℝ => R) a b :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => R)).contDiffOn
        |>.absolutelyContinuousOnInterval
    simpa [R] using AbsolutelyContinuousOnInterval.clm_apply hHac hR
      (ContinuousLinearMap.apply ℝ ℝ)
  have hrealInt := hrealAc.integral_deriv_eq_sub
  have himagInt := himagAc.integral_deriv_eq_sub
  rw [hzero.1, hzero.2] at hrealInt himagInt
  simp only [Complex.zero_re, sub_self] at hrealInt
  simp only [Complex.zero_im, sub_self] at himagInt
  have hformula : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b → deriv H t =
      (-Complex.I) * bilinearL2Two (exteriorSourceCurve sigma u v t) (q t) +
        Complex.I * bilinearL2Two
          (exteriorProductL2 (u.u t) (v.u t)) (qlap t) +
        bilinearL2Two (exteriorProductL2 (u.u t) (v.u t)) (qt t) := by
    filter_upwards [hHderiv] with t ht htI
    rw [(ht htI).deriv]
    dsimp [W, B]
    rw [bilinearL2Two_add_right, bilinearL2Two_smul_left,
      bilinearL2Two_smul_right, bilinearL2Two_transport_cancel,
      bilinearL2Two_transport_cancel, bilinearL2Two_transport_cancel]
    ring
  have hformula' : ∀ᵐ t : ℝ, t ∈ Set.uIoc a b → deriv H t =
      (-Complex.I) * bilinearL2Two (exteriorSourceCurve sigma u v t) (q t) +
        Complex.I * bilinearL2Two
          (exteriorProductL2 (u.u t) (v.u t)) (qlap t) +
        bilinearL2Two (exteriorProductL2 (u.u t) (v.u t)) (qt t) :=
    hformula.mono (fun t ht htI => ht (Set.uIoc_subset_uIcc htI))
  let D : ℝ → ℂ := fun t =>
    (-Complex.I) * bilinearL2Two (exteriorSourceCurve sigma u v t) (q t) +
      Complex.I * bilinearL2Two
        (exteriorProductL2 (u.u t) (v.u t)) (qlap t) +
      bilinearL2Two (exteriorProductL2 (u.u t) (v.u t)) (qt t)
  have hsourceCurve := exteriorSourceCurve_intervalIntegrable sigma u v a b
  have hqbounded : ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Set.uIcc a b, ‖q t‖ ≤ C := by
    have hcomp : IsCompact (q '' Set.uIcc a b) :=
      isCompact_uIcc.image_of_continuousOn hqcont.continuousOn
    obtain ⟨C, _hCpos, hC⟩ := hcomp.isBounded.subset_closedBall_lt 0
      (0 : TwoParticleL2)
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t ht
    have hm := hC ⟨t, ht, rfl⟩
    have hnorm : ‖q t‖ ≤ C := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    exact hnorm.trans (le_max_left _ _)
  obtain ⟨C, hC0, hqbound⟩ := hqbounded
  have sourcePair_integrable
      (mu : Measure ℝ) (hS : Integrable (exteriorSourceCurve sigma u v) mu)
      (hqmeas : AEStronglyMeasurable q mu)
      (hmem : ∀ᵐ t ∂mu, t ∈ Set.uIcc a b) :
      Integrable (fun t =>
        bilinearL2Two (exteriorSourceCurve sigma u v t) (q t)) mu := by
    have hmeas : AEStronglyMeasurable (fun t =>
        bilinearL2Two (exteriorSourceCurve sigma u v t) (q t)) mu :=
      bilinearL2TwoRealCLM.continuous₂.comp_aestronglyMeasurable
        (hS.1.prodMk hqmeas)
    refine (hS.norm.const_mul C).mono' hmeas ?_
    filter_upwards [hmem] with t ht
    calc
      ‖bilinearL2Two (exteriorSourceCurve sigma u v t) (q t)‖ ≤
          ‖exteriorSourceCurve sigma u v t‖ * ‖q t‖ :=
        norm_bilinearL2Two_le _ _
      _ ≤ ‖exteriorSourceCurve sigma u v t‖ * C := by
        gcongr
        exact hqbound t ht
      _ = C * ‖exteriorSourceCurve sigma u v t‖ := mul_comm _ _
  have hsource : IntervalIntegrable (fun t =>
      bilinearL2Two (exteriorSourceCurve sigma u v t) (q t)) volume a b := by
    constructor
    · apply sourcePair_integrable _ hsourceCurve.1
        hqcont.aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self ht)
    · apply sourcePair_integrable _ hsourceCurve.2
        hqcont.aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.uIcc_comm]
      exact Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self ht)
  have hE : Continuous (fun t => exteriorProductL2 (u.u t) (v.u t)) :=
    continuous_exteriorProductL2 u.u v.u u.continuous v.continuous
  have hElap : Continuous (fun t =>
      bilinearL2Two (exteriorProductL2 (u.u t) (v.u t)) (qlap t)) :=
    bilinearL2TwoRealCLM.continuous₂.comp (hE.prodMk hlapcont)
  have hEt : Continuous (fun t =>
      bilinearL2Two (exteriorProductL2 (u.u t) (v.u t)) (qt t)) :=
    bilinearL2TwoRealCLM.continuous₂.comp (hE.prodMk hqtcont)
  have hDint : IntervalIntegrable D volume a b := by
    dsimp [D]
    have hElapInt : IntervalIntegrable (fun t =>
        Complex.I * bilinearL2Two
          (exteriorProductL2 (u.u t) (v.u t)) (qlap t)) volume a b :=
      (hElap.const_mul Complex.I).intervalIntegrable a b
    have hEtInt : IntervalIntegrable (fun t =>
        bilinearL2Two (exteriorProductL2 (u.u t) (v.u t)) (qt t)) volume a b :=
      hEt.intervalIntegrable a b
    exact ((hsource.const_mul (-Complex.I)).add hElapInt).add hEtInt
  have hDzero : (∫ t in a..b, D t) = 0 := by
    apply Complex.ext
    · change RCLike.re (∫ t in a..b, D t) = RCLike.re (0 : ℂ)
      rw [← intervalIntegral.intervalIntegral_re hDint]
      change (∫ t in a..b, (D t).re) = 0
      calc
        _ = ∫ t in a..b, deriv (fun s => (H s).re) t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hformula', hHderiv] with t ht hHt htI
          have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
            (hHt (Set.uIoc_subset_uIcc htI))).deriv
          change deriv (fun s => (H s).re) t = _ at hre
          calc
            (D t).re = (deriv H t).re := congrArg Complex.re ((ht htI).symm)
            _ = _ := by rw [(hHt (Set.uIoc_subset_uIcc htI)).deriv]; exact hre.symm
        _ = 0 := hrealInt
    · change RCLike.im (∫ t in a..b, D t) = RCLike.im (0 : ℂ)
      rw [← intervalIntegral.intervalIntegral_im hDint]
      change (∫ t in a..b, (D t).im) = 0
      calc
        _ = ∫ t in a..b, deriv (fun s => (H s).im) t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hformula', hHderiv] with t ht hHt htI
          have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
            (hHt (Set.uIoc_subset_uIcc htI))).deriv
          change deriv (fun s => (H s).im) t = _ at him
          calc
            (D t).im = (deriv H t).im := congrArg Complex.im ((ht htI).symm)
            _ = _ := by rw [(hHt (Set.uIoc_subset_uIcc htI)).deriv]; exact him.symm
        _ = 0 := himagInt
  have hscaled := congrArg (fun z : ℂ => -Complex.I * z) hDzero
  simp only [mul_zero] at hscaled
  rw [← intervalIntegral.integral_const_mul] at hscaled
  let L : ℝ → ℂ := fun t =>
    bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
      ((-Complex.I) • qt t + qlap t)
  let R : ℝ → ℂ := fun t =>
    bilinearL2Two (exteriorSourceCurve sigma u v t) (q t)
  have hLint : IntervalIntegrable L volume a b := by
    dsimp [L]
    have htmp : IntervalIntegrable (fun t =>
        -Complex.I * bilinearL2Two
            (exteriorProductL2 (u.u t) (v.u t)) (qt t) +
          bilinearL2Two
            (exteriorProductL2 (u.u t) (v.u t)) (qlap t)) volume a b :=
      ((hEt.const_mul (-Complex.I)).add hElap).intervalIntegrable a b
    simpa only [bilinearL2Two_add_right, bilinearL2Two_smul_right,
      smul_eq_mul] using htmp
  have hRint : IntervalIntegrable R volume a b := hsource
  have hscaled' : (∫ t in a..b, L t - R t) = 0 := by
    calc
      _ = ∫ t in a..b, -Complex.I * D t := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [L, R, D]
        rw [bilinearL2Two_add_right, bilinearL2Two_smul_right]
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = 0 := hscaled
  rw [intervalIntegral.integral_sub hLint hRint] at hscaled'
  exact sub_eq_zero.mp hscaled'

/-! ## From the section identity to the distributional equation -/

/-- The spacetime Schwartz function which represents the formal adjoint of
`i∂ₜ + ∂ₓ² + ∂ᵧ²`. -/
private def spacetimeAdjointSchwartz
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) : 𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  (-Complex.I) • spacetimeTimePartial Psi + spacetimeSpatialLaplacian Psi

private lemma spacetimeAdjointSchwartz_hasCompactSupport
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ)) :
    HasCompactSupport
      (spacetimeAdjointSchwartz Psi : ℝ × (ℝ × ℝ) → ℂ) := by
  exact (spacetimeTimePartial_hasCompactSupport Psi hPsi).smul_left
    |>.add (spacetimeSpatialLaplacian_hasCompactSupport Psi hPsi)

private lemma spacetimeAdjointSchwartz_apply
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) :
    spacetimeAdjointSchwartz Psi p =
      -Complex.I * deriv (fun t => Psi (t, p.2)) p.1 +
        iteratedDeriv 2 (fun x => Psi (p.1, (x, p.2.2))) p.2.1 +
        iteratedDeriv 2 (fun y => Psi (p.1, (p.2.1, y))) p.2.2 := by
  rcases p with ⟨t, x, y⟩
  have ht := deriv_spacetimeTestSection Psi t (x, y)
  have hlap := congrArg (fun q : 𝓢(ℝ × ℝ, ℂ) => q (x, y))
    (spacetimeTestSection_spatialLaplacian Psi t)
  simp only [spacetimeTestSection_apply, pairLaplacian, add_apply,
    pairPartial0_apply, pairPartial1_apply] at hlap
  change -Complex.I * spacetimeTimePartial Psi (t, (x, y)) +
      spacetimeSpatialLaplacian Psi (t, (x, y)) = _
  rw [← ht, hlap]
  simp only [show iteratedDeriv 2 (fun x => Psi (t, (x, y))) =
      deriv (deriv (fun x => Psi (t, (x, y)))) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_one],
    show iteratedDeriv 2 (fun y => Psi (t, (x, y))) =
      deriv (deriv (fun y => Psi (t, (x, y)))) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_one]]
  ring

/-- A locally `L²` spacetime field is integrable after multiplication by a
compactly supported spacetime Schwartz function. -/
private theorem localL2_mul_compactSchwartz_integrable
    (F : ℝ × (ℝ × ℝ) → ℂ)
    (hFmeas : Measurable F)
    (hFlocal : ∀ T : ℝ, 0 ≤ T →
      MemLp F 2
        (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ))))
    (Phi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPhi : HasCompactSupport (Phi : ℝ × (ℝ × ℝ) → ℂ)) :
    Integrable (fun p => F p * Phi p)
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
  obtain ⟨R, hR⟩ :=
    hPhi.isCompact.isBounded.subset_closedBall (0 : ℝ × (ℝ × ℝ))
  let T : ℝ := |R| + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let S : Set (ℝ × (ℝ × ℝ)) := Set.Icc (-T) T ×ˢ Set.univ
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hFind : MemLp (S.indicator F) 2
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    rw [memLp_indicator_iff_restrict hS]
    rw [← Measure.restrict_prod_eq_prod_univ]
    exact hFlocal T hT
  have hPhiLp : MemLp (Phi : ℝ × (ℝ × ℝ) → ℂ) 2
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    exact Phi.continuous.memLp_of_hasCompactSupport hPhi
  have hprod : MemLp (fun p => Phi p * S.indicator F p) 1
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) :=
    hFind.mul' hPhiLp
  have hzero (p : ℝ × (ℝ × ℝ)) (hp : p.1 ∉ Set.Icc (-T) T) :
      Phi p = 0 := by
    by_contra hn
    have hpSupp : p ∈ tsupport (Phi : ℝ × (ℝ × ℝ) → ℂ) :=
      subset_tsupport _ hn
    have hpBall := hR hpSupp
    have hcoord : |p.1| ≤ R := by
      have hnorm : ‖p‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hpBall
      exact (show |p.1| ≤ ‖p‖ by
        simp only [Prod.norm_def, Real.norm_eq_abs]
        exact le_max_left _ _).trans hnorm
    have hcoordT : |p.1| ≤ T := by
      calc
        |p.1| ≤ R := hcoord
        _ ≤ |R| := le_abs_self R
        _ ≤ T := by dsimp [T]; linarith
    exact hp (abs_le.mp hcoordT)
  rw [memLp_one_iff_integrable] at hprod
  convert hprod using 1
  funext p
  by_cases hp : p.1 ∈ Set.Icc (-T) T
  · simp [S, hp, mul_comm]
  · simp [S, hp, hzero p hp]

private theorem measurableExterior_mul_compactSchwartz_integrable
    (sigma : ℝ) (u v : GlobalSolution sigma)
    (Phi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPhi : HasCompactSupport (Phi : ℝ × (ℝ × ℝ) → ℂ)) :
    Integrable (fun p => measurableExterior u v p * Phi p)
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
  exact localL2_mul_compactSchwartz_integrable
    (measurableExterior u v) (measurableExterior_measurable u v)
    (fun T _ => measurableExterior_memLp_two_Icc sigma u v T) Phi hPhi

private theorem measurableExteriorSource_mul_compactSchwartz_integrable
    (sigma : ℝ) (u v : GlobalSolution sigma)
    (Phi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPhi : HasCompactSupport (Phi : ℝ × (ℝ × ℝ) → ℂ)) :
    Integrable (fun p => measurableExteriorSource sigma u v p * Phi p)
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
  exact localL2_mul_compactSchwartz_integrable
    (measurableExteriorSource sigma u v)
    (measurableExteriorSource_measurable sigma u v)
    (measurableExteriorSource_memLp_two_Icc sigma u v) Phi hPhi

/-! ## Orthogonal transport to normal/tangential coordinates -/

private noncomputable def timeNormalCLE :
    (ℝ × (ℝ × ℝ)) ≃L[ℝ] (ℝ × (ℝ × ℝ)) :=
  ((LinearEquiv.refl ℝ ℝ).prodCongr normalToParticle).toContinuousLinearEquiv

private lemma timeNormalCLE_apply (p : ℝ × (ℝ × ℝ)) :
    timeNormalCLE p = fromNormalCoordinates p := rfl

private lemma timeNormalCLE_measurePreserving :
    MeasurePreserving timeNormalCLE
      ((volume : Measure ℝ).prod (volume.prod volume))
      ((volume : Measure ℝ).prod (volume.prod volume)) := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    normalToParticle_measurePreserving
  change MeasurePreserving (fun p : ℝ × (ℝ × ℝ) =>
    (p.1, normalToParticle p.2))
      ((volume : Measure ℝ).prod (volume.prod volume))
      ((volume : Measure ℝ).prod (volume.prod volume))
  change MeasurePreserving (Prod.map id normalToParticle)
      ((volume : Measure ℝ).prod (volume.prod volume))
      ((volume : Measure ℝ).prod (volume.prod volume))
  exact h

private def physicalPullback (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    𝓢(ℝ × (ℝ × ℝ), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ timeNormalCLE.symm Psi

@[simp] private lemma physicalPullback_apply_normal
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) :
    physicalPullback Psi (timeNormalCLE p) = Psi p := by
  change Psi (timeNormalCLE.symm (timeNormalCLE p)) = Psi p
  rw [timeNormalCLE.symm_apply_apply]

private lemma physicalPullback_timePartial
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    spacetimeTimePartial (physicalPullback Psi) =
      physicalPullback (spacetimeTimePartial Psi) := by
  unfold spacetimeTimePartial physicalPullback
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  congr 2
  ext <;> simp [timeNormalCLE, normalToParticle]

private lemma normal_directional_laplacian
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    ∂_{((0, (1, 0)) : ℝ × (ℝ × ℝ))}
        (∂_{((0, (1, 0)) : ℝ × (ℝ × ℝ))} Psi) +
      ∂_{((0, (0, 1)) : ℝ × (ℝ × ℝ))}
        (∂_{((0, (0, 1)) : ℝ × (ℝ × ℝ))} Psi) =
    ∂_{((0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))}
        (∂_{((0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))} Psi) +
      ∂_{((0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))}
        (∂_{((0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))} Psi) := by
  let B : (ℝ × (ℝ × ℝ)) →ₗ[ℝ]
      (ℝ × (ℝ × ℝ)) →ₗ[ℝ] 𝓢(ℝ × (ℝ × ℝ), ℂ) :=
    bilinearLineDerivTwo ℝ Psi
  change B (0, (1, 0)) (0, (1, 0)) + B (0, (0, 1)) (0, (0, 1)) =
    B (0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹))
      (0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) +
    B (0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹))
      (0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹))
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    field_simp [hs0]
    nlinarith [hs]
  rw [show (0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) =
      (Real.sqrt 2)⁻¹ •
        ((0, ((1 : ℝ), (1 : ℝ))) : ℝ × (ℝ × ℝ)) by ext <;> simp,
    show (0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) =
      (Real.sqrt 2)⁻¹ •
        ((0, (-(1 : ℝ), (1 : ℝ))) : ℝ × (ℝ × ℝ)) by ext <;> simp]
  simp only [map_smul]
  rw [show ((0, ((1 : ℝ), (1 : ℝ))) : ℝ × (ℝ × ℝ)) =
      (0, (1, 0)) + (0, (0, 1)) by ext <;> simp,
    show ((0, (-(1 : ℝ), (1 : ℝ))) : ℝ × (ℝ × ℝ)) =
      -(0, (1, 0)) + (0, (0, 1)) by ext <;> simp]
  simp only [map_add, map_neg, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.smul_apply]
  simp only [smul_add, smul_neg, smul_smul]
  rw [hc]
  module

private lemma physicalPullback_spatialLaplacian
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    spacetimeSpatialLaplacian (physicalPullback Psi) =
      physicalPullback (spacetimeSpatialLaplacian Psi) := by
  unfold spacetimeSpatialLaplacian spacetimePartial0 spacetimePartial1
  simp only [physicalPullback,
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  have hx : timeNormalCLE.symm ((0, (1, 0)) : ℝ × (ℝ × ℝ)) =
      (0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) := by
    ext <;> simp [timeNormalCLE, normalToParticle]
  have hy : timeNormalCLE.symm ((0, (0, 1)) : ℝ × (ℝ × ℝ)) =
      (0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) := by
    ext <;> simp [timeNormalCLE, normalToParticle] <;> ring
  rw [hx, hy]
  change SchwartzMap.compCLMOfContinuousLinearEquiv ℂ timeNormalCLE.symm
      (∂_{((0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))}
        (∂_{((0, ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))} Psi)) +
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ timeNormalCLE.symm
      (∂_{((0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))}
        (∂_{((0, (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)) : ℝ × (ℝ × ℝ))} Psi)) = _
  rw [← map_add, ← normal_directional_laplacian]

private lemma physicalPullback_adjoint
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) :
    spacetimeAdjointSchwartz (physicalPullback Psi) =
      physicalPullback (spacetimeAdjointSchwartz Psi) := by
  unfold spacetimeAdjointSchwartz
  rw [physicalPullback_timePartial, physicalPullback_spatialLaplacian]
  unfold physicalPullback
  rw [map_add, map_smul]

private lemma physicalPullback_adjoint_apply_normal
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) :
    spacetimeAdjointSchwartz (physicalPullback Psi) (timeNormalCLE p) =
      spacetimeAdjointSchwartz Psi p := by
  rw [physicalPullback_adjoint, physicalPullback_apply_normal]

@[simp] private lemma physicalPullback_apply_fromNormal
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) :
    physicalPullback Psi (p.1, normalToParticle p.2) = Psi p := by
  have h := physicalPullback_apply_normal Psi p
  rw [timeNormalCLE_apply, fromNormalCoordinates_eq] at h
  exact h

@[simp] private lemma physicalPullback_adjoint_apply_fromNormal
    (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ)) (p : ℝ × (ℝ × ℝ)) :
    spacetimeAdjointSchwartz (physicalPullback Psi)
        (p.1, normalToParticle p.2) =
      spacetimeAdjointSchwartz Psi p := by
  have h := physicalPullback_adjoint_apply_normal Psi p
  rw [timeNormalCLE_apply, fromNormalCoordinates_eq] at h
  exact h

/-- The physical exterior field satisfies its weak equation against every
compactly supported spacetime Schwartz test. -/
private theorem physical_exterior_schwartz_equation (sigma : ℝ)
    (u v : GlobalSolution sigma) (Psi : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (hPsi : HasCompactSupport (Psi : ℝ × (ℝ × ℝ) → ℂ)) :
    Integrable (fun p => measurableExterior u v p * Psi p)
        ((volume : Measure ℝ).prod (volume.prod volume)) ∧
    Integrable (fun p => measurableExterior u v p *
        spacetimeAdjointSchwartz Psi p)
        ((volume : Measure ℝ).prod (volume.prod volume)) ∧
    Integrable (fun p => measurableExteriorSource sigma u v p * Psi p)
        ((volume : Measure ℝ).prod (volume.prod volume)) ∧
    (∫ p, measurableExterior u v p * spacetimeAdjointSchwartz Psi p
        ∂((volume : Measure ℝ).prod (volume.prod volume))) =
      ∫ p, measurableExteriorSource sigma u v p * Psi p
        ∂((volume : Measure ℝ).prod (volume.prod volume)) := by
  have hAdj := spacetimeAdjointSchwartz_hasCompactSupport Psi hPsi
  have hFtest := measurableExterior_mul_compactSchwartz_integrable
    sigma u v Psi hPsi
  have hFadj := measurableExterior_mul_compactSchwartz_integrable
    sigma u v (spacetimeAdjointSchwartz Psi) hAdj
  have hRtest := measurableExteriorSource_mul_compactSchwartz_integrable
    sigma u v Psi hPsi
  refine ⟨hFtest, hFadj, hRtest, ?_⟩
  have hadjSection (t : ℝ) :
      spacetimeTestSection (spacetimeAdjointSchwartz Psi) t =
        (-Complex.I) • spacetimeTestSection (spacetimeTimePartial Psi) t +
          pairLaplacian (spacetimeTestSection Psi t) := by
    rw [← spacetimeTestSection_spatialLaplacian]
    ext z
    simp [spacetimeAdjointSchwartz]
  have hadjToLp (t : ℝ) :
      (spacetimeTestSection (spacetimeAdjointSchwartz Psi) t).toLp 2
          (volume.prod volume) =
        (-Complex.I) •
            (spacetimeTestSection (spacetimeTimePartial Psi) t).toLp 2
              (volume.prod volume) +
          (pairLaplacian (spacetimeTestSection Psi t)).toLp 2
            (volume.prod volume) := by
    rw [hadjSection]
    change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume.prod volume))
        ((-Complex.I) • spacetimeTestSection (spacetimeTimePartial Psi) t +
          pairLaplacian (spacetimeTestSection Psi t)) = _
    rw [map_add, map_smul]
    rfl
  let L : ℝ → ℂ := fun t =>
    bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
      ((spacetimeTestSection (spacetimeAdjointSchwartz Psi) t).toLp 2
        (volume.prod volume))
  let R : ℝ → ℂ := fun t =>
    bilinearL2Two (exteriorSourceCurve sigma u v t)
      ((spacetimeTestSection Psi t).toLp 2 (volume.prod volume))
  have hleftGlobal :
      (∫ p, measurableExterior u v p * spacetimeAdjointSchwartz Psi p
          ∂((volume : Measure ℝ).prod (volume.prod volume))) =
        ∫ t, L t := by
    rw [MeasureTheory.integral_prod _ hFadj]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [L]
    rw [bilinearL2Two_exteriorProductL2]
    apply integral_congr_ae
    filter_upwards [measurableExterior_slice u v t] with z hz
    rw [hz]
    rfl
  have hrightGlobal :
      (∫ p, measurableExteriorSource sigma u v p * Psi p
          ∂((volume : Measure ℝ).prod (volume.prod volume))) =
        ∫ t, R t := by
    rw [MeasureTheory.integral_prod _ hRtest]
    apply integral_congr_ae
    filter_upwards [measurableExteriorSource_slice sigma u v] with t ht
    dsimp [R]
    rw [bilinearL2Two_eq_integral]
    apply integral_congr_ae
    filter_upwards [ht,
      (spacetimeTestSection Psi t).coeFn_toLp 2 (volume.prod volume)]
      with z hz hq
    rw [hz, hq]
    rfl
  obtain ⟨Rpsi, hRpsi⟩ :=
    hPsi.isCompact.isBounded.subset_closedBall (0 : ℝ × (ℝ × ℝ))
  obtain ⟨Radj, hRadj⟩ :=
    hAdj.isCompact.isBounded.subset_closedBall (0 : ℝ × (ℝ × ℝ))
  let T : ℝ := |Rpsi| + |Radj| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hPsiZero (t : ℝ) (ht : t ∉ Set.Ioc (-T) T) (z : ℝ × ℝ) :
      Psi (t, z) = 0 := by
    by_contra hn
    have hp := hRpsi (subset_tsupport _ hn)
    have htR : |t| ≤ Rpsi := by
      have hnorm : ‖(t, z)‖ ≤ Rpsi := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hp
      exact (show |t| ≤ ‖(t, z)‖ by
        simp only [Prod.norm_def, Real.norm_eq_abs]
        exact le_max_left _ _).trans hnorm
    have htT : |t| < T := by
      calc
        |t| ≤ Rpsi := htR
        _ ≤ |Rpsi| := le_abs_self Rpsi
        _ < T := by dsimp [T]; linarith [abs_nonneg Radj]
    exact ht ⟨(abs_lt.mp htT).1, (abs_lt.mp htT).2.le⟩
  have hAdjZero (t : ℝ) (ht : t ∉ Set.Ioc (-T) T) (z : ℝ × ℝ) :
      spacetimeAdjointSchwartz Psi (t, z) = 0 := by
    by_contra hn
    have hp := hRadj (subset_tsupport _ hn)
    have htR : |t| ≤ Radj := by
      have hnorm : ‖(t, z)‖ ≤ Radj := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hp
      exact (show |t| ≤ ‖(t, z)‖ by
        simp only [Prod.norm_def, Real.norm_eq_abs]
        exact le_max_left _ _).trans hnorm
    have htT : |t| < T := by
      calc
        |t| ≤ Radj := htR
        _ ≤ |Radj| := le_abs_self Radj
        _ < T := by dsimp [T]; linarith [abs_nonneg Rpsi]
    exact ht ⟨(abs_lt.mp htT).1, (abs_lt.mp htT).2.le⟩
  have hPsiAtLeft (z : ℝ × ℝ) : Psi (-T, z) = 0 :=
    hPsiZero (-T) (by simp) z
  have hPsiAtRight (z : ℝ × ℝ) : Psi (T, z) = 0 := by
    by_contra hn
    have hp := hRpsi (subset_tsupport _ hn)
    have hcoord : T ≤ Rpsi := by
      have hnorm : ‖(T, z)‖ ≤ Rpsi := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hp
      have hle : |T| ≤ ‖(T, z)‖ := by
        simp only [Prod.norm_def, Real.norm_eq_abs]
        exact le_max_left _ _
      simpa [abs_of_pos hT] using hle.trans hnorm
    have : Rpsi < T := by
      calc
        Rpsi ≤ |Rpsi| := le_abs_self Rpsi
        _ < T := by dsimp [T]; linarith [abs_nonneg Radj]
    linarith
  have hLzero (t : ℝ) (ht : t ∉ Set.Ioc (-T) T) : L t = 0 := by
    have hs : spacetimeTestSection (spacetimeAdjointSchwartz Psi) t = 0 := by
      ext z
      exact hAdjZero t ht z
    dsimp [L]
    rw [hs]
    change bilinearL2Two _ ((SchwartzMap.toLpCLM ℂ ℂ 2
      (volume.prod volume)) 0) = 0
    rw [map_zero]
    exact map_zero (bilinearL2TwoCLM (exteriorProductL2 (u.u t) (v.u t)))
  have hRzero (t : ℝ) (ht : t ∉ Set.Ioc (-T) T) : R t = 0 := by
    have hs : spacetimeTestSection Psi t = 0 := by
      ext z
      exact hPsiZero t ht z
    dsimp [R]
    rw [hs]
    change bilinearL2Two _ ((SchwartzMap.toLpCLM ℂ ℂ 2
      (volume.prod volume)) 0) = 0
    rw [map_zero]
    exact map_zero (bilinearL2TwoCLM (exteriorSourceCurve sigma u v t))
  have hLglobal : (∫ t, L t) = ∫ t in (-T)..T, L t := by
    calc
      (∫ t, L t) = ∫ t in Set.Ioc (-T) T, L t :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hLzero).symm
      _ = ∫ t in (-T)..T, L t :=
        (intervalIntegral.integral_of_le
          (a := -T) (b := T) (f := L) (μ := volume) (by linarith)).symm
  have hRglobal : (∫ t, R t) = ∫ t in (-T)..T, R t := by
    calc
      (∫ t, R t) = ∫ t in Set.Ioc (-T) T, R t :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hRzero).symm
      _ = ∫ t in (-T)..T, R t :=
        (intervalIntegral.integral_of_le
          (a := -T) (b := T) (f := R) (μ := volume) (by linarith)).symm
  have hinterval : (∫ t in (-T)..T, L t) = ∫ t in (-T)..T, R t := by
    have h := physical_exterior_spacetime_interval sigma u v Psi hPsi
      hPsiAtLeft hPsiAtRight
    convert h using 1 <;> apply intervalIntegral.integral_congr <;>
      intro t _
    · dsimp [L]
      rw [hadjToLp]
  rw [hleftGlobal, hrightGlobal, hLglobal, hRglobal, hinterval]

/-- The measurable physical exterior field satisfies the distributional
two-particle equation with its measurable nonlinear source. -/
theorem physical_exterior_weak_equation (sigma : ℝ)
    (u v : GlobalSolution sigma) :
    IsWeakTwoParticleEquation (measurableExterior u v)
      (measurableExteriorSource sigma u v) := by
  intro Psi hPsiDiff hPsiComp
  let PsiS : 𝓢(ℝ × (ℝ × ℝ), ℂ) :=
    hPsiComp.toSchwartzMap hPsiDiff
  have h := physical_exterior_schwartz_equation sigma u v PsiS hPsiComp
  simpa [PsiS, spacetimeAdjointSchwartz_apply] using h

/-- The physical weak equation transported through the unit-Jacobian
normal/tangential rotation. -/
theorem normal_exterior_weak_equation (sigma : ℝ)
    (u v : GlobalSolution sigma) :
    IsWeakTwoParticleEquation (measurableNormalExterior u v)
      (measurableNormalExteriorSource sigma u v) := by
  intro Psi hPsiDiff hPsiComp
  let PsiS : 𝓢(ℝ × (ℝ × ℝ), ℂ) :=
    hPsiComp.toSchwartzMap hPsiDiff
  have hPsiS : (PsiS : ℝ × (ℝ × ℝ) → ℂ) = Psi := rfl
  let PhiS : 𝓢(ℝ × (ℝ × ℝ), ℂ) := physicalPullback PsiS
  have hPhiComp : HasCompactSupport
      (PhiS : ℝ × (ℝ × ℝ) → ℂ) := by
    have h := hPsiComp.comp_homeomorph timeNormalCLE.symm.toHomeomorph
    simpa [PhiS, physicalPullback, hPsiS] using h
  have hphys := physical_exterior_schwartz_equation
    sigma u v PhiS hPhiComp
  let mu : Measure (ℝ × (ℝ × ℝ)) :=
    (volume : Measure ℝ).prod (volume.prod volume)
  have hmp : MeasurePreserving timeNormalCLE mu mu := by
    simpa [mu] using timeNormalCLE_measurePreserving
  have hemb : MeasurableEmbedding timeNormalCLE :=
    timeNormalCLE.toHomeomorph.measurableEmbedding
  have hFtest : Integrable
      (fun p => measurableNormalExterior u v p * PsiS p) mu := by
    have hc := (hmp.integrable_comp_emb hemb).2 hphys.1
    simpa [Function.comp_def, mu, PhiS, measurableNormalExterior,
      fromNormalCoordinates_eq, timeNormalCLE_apply,
      physicalPullback_apply_normal] using hc
  have hFadj : Integrable
      (fun p => measurableNormalExterior u v p *
        spacetimeAdjointSchwartz PsiS p) mu := by
    have hc := (hmp.integrable_comp_emb hemb).2 hphys.2.1
    simpa [Function.comp_def, mu, PhiS, measurableNormalExterior,
      fromNormalCoordinates_eq, timeNormalCLE_apply,
      physicalPullback_adjoint_apply_normal] using hc
  have hRtest : Integrable
      (fun p => measurableNormalExteriorSource sigma u v p * PsiS p) mu := by
    have hc := (hmp.integrable_comp_emb hemb).2 hphys.2.2.1
    simpa [Function.comp_def, mu, PhiS, measurableNormalExteriorSource,
      fromNormalCoordinates_eq, timeNormalCLE_apply,
      physicalPullback_apply_normal] using hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [PsiS, mu] using hFtest
  · simpa [PsiS, mu, spacetimeAdjointSchwartz_apply] using hFadj
  · simpa [PsiS, mu] using hRtest
  · have hleft := hmp.integral_comp hemb
        (fun q => measurableExterior u v q * spacetimeAdjointSchwartz PhiS q)
    have hright := hmp.integral_comp hemb
        (fun q => measurableExteriorSource sigma u v q * PhiS q)
    have heq :
        (∫ p, measurableNormalExterior u v p *
            spacetimeAdjointSchwartz PsiS p ∂mu) =
          ∫ p, measurableNormalExteriorSource sigma u v p * PsiS p ∂mu := by
      calc
        _ = ∫ q, measurableExterior u v q *
              spacetimeAdjointSchwartz PhiS q ∂mu := by
          simpa [Function.comp_def, PhiS, measurableNormalExterior,
            fromNormalCoordinates_eq, timeNormalCLE_apply,
            physicalPullback_adjoint_apply_normal]
            using hleft
        _ = ∫ q, measurableExteriorSource sigma u v q * PhiS q ∂mu :=
          hphys.2.2.2
        _ = _ := by
          simpa [Function.comp_def, PhiS, measurableNormalExteriorSource,
            fromNormalCoordinates_eq, timeNormalCLE_apply,
            physicalPullback_apply_normal] using hright.symm
    simpa [PsiS, mu, spacetimeAdjointSchwartz_apply] using heq

/-- On an open equal-modulus time region the transported source is the real
ridge potential times the normal exterior field. -/
theorem normal_exterior_weak_equation_on_sameModulus (sigma : ℝ)
    (u v : GlobalSolution sigma) (I : Set ℝ) (hI : IsOpen I)
    (hmod : SameModulusOnSet I u.u v.u) :
    IsWeakTwoParticleEquationOn I (measurableNormalExterior u v)
      (fun p => measurableRidgePotential sigma u p *
        measurableNormalExterior u v p) := by
  intro Psi hPsiDiff hPsiComp hPsiI
  have hglobal := normal_exterior_weak_equation sigma u v
    Psi hPsiDiff hPsiComp
  let mu : Measure (ℝ × (ℝ × ℝ)) :=
    (volume : Measure ℝ).prod (volume.prod volume)
  let S : Set (ℝ × (ℝ × ℝ)) := I ×ˢ Set.univ
  have hS : MeasurableSet S := hI.measurableSet.prod MeasurableSet.univ
  have hsource := measurableNormalExteriorSource_eq_ridge_mul
    sigma u v I hI hmod
  have hsource' : ∀ᵐ p ∂mu, p ∈ S →
      measurableNormalExteriorSource sigma u v p =
        measurableRidgePotential sigma u p *
          measurableNormalExterior u v p := by
    apply (ae_restrict_iff' hS).mp
    rw [← Measure.restrict_prod_eq_prod_univ]
    simpa [mu, S] using hsource
  have hprodEq :
      (fun p => measurableNormalExteriorSource sigma u v p * Psi p) =ᵐ[mu]
      (fun p => (measurableRidgePotential sigma u p *
        measurableNormalExterior u v p) * Psi p) := by
    filter_upwards [hsource'] with p hp
    by_cases hzero : Psi p = 0
    · simp [hzero]
    · have hpSupp : p ∈ tsupport Psi := subset_tsupport _ hzero
      have hpI : p.1 ∈ I := hPsiI p hpSupp
      rw [hp ⟨hpI, Set.mem_univ _⟩]
  have hforcingInt : Integrable
      (fun p => (measurableRidgePotential sigma u p *
        measurableNormalExterior u v p) * Psi p) mu :=
    hglobal.2.2.1.congr hprodEq
  refine ⟨hglobal.1, hglobal.2.1, ?_, ?_⟩
  · simpa [mu] using hforcingInt
  · calc
      (∫ p, measurableNormalExterior u v p *
          (-Complex.I * deriv (fun t => Psi (t, p.2)) p.1 +
            iteratedDeriv 2 (fun x => Psi (p.1, (x, p.2.2))) p.2.1 +
            iteratedDeriv 2 (fun y => Psi (p.1, (p.2.1, y))) p.2.2)
          ∂(volume.prod (volume.prod volume))) =
        ∫ p, measurableNormalExteriorSource sigma u v p * Psi p
          ∂(volume.prod (volume.prod volume)) := hglobal.2.2.2
      _ = ∫ p, (measurableRidgePotential sigma u p *
            measurableNormalExterior u v p) * Psi p
          ∂(volume.prod (volume.prod volume)) := by
        exact integral_congr_ae (by simpa [mu] using hprodEq)

/-- The interaction-picture exterior identity transported back to physical
space, for a compact temporal factor and a Schwartz spatial factor.  This is
the separated-test core of the full distributional two-particle equation. -/
theorem physical_exterior_separated_interval (sigma : ℝ)
    (u v : GlobalSolution sigma) (eta : SchwartzMap ℝ ℂ)
    (q : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ}
    (hetaa : eta a = 0) (hetab : eta b = 0) :
    (∫ t in a..b, bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
      ((-Complex.I * deriv (eta : ℝ → ℂ) t) •
          q.toLp 2 (volume.prod volume) +
        eta t • (pairLaplacian q).toLp 2 (volume.prod volume))) =
      ∫ t in a..b, bilinearL2Two (exteriorSourceCurve sigma u v t)
        (eta t • q.toLp 2 (volume.prod volume)) := by
  let W : ℝ → TwoParticleL2 := fun t =>
    twoFreeProp (-t) (exteriorProductL2 (u.u t) (v.u t))
  let B : ℝ → TwoParticleL2 := fun t =>
    eta t • twoFreeTranspose t (q.toLp 2 (volume.prod volume))
  let H : ℝ → ℂ := fun t => bilinearL2Two (W t) (B t)
  have hWac : AbsolutelyContinuousOnInterval W a b := by
    have h := interaction_exterior_absolutelyContinuousOnInterval sigma u v a b
    convert h using 1
    funext t
    rw [← twoFreeProp_exteriorProductL2]
  have hBdiff : ContDiff ℝ 1 B := by
    simpa [B] using separatedTranspose_contDiff eta q
  have hBac : AbsolutelyContinuousOnInterval B a b :=
    hBdiff.contDiffOn.absolutelyContinuousOnInterval
  have hHac : AbsolutelyContinuousOnInterval H a b := by
    exact AbsolutelyContinuousOnInterval.clm_apply hWac hBac bilinearL2TwoRealCLM
  have hWderiv : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt W
        (-Complex.I • twoFreeProp (-t) (exteriorSourceCurve sigma u v t)) t := by
    simpa [W] using interaction_exterior_ae_hasDerivAt_source sigma u v a b
  have hHderiv : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt H
        (bilinearL2Two
            (-Complex.I • twoFreeProp (-t)
              (exteriorSourceCurve sigma u v t)) (B t) +
          bilinearL2Two (W t)
            (eta t • Complex.I • twoFreeTranspose t
                ((pairLaplacian q).toLp 2 (volume.prod volume)) +
              deriv (eta : ℝ → ℂ) t •
                twoFreeTranspose t (q.toLp 2 (volume.prod volume)))) t := by
    filter_upwards [hWderiv] with t ht htI
    have hwt := ht htI
    have hbt := separatedTranspose_derivative eta q t
    change HasDerivAt
      (fun s => bilinearL2TwoRealCLM (W s) (B s)) _ t
    exact (bilinearL2TwoRealCLM.hasFDerivAt.comp_hasDerivAt t hwt).clm_apply hbt
  have hzero : H a = 0 ∧ H b = 0 := by
    constructor
    · dsimp [H, B]
      rw [hetaa, zero_smul, bilinearL2Two_eq_integral]
      simp
    · dsimp [H, B]
      rw [hetab, zero_smul, bilinearL2Two_eq_integral]
      simp
  have hrealAc : AbsolutelyContinuousOnInterval (fun t => (H t).re) a b := by
    let R : ℂ →L[ℝ] ℝ := Complex.reCLM
    have hR : AbsolutelyContinuousOnInterval (fun _ : ℝ => R) a b := by
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => R)).contDiffOn
        |>.absolutelyContinuousOnInterval
    simpa [R] using AbsolutelyContinuousOnInterval.clm_apply hHac hR
      (ContinuousLinearMap.apply ℝ ℝ)
  have himagAc : AbsolutelyContinuousOnInterval (fun t => (H t).im) a b := by
    let R : ℂ →L[ℝ] ℝ := Complex.imCLM
    have hR : AbsolutelyContinuousOnInterval (fun _ : ℝ => R) a b := by
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => R)).contDiffOn
        |>.absolutelyContinuousOnInterval
    simpa [R] using AbsolutelyContinuousOnInterval.clm_apply hHac hR
      (ContinuousLinearMap.apply ℝ ℝ)
  have hrealInt := hrealAc.integral_deriv_eq_sub
  have himagInt := himagAc.integral_deriv_eq_sub
  rw [hzero.1, hzero.2] at hrealInt himagInt
  simp only [Complex.zero_re, sub_self] at hrealInt
  simp only [Complex.zero_im, sub_self] at himagInt
  have hformula : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      deriv H t =
        (-Complex.I) * eta t *
            bilinearL2Two (exteriorSourceCurve sigma u v t)
              (q.toLp 2 (volume.prod volume)) +
          deriv (eta : ℝ → ℂ) t *
            bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
              (q.toLp 2 (volume.prod volume)) +
          Complex.I * eta t *
            bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
              ((pairLaplacian q).toLp 2 (volume.prod volume)) := by
    filter_upwards [hHderiv] with t ht htI
    rw [ht htI |>.deriv]
    dsimp [W, B]
    rw [bilinearL2Two_add_right, bilinearL2Two_smul_left,
      bilinearL2Two_smul_right, bilinearL2Two_smul_right,
      bilinearL2Two_smul_right, bilinearL2Two_smul_right,
      bilinearL2Two_transport_cancel,
      bilinearL2Two_transport_cancel,
      bilinearL2Two_transport_cancel]
    ring
  have hformula' : ∀ᵐ t : ℝ, t ∈ Set.uIoc a b →
      deriv H t =
        (-Complex.I) * eta t *
            bilinearL2Two (exteriorSourceCurve sigma u v t)
              (q.toLp 2 (volume.prod volume)) +
          deriv (eta : ℝ → ℂ) t *
            bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
              (q.toLp 2 (volume.prod volume)) +
          Complex.I * eta t *
            bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
              ((pairLaplacian q).toLp 2 (volume.prod volume)) :=
    hformula.mono (fun t ht htI => ht (Set.uIoc_subset_uIcc htI))
  let D : ℝ → ℂ := fun t =>
    (-Complex.I) * eta t *
        bilinearL2Two (exteriorSourceCurve sigma u v t)
          (q.toLp 2 (volume.prod volume)) +
      deriv (eta : ℝ → ℂ) t *
        bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
          (q.toLp 2 (volume.prod volume)) +
      Complex.I * eta t *
        bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
          ((pairLaplacian q).toLp 2 (volume.prod volume))
  have hsource : IntervalIntegrable (fun t =>
      bilinearL2Two (exteriorSourceCurve sigma u v t)
        (q.toLp 2 (volume.prod volume))) volume a b := by
    let L := bilinearL2TwoLeftCLM (q.toLp 2 (volume.prod volume))
    have hs := exteriorSourceCurve_intervalIntegrable sigma u v a b
    exact ⟨L.integrable_comp hs.1, L.integrable_comp hs.2⟩
  have hE0 : Continuous (fun t =>
      bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
        (q.toLp 2 (volume.prod volume))) := by
    exact (bilinearL2TwoLeftCLM
      (q.toLp 2 (volume.prod volume))).continuous.comp
        (continuous_exteriorProductL2 u.u v.u u.continuous v.continuous)
  have hE2 : Continuous (fun t =>
      bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
        ((pairLaplacian q).toLp 2 (volume.prod volume))) := by
    exact (bilinearL2TwoLeftCLM
      ((pairLaplacian q).toLp 2 (volume.prod volume))).continuous.comp
        (continuous_exteriorProductL2 u.u v.u u.continuous v.continuous)
  have hDint : IntervalIntegrable D volume a b := by
    dsimp [D]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (((hsource.const_mul (-Complex.I)).mul_continuousOn
        eta.continuous.continuousOn).add
      (((eta.smooth 1).continuous_deriv (by simp)).continuousOn.intervalIntegrable.mul_continuousOn
        hE0.continuousOn)).add
      ((eta.continuous.continuousOn.const_mul Complex.I).intervalIntegrable.mul_continuousOn
        hE2.continuousOn)
  have hDzero : (∫ t in a..b, D t) = 0 := by
    apply Complex.ext
    · change RCLike.re (∫ t in a..b, D t) = RCLike.re (0 : ℂ)
      rw [← intervalIntegral.intervalIntegral_re hDint]
      change (∫ t in a..b, (D t).re) = 0
      calc
        (∫ t in a..b, (D t).re) =
            ∫ t in a..b, deriv (fun s => (H s).re) t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hformula', hHderiv] with t ht hHt htI
          have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
            (hHt (Set.uIoc_subset_uIcc htI))).deriv
          change deriv (fun s => (H s).re) t = _ at hre
          calc
            (D t).re = (deriv H t).re :=
              congrArg Complex.re ((ht htI).symm)
            _ = _ := by
              rw [(hHt (Set.uIoc_subset_uIcc htI)).deriv]
              exact hre.symm
        _ = 0 := hrealInt
    · change RCLike.im (∫ t in a..b, D t) = RCLike.im (0 : ℂ)
      rw [← intervalIntegral.intervalIntegral_im hDint]
      change (∫ t in a..b, (D t).im) = 0
      calc
        (∫ t in a..b, (D t).im) =
            ∫ t in a..b, deriv (fun s => (H s).im) t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hformula', hHderiv] with t ht hHt htI
          have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
            (hHt (Set.uIoc_subset_uIcc htI))).deriv
          change deriv (fun s => (H s).im) t = _ at him
          calc
            (D t).im = (deriv H t).im :=
              congrArg Complex.im ((ht htI).symm)
            _ = _ := by
              rw [(hHt (Set.uIoc_subset_uIcc htI)).deriv]
              exact him.symm
        _ = 0 := himagInt
  have hscaled := congrArg (fun z : ℂ => -Complex.I * z) hDzero
  simp only [mul_zero] at hscaled
  rw [← intervalIntegral.integral_const_mul] at hscaled
  let L : ℝ → ℂ := fun t =>
    (-Complex.I * deriv (eta : ℝ → ℂ) t) *
        bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
          (q.toLp 2 (volume.prod volume)) +
      eta t * bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
        ((pairLaplacian q).toLp 2 (volume.prod volume))
  let R : ℝ → ℂ := fun t =>
    eta t * bilinearL2Two (exteriorSourceCurve sigma u v t)
      (q.toLp 2 (volume.prod volume))
  have hLint : IntervalIntegrable L volume a b := by
    dsimp [L]
    exact (((eta.smooth 1).continuous_deriv (by simp)).const_mul
      (-Complex.I)).mul hE0 |>.add (eta.continuous.mul hE2)
      |>.continuousOn.intervalIntegrable
  have hRint : IntervalIntegrable R volume a b := by
    dsimp [R]
    simpa only [mul_comm] using
      hsource.mul_continuousOn eta.continuous.continuousOn
  have hscaled' : (∫ t in a..b, L t - R t) = 0 := by
    calc
      (∫ t in a..b, L t - R t) = ∫ t in a..b, -Complex.I * D t := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [L, R, D]
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = 0 := hscaled
  rw [intervalIntegral.integral_sub hLint hRint] at hscaled'
  have hLR := sub_eq_zero.mp hscaled'
  simpa only [L, R, bilinearL2Two_add_right,
    bilinearL2Two_smul_right, smul_eq_mul] using hLR

/-- Global form of `physical_exterior_separated_interval` for a compactly
supported temporal factor.  This is the form used when separated tests are
viewed as genuine spacetime test functions. -/
theorem physical_exterior_separated (sigma : ℝ)
    (u v : GlobalSolution sigma) (eta : SchwartzMap ℝ ℂ)
    (q : SchwartzMap (ℝ × ℝ) ℂ)
    (heta : HasCompactSupport (eta : ℝ → ℂ)) :
    (∫ t, bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
      ((-Complex.I * deriv (eta : ℝ → ℂ) t) •
          q.toLp 2 (volume.prod volume) +
        eta t • (pairLaplacian q).toLp 2 (volume.prod volume))) =
      ∫ t, bilinearL2Two (exteriorSourceCurve sigma u v t)
        (eta t • q.toLp 2 (volume.prod volume)) := by
  rcases heta.isCompact.bddBelow with ⟨c, hc⟩
  rcases heta.isCompact.bddAbove with ⟨d, hd⟩
  let a : ℝ := min c d - 1
  let b : ℝ := max c d + 1
  have hab : a < b := by
    dsimp [a, b]
    linarith [(min_le_max : min c d ≤ max c d)]
  have hsupp : tsupport (eta : ℝ → ℂ) ⊆ Set.Ioo a b := by
    intro t ht
    have hct : c ≤ t := hc ht
    have htd : t ≤ d := hd ht
    dsimp [a, b]
    constructor
    · linarith [min_le_left c d]
    · linarith [le_max_right c d]
  have hetazero (t : ℝ) (ht : t ∉ Set.Ioc a b) : eta t = 0 := by
    by_contra hn
    have ht' := hsupp (subset_tsupport _ hn)
    exact ht ⟨ht'.1, ht'.2.le⟩
  have hderivzero (t : ℝ) (ht : t ∉ Set.Ioc a b) :
      deriv (eta : ℝ → ℂ) t = 0 := by
    by_contra hn
    have ht' : t ∈ tsupport (eta : ℝ → ℂ) :=
      tsupport_deriv_subset (subset_tsupport _ hn)
    have hs := hsupp ht'
    exact ht ⟨hs.1, hs.2.le⟩
  have hetaa : eta a = 0 := hetazero a (by simp)
  have hetab : eta b = 0 := by
    by_contra hn
    exact (hsupp (subset_tsupport _ hn)).2.false
  let L : ℝ → ℂ := fun t =>
    bilinearL2Two (exteriorProductL2 (u.u t) (v.u t))
      ((-Complex.I * deriv (eta : ℝ → ℂ) t) •
          q.toLp 2 (volume.prod volume) +
        eta t • (pairLaplacian q).toLp 2 (volume.prod volume))
  let R : ℝ → ℂ := fun t =>
    bilinearL2Two (exteriorSourceCurve sigma u v t)
      (eta t • q.toLp 2 (volume.prod volume))
  have hLzero (t : ℝ) (ht : t ∉ Set.Ioc a b) : L t = 0 := by
    dsimp [L]
    rw [hetazero t ht, hderivzero t ht]
    simp only [mul_zero, zero_smul, add_zero]
    rw [bilinearL2Two_eq_integral]
    simp
  have hRzero (t : ℝ) (ht : t ∉ Set.Ioc a b) : R t = 0 := by
    dsimp [R]
    rw [hetazero t ht, zero_smul, bilinearL2Two_eq_integral]
    simp
  have hLglobal : (∫ t, L t) = ∫ t in a..b, L t := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hLzero).symm
  have hRglobal : (∫ t, R t) = ∫ t in a..b, R t := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hRzero).symm
  change (∫ t, L t) = ∫ t, R t
  rw [hLglobal, hRglobal]
  exact physical_exterior_separated_interval sigma u v eta q hetaa hetab

end CubicNLSPhaseRetrieval
