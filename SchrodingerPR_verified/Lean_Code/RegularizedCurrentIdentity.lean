import Lean_Code.RegularizedSpatialDerivative
import Lean_Code.RegularizedMass

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology ComplexConjugate
open LineDeriv

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- The Fourier symbol of the second spatial derivative after resolvent
smoothing. -/
def regularizedSecondDerivativeSymbol (n : ℕ) (ξ : ℝ) : ℂ :=
  ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) * resolventSymbol n ξ

lemma continuous_regularizedSecondDerivativeSymbol (n : ℕ) :
    Continuous (regularizedSecondDerivativeSymbol n) := by
  unfold regularizedSecondDerivativeSymbol
  have hreal : Continuous (fun ξ : ℝ => -(4 * Real.pi ^ 2 * ξ ^ 2)) := by
    fun_prop
  exact (Complex.continuous_ofReal.comp hreal).mul
    (continuous_resolventSymbol n)

lemma norm_regularizedSecondDerivativeSymbol_le (n : ℕ) (ξ : ℝ) :
    ‖regularizedSecondDerivativeSymbol n ξ‖ ≤
      4 * Real.pi ^ 2 * (n + 1 : ℝ) := by
  rw [regularizedSecondDerivativeSymbol, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_neg]
  have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hden : 0 < 1 + ξ ^ 2 / (n + 1 : ℝ) := by positivity
  have hr : ‖resolventSymbol n ξ‖ =
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ := by
    rw [resolventSymbol, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hden]
  rw [hr, abs_mul, abs_of_nonneg hpi, abs_pow]
  have hq : ξ ^ 2 * (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ ≤
      (n + 1 : ℝ) := by
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hden]
    calc
      ξ ^ 2 ≤ (n + 1 : ℝ) + ξ ^ 2 := by
        nlinarith [show 0 ≤ (n : ℝ) by positivity]
      _ = (n + 1 : ℝ) * (1 + ξ ^ 2 / (n + 1 : ℝ)) := by
        field_simp
  calc
    4 * Real.pi ^ 2 * |ξ| ^ 2 *
        (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ =
        (4 * Real.pi ^ 2) *
          (ξ ^ 2 * (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹) := by
            rw [sq_abs]
            ring
    _ ≤ (4 * Real.pi ^ 2) * (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hq hpi

/-- The physical second derivative of a resolvent-smoothed `L²` function. -/
def frequencySmoothSecondDerivativeCLM (n : ℕ) : L2 →L[ℂ] L2 :=
  fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM (regularizedSecondDerivativeSymbol n)
      (continuous_regularizedSecondDerivativeSymbol n)
      (4 * Real.pi ^ 2 * (n + 1 : ℝ)) (by positivity)
      (norm_regularizedSecondDerivativeSymbol_le n)).comp
        fourierL2.toContinuousLinearEquiv.toContinuousLinearMap)

lemma fourier_frequencySmoothSecondDerivativeCLM (n : ℕ) (f : L2) :
    fourierL2 (frequencySmoothSecondDerivativeCLM n f) =
      boundedMulCLM (regularizedSecondDerivativeSymbol n)
        (continuous_regularizedSecondDerivativeSymbol n)
        (4 * Real.pi ^ 2 * (n + 1 : ℝ)) (by positivity)
        (norm_regularizedSecondDerivativeSymbol_le n) (fourierL2 f) := by
  simp [frequencySmoothSecondDerivativeCLM]

lemma coe_fourier_frequencySmoothSecondDerivativeCLM (n : ℕ) (f : L2) :
    (fourierL2 (frequencySmoothSecondDerivativeCLM n f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) *
        (fourierL2 (frequencySmoothCLM n f) : ℝ → ℂ) ξ := by
  rw [fourier_frequencySmoothSecondDerivativeCLM]
  filter_upwards [coe_boundedMulCLM (regularizedSecondDerivativeSymbol n)
      (continuous_regularizedSecondDerivativeSymbol n)
      (4 * Real.pi ^ 2 * (n + 1 : ℝ)) (by positivity)
      (norm_regularizedSecondDerivativeSymbol_le n) (fourierL2 f),
    coe_fourier_frequencySmoothCLM n f] with ξ h2 hw
  rw [h2, hw]
  simp [regularizedSecondDerivativeSymbol]
  ring

/-- The strong free-generator term in the regularized NLS equation is exactly
`i` times the physical second derivative. -/
lemma regularizedGenerator_eq_i_second (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (t : ℝ) :
    freePropDerivative (regularizedInteraction n u t)
        (regularizedInteraction_generator_memLp n u t) t =
      Complex.I • frequencySmoothSecondDerivativeCLM n (u.u t) := by
  apply fourierL2.injective
  rw [map_smul]
  apply Lp.ext
  have hto := (generator_symbol_mul_memLp
      (fourierL2 (regularizedInteraction n u t))
      (regularizedInteraction_generator_memLp n u t) t).coeFn_toLp
  have hsecond := coe_fourier_frequencySmoothSecondDerivativeCLM n (u.u t)
  have hsmul := Lp.coeFn_smul Complex.I
    (fourierL2 (frequencySmoothSecondDerivativeCLM n (u.u t)))
  have horbit := congrArg fourierL2
    (freeProp_regularizedInteraction n u t)
  have horbitAe :
      (fourierL2 (freeProp t (regularizedInteraction n u t)) : ℝ → ℂ) =ᵐ[volume]
        (fourierL2 (frequencySmoothCLM n (u.u t)) : ℝ → ℂ) :=
    Filter.Eventually.of_forall fun ξ => congrArg
      (fun z : L2 => (z : ℝ → ℂ) ξ) horbit
  filter_upwards [hto, hsecond, hsmul,
    fourier_freeProp t (regularizedInteraction n u t), horbitAe]
      with ξ hto hsecond hsmul hfree horbit
  rw [freePropDerivative, LinearIsometryEquiv.apply_symm_apply]
  rw [hto, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsecond, ← horbit, hfree]
  change (((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) * Complex.I) *
      schrodingerSymbol t ξ *
        (fourierL2 (regularizedInteraction n u t) : ℝ → ℂ) ξ = _
  push_cast
  ring

lemma hasTemperateGrowth_resolventSymbol (n : ℕ) :
    Function.HasTemperateGrowth (resolventSymbol n) := by
  let L : ℝ →L[ℝ] ℝ :=
    (Real.sqrt (n + 1 : ℝ))⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have hLfun : (fun ξ : ℝ => ξ / Real.sqrt (n + 1 : ℝ)) = L := by
    funext ξ
    simp [L, div_eq_mul_inv, mul_comm]
  have hinner : Function.HasTemperateGrowth
      (fun ξ : ℝ => ξ / Real.sqrt (n + 1 : ℝ)) := by
    rw [hLfun]
    exact L.hasTemperateGrowth
  have houter : Function.HasTemperateGrowth (fun x : ℝ =>
      (((1 + ‖x‖ ^ 2) ^ (-1 : ℝ) : ℝ) : ℂ)) := by
    fun_prop
  have hcomp := houter.comp hinner
  have heq : resolventSymbol n = fun ξ : ℝ =>
      (((1 + ‖ξ / Real.sqrt (n + 1 : ℝ)‖ ^ 2) ^
        (-1 : ℝ) : ℝ) : ℂ) := by
    funext ξ
    rw [resolventSymbol]
    have hr : (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ =
        (1 + ‖ξ / Real.sqrt (n + 1 : ℝ)‖ ^ 2) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      congr 2
      rw [Real.norm_eq_abs, sq_abs, div_pow,
        Real.sq_sqrt (by positivity)]
    exact_mod_cast hr
  rw [heq]
  exact hcomp

/-- Resolvent smoothing preserves the Schwartz class. -/
def frequencySmoothSchwartz (n : ℕ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (resolventSymbol n)

lemma fourier_frequencySmoothSchwartz_apply (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (𝓕 (frequencySmoothSchwartz n φ)) ξ =
      resolventSymbol n ξ * (𝓕 φ) ξ := by
  rw [frequencySmoothSchwartz,
    SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]
  exact SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_resolventSymbol n) (𝓕 φ) ξ

lemma coe_fourierL2_schwartz_public (φ : SchwartzMap ℝ ℂ) :
    (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (𝓕 φ) ξ := by
  have hfourier : fourierL2 (φ.toLp 2 volume) =
      (𝓕 φ).toLp 2 volume := by
    unfold fourierL2
    exact SchwartzMap.toLp_fourier_eq φ
  rw [hfourier]
  exact MemLp.coeFn_toLp ((𝓕 φ).memLp 2 volume)

lemma frequencySmoothCLM_schwartz (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    frequencySmoothCLM n (φ.toLp 2 volume) =
      (frequencySmoothSchwartz n φ).toLp 2 volume := by
  apply fourierL2.injective
  apply Lp.ext
  filter_upwards [coe_fourier_frequencySmoothCLM n (φ.toLp 2 volume),
    coe_fourierL2_schwartz_public φ,
    coe_fourierL2_schwartz_public (frequencySmoothSchwartz n φ)]
      with ξ hleft hφ hright
  rw [hleft, hφ, hright, fourier_frequencySmoothSchwartz_apply]

lemma frequencySmoothDerivativeCLM_schwartz (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) :
    frequencySmoothDerivativeCLM n (φ.toLp 2 volume) =
      ((SchwartzMap.derivCLM ℂ ℂ) (frequencySmoothSchwartz n φ)).toLp
        2 volume := by
  apply fourierL2.injective
  apply Lp.ext
  let w := frequencySmoothSchwartz n φ
  have hfreq : fourierL2 (frequencySmoothCLM n (φ.toLp 2 volume)) =
      fourierL2 (w.toLp 2 volume) := congrArg fourierL2
    (frequencySmoothCLM_schwartz n φ)
  have hfreqAe :
      (fourierL2 (frequencySmoothCLM n (φ.toLp 2 volume)) : ℝ → ℂ) =ᵐ[volume]
        (fourierL2 (w.toLp 2 volume) : ℝ → ℂ) :=
    Filter.Eventually.of_forall fun ξ => congrArg
      (fun z : L2 => (z : ℝ → ℂ) ξ) hfreq
  filter_upwards [coe_fourier_frequencySmoothDerivativeCLM n
      (φ.toLp 2 volume),
    coe_fourierL2_schwartz_public
      ((SchwartzMap.derivCLM ℂ ℂ) (frequencySmoothSchwartz n φ)),
    coe_fourierL2_schwartz_public w, hfreqAe]
      with ξ hleft hright hw hfreq
  rw [hleft, hright, hfreq, hw]
  have hd := Real.fourier_deriv (frequencySmoothSchwartz n φ).integrable
    (frequencySmoothSchwartz n φ).differentiable
    ((SchwartzMap.derivCLM ℂ ℂ) (frequencySmoothSchwartz n φ)).integrable
  change _ = 𝓕 (deriv (frequencySmoothSchwartz n φ : ℝ → ℂ)) ξ
  rw [congrFun hd ξ]
  simp [SchwartzMap.fourier_coe]
  ring

lemma frequencySmoothSecondDerivativeCLM_schwartz (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) :
    frequencySmoothSecondDerivativeCLM n (φ.toLp 2 volume) =
      ((SchwartzMap.derivCLM ℂ ℂ)
        ((SchwartzMap.derivCLM ℂ ℂ)
          (frequencySmoothSchwartz n φ))).toLp 2 volume := by
  apply fourierL2.injective
  apply Lp.ext
  let w := frequencySmoothSchwartz n φ
  let w' := (SchwartzMap.derivCLM ℂ ℂ) w
  let w'' := (SchwartzMap.derivCLM ℂ ℂ) w'
  have h1 := Real.fourier_deriv w.integrable w.differentiable w'.integrable
  have h2 := Real.fourier_deriv w'.integrable w'.differentiable w''.integrable
  have hfreq : fourierL2 (frequencySmoothCLM n (φ.toLp 2 volume)) =
      fourierL2 (w.toLp 2 volume) := congrArg fourierL2
    (frequencySmoothCLM_schwartz n φ)
  have hfreqAe :
      (fourierL2 (frequencySmoothCLM n (φ.toLp 2 volume)) : ℝ → ℂ) =ᵐ[volume]
        (fourierL2 (w.toLp 2 volume) : ℝ → ℂ) :=
    Filter.Eventually.of_forall fun ξ => congrArg
      (fun z : L2 => (z : ℝ → ℂ) ξ) hfreq
  filter_upwards [coe_fourier_frequencySmoothSecondDerivativeCLM n
      (φ.toLp 2 volume), coe_fourierL2_schwartz_public w,
    coe_fourierL2_schwartz_public w'', hfreqAe]
      with ξ hleft hw hright hfreq
  change (fourierL2 (frequencySmoothSecondDerivativeCLM n
      (φ.toLp 2 volume)) : ℝ → ℂ) ξ =
    (fourierL2 (w''.toLp 2 volume) : ℝ → ℂ) ξ
  rw [hleft, hfreq, hw, hright]
  change ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) * (𝓕 w) ξ =
    (𝓕 w'') ξ
  change _ = 𝓕 (deriv (w' : ℝ → ℂ)) ξ
  rw [congrFun h2 ξ]
  change _ = (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) *
    𝓕 (deriv (w : ℝ → ℂ)) ξ
  rw [congrFun h1 ξ]
  rw [SchwartzMap.fourier_coe]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma hasTemperateGrowth_spatialPrimitive (φ : SchwartzMap ℝ ℂ) :
    Function.HasTemperateGrowth (spatialPrimitive φ) := by
  apply Function.HasTemperateGrowth.of_fderiv (k := 0)
    (C := spatialPrimitiveBound φ)
  · have heq : fderiv ℝ (spatialPrimitive φ) = fun x =>
        ContinuousLinearMap.toSpanSingleton ℝ (φ x) := by
      funext x
      exact (hasDerivAt_spatialPrimitive φ x).hasFDerivAt.fderiv
    rw [heq]
    have hφ : Function.HasTemperateGrowth (φ : ℝ → ℂ) :=
      φ.hasTemperateGrowth
    exact (ContinuousLinearMap.toSpanSingletonCLE :
      ℂ ≃L[ℝ] (ℝ →L[ℝ] ℂ)).hasTemperateGrowth.comp hφ
  · exact fun x => (hasDerivAt_spatialPrimitive φ x).differentiableAt
  · intro x
    simpa using norm_spatialPrimitive_le φ x

private def primitiveMulSchwartz (φ w : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (spatialPrimitive φ) w

@[simp] private lemma primitiveMulSchwartz_apply
    (φ w : SchwartzMap ℝ ℂ) (x : ℝ) :
    primitiveMulSchwartz φ w x = spatialPrimitive φ x * w x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_spatialPrimitive φ) w x

private lemma deriv_primitiveMulSchwartz (φ w : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (primitiveMulSchwartz φ w : ℝ → ℂ) x =
      φ x * w x + spatialPrimitive φ x * deriv (w : ℝ → ℂ) x := by
  have heq : (primitiveMulSchwartz φ w : ℝ → ℂ) =
      fun y => spatialPrimitive φ y * w y := by
    funext y
    exact primitiveMulSchwartz_apply φ w y
  rw [heq]
  exact ((hasDerivAt_spatialPrimitive φ x).mul
    w.differentiableAt.hasDerivAt).deriv

private lemma deriv_conjSchwartz (w : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (conjSchwartz w : ℝ → ℂ) x =
      conj (deriv (w : ℝ → ℂ) x) := by
  exact w.differentiableAt.hasDerivAt.star.deriv

private def schwartzMul (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (f : ℝ → ℂ) g

@[simp] private lemma schwartzMul_apply (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzMul f g x = f x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth g x

/-- The integration-by-parts identity behind the regularized continuity
equation, proved on the Schwartz core. -/
private lemma schwartz_second_derivative_current_identity
    (φ w : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, conj (w x) * spatialPrimitive φ x *
        (Complex.I * iteratedDeriv 2 (w : ℝ → ℂ) x)) +
      (∫ x : ℝ, conj (Complex.I * iteratedDeriv 2 (w : ℝ → ℂ) x) *
        spatialPrimitive φ x * w x) =
      Complex.I *
        ((∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) * φ x * w x) -
          ∫ x : ℝ, deriv (w : ℝ → ℂ) x * φ x * conj (w x)) := by
  let w' := (SchwartzMap.derivCLM ℂ ℂ) w
  let w'' := (SchwartzMap.derivCLM ℂ ℂ) w'
  let awbar := primitiveMulSchwartz φ (conjSchwartz w)
  let aw := primitiveMulSchwartz φ w
  have hw' (x : ℝ) : w' x = deriv (w : ℝ → ℂ) x := rfl
  have hw'' (x : ℝ) : w'' x = iteratedDeriv 2 (w : ℝ → ℂ) x := by
    rw [show iteratedDeriv 2 (w : ℝ → ℂ) =
      deriv (deriv (w : ℝ → ℂ)) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num,
          iteratedDeriv_succ, iteratedDeriv_one]]
    rfl
  have hawbar (x : ℝ) : awbar x =
      spatialPrimitive φ x * conj (w x) := by
    simp [awbar, primitiveMulSchwartz_apply]
  have haw (x : ℝ) : aw x = spatialPrimitive φ x * w x := by
    simp [aw, primitiveMulSchwartz_apply]
  have hdawbar (x : ℝ) : deriv (awbar : ℝ → ℂ) x =
      φ x * conj (w x) +
        spatialPrimitive φ x * conj (deriv (w : ℝ → ℂ) x) := by
    rw [show deriv (awbar : ℝ → ℂ) x =
      deriv (primitiveMulSchwartz φ (conjSchwartz w) : ℝ → ℂ) x by rfl,
      deriv_primitiveMulSchwartz, deriv_conjSchwartz]
    simp
  have hdaw (x : ℝ) : deriv (aw : ℝ → ℂ) x =
      φ x * w x + spatialPrimitive φ x * deriv (w : ℝ → ℂ) x := by
    rw [show deriv (aw : ℝ → ℂ) x =
      deriv (primitiveMulSchwartz φ w : ℝ → ℂ) x by rfl,
      deriv_primitiveMulSchwartz]
  have hibp1 := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul awbar w'
  have hibp2 := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul
    (conjSchwartz w') aw
  have hintF : Integrable (fun x : ℝ =>
      deriv (w : ℝ → ℂ) x * φ x * conj (w x)) := by
    have h : Integrable
        (schwartzMul (schwartzMul w' φ) (conjSchwartz w) : ℝ → ℂ)
        volume :=
      (schwartzMul (schwartzMul w' φ) (conjSchwartz w)).integrable
    apply h.congr
    filter_upwards with x
    rw [schwartzMul_apply, schwartzMul_apply, conjSchwartz_apply, hw']
  have hintR : Integrable (fun x : ℝ =>
      conj (deriv (w : ℝ → ℂ) x) * φ x * w x) := by
    have h : Integrable
        (schwartzMul (schwartzMul (conjSchwartz w') φ) w : ℝ → ℂ)
        volume :=
      (schwartzMul (schwartzMul (conjSchwartz w') φ) w).integrable
    apply h.congr
    filter_upwards with x
    rw [schwartzMul_apply, schwartzMul_apply, conjSchwartz_apply, hw']
  have hintE : Integrable (fun x : ℝ =>
      conj (deriv (w : ℝ → ℂ) x) * spatialPrimitive φ x *
        deriv (w : ℝ → ℂ) x) := by
    have h : Integrable
        (schwartzMul (conjSchwartz w')
          (primitiveMulSchwartz φ w') : ℝ → ℂ) volume :=
      (schwartzMul (conjSchwartz w')
        (primitiveMulSchwartz φ w')).integrable
    apply h.congr
    filter_upwards with x
    rw [schwartzMul_apply, conjSchwartz_apply,
      primitiveMulSchwartz_apply, hw']
    ring
  have h1 :
      (∫ x : ℝ, spatialPrimitive φ x * conj (w x) *
          iteratedDeriv 2 (w : ℝ → ℂ) x) =
        -((∫ x : ℝ, deriv (w : ℝ → ℂ) x * φ x * conj (w x)) +
          ∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) *
            spatialPrimitive φ x * deriv (w : ℝ → ℂ) x) := by
    have hleft :
        (∫ x : ℝ, awbar x * deriv (w' : ℝ → ℂ) x) =
          ∫ x : ℝ, spatialPrimitive φ x * conj (w x) *
            iteratedDeriv 2 (w : ℝ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hawbar]
      change spatialPrimitive φ x * conj (w x) * w'' x = _
      rw [hw'']
    have hright :
        (∫ x : ℝ, deriv (awbar : ℝ → ℂ) x * w' x) =
          ∫ x : ℝ,
            (deriv (w : ℝ → ℂ) x * φ x * conj (w x) +
              conj (deriv (w : ℝ → ℂ) x) *
                spatialPrimitive φ x * deriv (w : ℝ → ℂ) x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hdawbar, hw']
      ring
    rw [hleft, hright, integral_add hintF hintE] at hibp1
    exact hibp1
  have h2 :
      (∫ x : ℝ, conj (iteratedDeriv 2 (w : ℝ → ℂ) x) *
          spatialPrimitive φ x * w x) =
        -((∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) * φ x * w x) +
          ∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) *
            spatialPrimitive φ x * deriv (w : ℝ → ℂ) x) := by
    have hleft :
        (∫ x : ℝ, conjSchwartz w' x * deriv (aw : ℝ → ℂ) x) =
          ∫ x : ℝ,
            (conj (deriv (w : ℝ → ℂ) x) * φ x * w x +
              conj (deriv (w : ℝ → ℂ) x) *
                spatialPrimitive φ x * deriv (w : ℝ → ℂ) x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [conjSchwartz_apply, hw', hdaw]
      ring
    have hright :
        (∫ x : ℝ, deriv (conjSchwartz w' : ℝ → ℂ) x * aw x) =
          ∫ x : ℝ, conj (iteratedDeriv 2 (w : ℝ → ℂ) x) *
            spatialPrimitive φ x * w x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [deriv_conjSchwartz, haw]
      change conj (w'' x) * (spatialPrimitive φ x * w x) = _
      rw [hw'']
      ring
    rw [hleft, hright, integral_add hintR hintE] at hibp2
    linear_combination hibp2
  have hgen1 :
      (∫ x : ℝ, conj (w x) * spatialPrimitive φ x *
        (Complex.I * iteratedDeriv 2 (w : ℝ → ℂ) x)) =
        Complex.I * (∫ x : ℝ, spatialPrimitive φ x * conj (w x) *
          iteratedDeriv 2 (w : ℝ → ℂ) x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hgen2 :
      (∫ x : ℝ, conj (Complex.I * iteratedDeriv 2 (w : ℝ → ℂ) x) *
        spatialPrimitive φ x * w x) =
        -Complex.I * (∫ x : ℝ, conj (iteratedDeriv 2 (w : ℝ → ℂ) x) *
          spatialPrimitive φ x * w x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [map_mul, Complex.conj_I]
    ring
  rw [hgen1, hgen2]
  linear_combination Complex.I * h1 - Complex.I * h2

/-- The two first-order currents occurring in the regularized continuity
equation.  Both are written as Hilbert-space pairings so that their
continuity on `L²` is immediate. -/
def regularizedForwardCurrent (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ (conjL2 (frequencySmoothDerivativeCLM n f))
    (cutoffL2CLM φ (conjL2 (frequencySmoothCLM n f)))

def regularizedReverseCurrent (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ (frequencySmoothDerivativeCLM n f)
    (cutoffL2CLM φ (frequencySmoothCLM n f))

/-- The free-generator part of the differentiated density moment, expressed
only in terms of bounded operators on the initial `L²` datum. -/
def regularizedGeneratorForm (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ (frequencySmoothCLM n f)
      (spatialPrimitiveMulCLM φ
        (Complex.I • frequencySmoothSecondDerivativeCLM n f)) +
    inner ℂ (Complex.I • frequencySmoothSecondDerivativeCLM n f)
      (spatialPrimitiveMulCLM φ (frequencySmoothCLM n f))

lemma continuous_regularizedForwardCurrent (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun f : L2 => regularizedForwardCurrent n f φ) := by
  unfold regularizedForwardCurrent conjL2
  apply Continuous.inner
  · exact (Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume).continuous.comp
      (frequencySmoothDerivativeCLM n).continuous
  · exact (cutoffL2CLM φ).continuous.comp
      ((Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume).continuous.comp
        (frequencySmoothCLM n).continuous)

lemma continuous_regularizedReverseCurrent (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun f : L2 => regularizedReverseCurrent n f φ) := by
  unfold regularizedReverseCurrent
  exact Continuous.inner (frequencySmoothDerivativeCLM n).continuous
    ((cutoffL2CLM φ).continuous.comp (frequencySmoothCLM n).continuous)

lemma continuous_regularizedGeneratorForm (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun f : L2 => regularizedGeneratorForm n f φ) := by
  unfold regularizedGeneratorForm
  apply Continuous.add
  · apply Continuous.inner
    · exact (frequencySmoothCLM n).continuous
    · exact (spatialPrimitiveMulCLM φ).continuous.comp
        ((frequencySmoothSecondDerivativeCLM n).continuous.const_smul Complex.I)
  · apply Continuous.inner
    · exact (frequencySmoothSecondDerivativeCLM n).continuous.const_smul Complex.I
    · exact (spatialPrimitiveMulCLM φ).continuous.comp
        (frequencySmoothCLM n).continuous

private lemma conjL2_schwartz (f : SchwartzMap ℝ ℂ) :
    conjL2 (f.toLp 2 volume) = (conjSchwartz f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [Complex.conjLIE.toContinuousLinearMap.coeFn_compLpL
      (f.toLp 2 volume), f.coeFn_toLp 2 volume,
    (conjSchwartz f).coeFn_toLp 2 volume] with x hc hf hout
  rw [conjL2, hc, hf, hout, conjSchwartz_apply]
  rfl

private lemma cutoffL2CLM_schwartz (φ f : SchwartzMap ℝ ℂ) :
    cutoffL2CLM φ (f.toLp 2 volume) =
      (schwartzMul φ f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [coe_cutoffL2CLM φ (f.toLp 2 volume),
    f.coeFn_toLp 2 volume, (schwartzMul φ f).coeFn_toLp 2 volume]
      with x hcut hf hout
  rw [hcut, hf, hout, schwartzMul_apply]

private lemma regularizedGeneratorForm_schwartz (n : ℕ)
    (f φ : SchwartzMap ℝ ℂ) :
    regularizedGeneratorForm n (f.toLp 2 volume) φ =
      Complex.I *
        (regularizedReverseCurrent n (f.toLp 2 volume) φ -
          regularizedForwardCurrent n (f.toLp 2 volume) φ) := by
  let w := frequencySmoothSchwartz n f
  let w' := (SchwartzMap.derivCLM ℂ ℂ) w
  let w'' := (SchwartzMap.derivCLM ℂ ℂ) w'
  have hw : frequencySmoothCLM n (f.toLp 2 volume) =
      w.toLp 2 volume := frequencySmoothCLM_schwartz n f
  have hw' : frequencySmoothDerivativeCLM n (f.toLp 2 volume) =
      w'.toLp 2 volume := frequencySmoothDerivativeCLM_schwartz n f
  have hw'' : frequencySmoothSecondDerivativeCLM n (f.toLp 2 volume) =
      w''.toLp 2 volume := frequencySmoothSecondDerivativeCLM_schwartz n f
  rw [regularizedGeneratorForm, regularizedReverseCurrent,
    regularizedForwardCurrent, hw, hw', hw'', conjL2_schwartz,
    conjL2_schwartz, cutoffL2CLM_schwartz, cutoffL2CLM_schwartz,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hMw := coe_spatialPrimitiveMulCLM φ
    (Complex.I • w''.toLp 2 volume)
  have hM0 := coe_spatialPrimitiveMulCLM φ (w.toLp 2 volume)
  have hsmul := Lp.coeFn_smul Complex.I (w''.toLp 2 volume)
  have hwcoe := w.coeFn_toLp 2 volume
  have hwpcoe := w'.coeFn_toLp 2 volume
  have hwppcoe := w''.coeFn_toLp 2 volume
  have hcw := (conjSchwartz w).coeFn_toLp 2 volume
  have hcwp := (conjSchwartz w').coeFn_toLp 2 volume
  have hφw := (schwartzMul φ w).coeFn_toLp 2 volume
  have hφcw := (schwartzMul φ (conjSchwartz w)).coeFn_toLp 2 volume
  have hcore := schwartz_second_derivative_current_identity φ w
  have hww (x : ℝ) : w'' x = iteratedDeriv 2 (w : ℝ → ℂ) x := by
    rw [show iteratedDeriv 2 (w : ℝ → ℂ) =
      deriv (deriv (w : ℝ → ℂ)) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num,
          iteratedDeriv_succ, iteratedDeriv_one]]
    rfl
  have hL1 :
      (∫ x : ℝ, inner ℂ (w.toLp 2 volume x)
        (spatialPrimitiveMulCLM φ
          (Complex.I • w''.toLp 2 volume) x)) =
        ∫ x : ℝ, conj (w x) * spatialPrimitive φ x *
          (Complex.I * iteratedDeriv 2 (w : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards [hMw, hsmul, hwcoe, hwppcoe]
      with x hMw hsmul hw hwpp
    rw [hw, hMw, hsmul]
    simp only [RCLike.inner_apply, Pi.smul_apply, smul_eq_mul]
    rw [hwpp, hww]
    ring
  have hL2 :
      (∫ x : ℝ, inner ℂ
        (((Complex.I • w''.toLp 2 volume : L2) : ℝ → ℂ) x)
        (spatialPrimitiveMulCLM φ (w.toLp 2 volume) x)) =
        ∫ x : ℝ, conj (Complex.I * iteratedDeriv 2 (w : ℝ → ℂ) x) *
          spatialPrimitive φ x * w x := by
    apply integral_congr_ae
    filter_upwards [hM0, hsmul, hwcoe, hwppcoe]
      with x hM0 hsmul hw hwpp
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hwpp, hM0, hw, hww]
    simp only [RCLike.inner_apply]
    ring
  have hR1 :
      (∫ x : ℝ, inner ℂ (w'.toLp 2 volume x)
        ((schwartzMul φ w).toLp 2 volume x)) =
        ∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) * φ x * w x := by
    apply integral_congr_ae
    filter_upwards [hwpcoe, hφw] with x hwp hφw
    rw [hwp, hφw, schwartzMul_apply]
    simp only [RCLike.inner_apply]
    change φ x * w x * conj (deriv (w : ℝ → ℂ) x) = _
    ring
  have hR2 :
      (∫ x : ℝ, inner ℂ ((conjSchwartz w').toLp 2 volume x)
        ((schwartzMul φ (conjSchwartz w)).toLp 2 volume x)) =
        ∫ x : ℝ, deriv (w : ℝ → ℂ) x * φ x * conj (w x) := by
    apply integral_congr_ae
    filter_upwards [hcwp, hφcw] with x hcwp hφcw
    rw [hcwp, hφcw, schwartzMul_apply, conjSchwartz_apply,
      conjSchwartz_apply]
    simp only [RCLike.inner_apply]
    rw [show conj (conj (w' x)) = w' x by simp]
    change φ x * conj (w x) * w' x = _
    rw [show w' x = deriv (w : ℝ → ℂ) x by rfl]
    ring
  rw [hL1, hL2, hR1, hR2]
  exact hcore

/-- The regularized free-generator identity for arbitrary `L²` data. -/
theorem regularizedGeneratorForm_eq_currents (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) :
    regularizedGeneratorForm n f φ =
      Complex.I *
        (regularizedReverseCurrent n f φ -
          regularizedForwardCurrent n f φ) := by
  let e : SchwartzMap ℝ ℂ → L2 := SchwartzMap.toLpCLM ℝ ℂ 2 volume
  have he : DenseRange e :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (μ := volume) (by norm_num)
  let left : L2 → ℂ := fun g => regularizedGeneratorForm n g φ
  let right : L2 → ℂ := fun g => Complex.I *
    (regularizedReverseCurrent n g φ - regularizedForwardCurrent n g φ)
  have hfun : left = right := by
    apply he.equalizer
    · exact continuous_regularizedGeneratorForm n φ
    · exact continuous_const.mul
        ((continuous_regularizedReverseCurrent n φ).sub
          (continuous_regularizedForwardCurrent n φ))
    · funext g
      exact regularizedGeneratorForm_schwartz n g φ
  exact congrFun hfun f

/-- The generator term selected from the mild equation is the regularized
continuity current. -/
theorem regularizedGeneratorMomentContribution_eq_currents
    (n : ℕ) {σ : ℝ} (u : GlobalSolution σ)
    (φ : SchwartzMap ℝ ℂ) (t : ℝ) :
    regularizedGeneratorMomentContribution n u φ t =
      Complex.I *
        (regularizedReverseCurrent n (u.u t) φ -
          regularizedForwardCurrent n (u.u t) φ) := by
  rw [regularizedGeneratorMomentContribution,
    regularizedGenerator_eq_i_second]
  exact regularizedGeneratorForm_eq_currents n (u.u t) φ

/-- The derivative-of-density term paired with a Schwartz test. -/
def regularizedDensityDerivativeTest (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ (frequencySmoothCLM n f)
    (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)
      (frequencySmoothCLM n f))

lemma continuous_regularizedDensityDerivativeTest (n : ℕ)
    (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun f : L2 => regularizedDensityDerivativeTest n f φ) := by
  unfold regularizedDensityDerivativeTest
  exact Continuous.inner (frequencySmoothCLM n).continuous
    ((cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)).continuous.comp
      (frequencySmoothCLM n).continuous)

private lemma deriv_schwartzMul (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (schwartzMul f g : ℝ → ℂ) x =
      deriv (f : ℝ → ℂ) x * g x + f x * deriv (g : ℝ → ℂ) x := by
  have heq : (schwartzMul f g : ℝ → ℂ) = fun y => f y * g y := by
    funext y
    exact schwartzMul_apply f g y
  rw [heq]
  exact (f.differentiableAt.hasDerivAt.mul
    g.differentiableAt.hasDerivAt).deriv

private lemma schwartz_current_sum_identity
    (φ w : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) * φ x * w x) +
      (∫ x : ℝ, deriv (w : ℝ → ℂ) x * φ x * conj (w x)) =
      -(∫ x : ℝ, conj (w x) * deriv (φ : ℝ → ℂ) x * w x) := by
  let w' := (SchwartzMap.derivCLM ℂ ℂ) w
  let φ' := (SchwartzMap.derivCLM ℂ ℂ) φ
  let φw := schwartzMul φ w
  have hw' (x : ℝ) : w' x = deriv (w : ℝ → ℂ) x := rfl
  have hφ' (x : ℝ) : φ' x = deriv (φ : ℝ → ℂ) x := rfl
  have hφw (x : ℝ) : φw x = φ x * w x := by
    exact schwartzMul_apply φ w x
  have hdφw (x : ℝ) : deriv (φw : ℝ → ℂ) x =
      deriv (φ : ℝ → ℂ) x * w x + φ x * deriv (w : ℝ → ℂ) x := by
    exact deriv_schwartzMul φ w x
  have hibp := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul
    (conjSchwartz w) φw
  have hintD : Integrable (fun x : ℝ =>
      conj (w x) * deriv (φ : ℝ → ℂ) x * w x) := by
    have h : Integrable
        (schwartzMul (schwartzMul (conjSchwartz w) φ') w : ℝ → ℂ)
        volume := (schwartzMul
          (schwartzMul (conjSchwartz w) φ') w).integrable
    apply h.congr
    filter_upwards with x
    rw [schwartzMul_apply, schwartzMul_apply, conjSchwartz_apply, hφ']
  have hintF : Integrable (fun x : ℝ =>
      deriv (w : ℝ → ℂ) x * φ x * conj (w x)) := by
    have h : Integrable
        (schwartzMul (schwartzMul w' φ) (conjSchwartz w) : ℝ → ℂ)
        volume := (schwartzMul
          (schwartzMul w' φ) (conjSchwartz w)).integrable
    apply h.congr
    filter_upwards with x
    rw [schwartzMul_apply, schwartzMul_apply, conjSchwartz_apply, hw']
  have hleft :
      (∫ x : ℝ, conjSchwartz w x * deriv (φw : ℝ → ℂ) x) =
        (∫ x : ℝ, conj (w x) * deriv (φ : ℝ → ℂ) x * w x) +
          ∫ x : ℝ, deriv (w : ℝ → ℂ) x * φ x * conj (w x) := by
    rw [← integral_add hintD hintF]
    apply integral_congr_ae
    filter_upwards with x
    rw [conjSchwartz_apply, hdφw]
    ring
  have hright :
      (∫ x : ℝ, deriv (conjSchwartz w : ℝ → ℂ) x * φw x) =
        ∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) * φ x * w x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [deriv_conjSchwartz, hφw]
    ring
  rw [hleft, hright] at hibp
  linear_combination hibp

private lemma regularizedCurrent_sum_schwartz (n : ℕ)
    (f φ : SchwartzMap ℝ ℂ) :
    regularizedReverseCurrent n (f.toLp 2 volume) φ +
      regularizedForwardCurrent n (f.toLp 2 volume) φ =
      -regularizedDensityDerivativeTest n (f.toLp 2 volume) φ := by
  let w := frequencySmoothSchwartz n f
  let w' := (SchwartzMap.derivCLM ℂ ℂ) w
  have hw : frequencySmoothCLM n (f.toLp 2 volume) =
      w.toLp 2 volume := frequencySmoothCLM_schwartz n f
  have hw' : frequencySmoothDerivativeCLM n (f.toLp 2 volume) =
      w'.toLp 2 volume := frequencySmoothDerivativeCLM_schwartz n f
  rw [regularizedReverseCurrent, regularizedForwardCurrent,
    regularizedDensityDerivativeTest, hw, hw', conjL2_schwartz,
    conjL2_schwartz, cutoffL2CLM_schwartz, cutoffL2CLM_schwartz,
    cutoffL2CLM_schwartz, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hwp := w'.coeFn_toLp 2 volume
  have hwc := w.coeFn_toLp 2 volume
  have hcwp := (conjSchwartz w').coeFn_toLp 2 volume
  have hφw := (schwartzMul φ w).coeFn_toLp 2 volume
  have hφcw := (schwartzMul φ (conjSchwartz w)).coeFn_toLp 2 volume
  have hdφw := (schwartzMul (SchwartzMap.derivCLM ℂ ℂ φ) w).coeFn_toLp
    2 volume
  have hcore := schwartz_current_sum_identity φ w
  have hR :
      (∫ x : ℝ, inner ℂ (w'.toLp 2 volume x)
        ((schwartzMul φ w).toLp 2 volume x)) =
        ∫ x : ℝ, conj (deriv (w : ℝ → ℂ) x) * φ x * w x := by
    apply integral_congr_ae
    filter_upwards [hwp, hφw] with x hwp hφw
    rw [hwp, hφw, schwartzMul_apply]
    simp only [RCLike.inner_apply]
    change φ x * w x * conj (deriv (w : ℝ → ℂ) x) = _
    ring
  have hF :
      (∫ x : ℝ, inner ℂ ((conjSchwartz w').toLp 2 volume x)
        ((schwartzMul φ (conjSchwartz w)).toLp 2 volume x)) =
        ∫ x : ℝ, deriv (w : ℝ → ℂ) x * φ x * conj (w x) := by
    apply integral_congr_ae
    filter_upwards [hcwp, hφcw] with x hcwp hφcw
    rw [hcwp, hφcw, schwartzMul_apply, conjSchwartz_apply,
      conjSchwartz_apply]
    simp only [RCLike.inner_apply]
    rw [show conj (conj (w' x)) = w' x by simp]
    change φ x * conj (w x) * deriv (w : ℝ → ℂ) x = _
    ring
  have hD :
      (∫ x : ℝ, inner ℂ (w.toLp 2 volume x)
        ((schwartzMul (SchwartzMap.derivCLM ℂ ℂ φ) w).toLp
          2 volume x)) =
        ∫ x : ℝ, conj (w x) * deriv (φ : ℝ → ℂ) x * w x := by
    apply integral_congr_ae
    filter_upwards [hwc, hdφw] with x hwc hdφw
    rw [hwc, hdφw, schwartzMul_apply]
    simp only [RCLike.inner_apply]
    change deriv (φ : ℝ → ℂ) x * w x * conj (w x) = _
    ring
  rw [hR, hF, hD]
  exact hcore

theorem regularizedCurrent_sum_eq_densityDerivative (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) :
    regularizedReverseCurrent n f φ + regularizedForwardCurrent n f φ =
      -regularizedDensityDerivativeTest n f φ := by
  let e : SchwartzMap ℝ ℂ → L2 := SchwartzMap.toLpCLM ℝ ℂ 2 volume
  have he : DenseRange e :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (μ := volume) (by norm_num)
  apply congrFun (he.equalizer
    ((continuous_regularizedReverseCurrent n φ).add
      (continuous_regularizedForwardCurrent n φ))
    (continuous_regularizedDensityDerivativeTest n φ).neg
    (by
      funext g
      exact regularizedCurrent_sum_schwartz n g φ)) f

/-- Solving the symmetric and antisymmetric current identities recovers the
forward quadratic current. -/
theorem two_mul_regularizedForwardCurrent_eq (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) :
    2 * regularizedForwardCurrent n f φ =
      Complex.I * regularizedGeneratorForm n f φ -
        regularizedDensityDerivativeTest n f φ := by
  have hg := regularizedGeneratorForm_eq_currents n f φ
  have hs := regularizedCurrent_sum_eq_densityDerivative n f φ
  rw [hg]
  rw [show Complex.I *
      (Complex.I * (regularizedReverseCurrent n f φ -
        regularizedForwardCurrent n f φ)) =
      -(regularizedReverseCurrent n f φ -
        regularizedForwardCurrent n f φ) by
    rw [← mul_assoc, Complex.I_mul_I]
    ring]
  linear_combination hs

end CubicNLSPhaseRetrieval
