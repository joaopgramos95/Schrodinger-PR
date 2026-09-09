import Lean_Code.RegularizedSolution
import Lean_Code.DensityCurrent

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- A bounded primitive of a Schwartz test.  The base point is irrelevant for
the continuity equation; choosing zero gives a particularly direct FTC. -/
def spatialPrimitive (phi : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ y in 0..x, phi y

def spatialPrimitiveBound (phi : SchwartzMap ℝ ℂ) : ℝ :=
  ∫ y, ‖phi y‖

lemma spatialPrimitiveBound_nonneg (phi : SchwartzMap ℝ ℂ) :
    0 ≤ spatialPrimitiveBound phi := by
  exact integral_nonneg fun _ => norm_nonneg _

lemma norm_spatialPrimitive_le (phi : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖spatialPrimitive phi x‖ ≤ spatialPrimitiveBound phi := by
  calc
    ‖spatialPrimitive phi x‖ ≤ ∫ y in Set.uIoc 0 x, ‖phi y‖ := by
      exact intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ y, ‖phi y‖ := by
      exact MeasureTheory.setIntegral_le_integral phi.integrable.norm
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)

lemma hasDerivAt_spatialPrimitive (phi : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (spatialPrimitive phi) (phi x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (phi.continuous.intervalIntegrable 0 x)
    (phi.continuous.stronglyMeasurableAtFilter volume (nhds x))
    phi.continuous.continuousAt

lemma continuous_spatialPrimitive (phi : SchwartzMap ℝ ℂ) :
    Continuous (spatialPrimitive phi) := by
  exact continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_spatialPrimitive phi x).continuousAt

/-- Multiplication by the bounded primitive of a Schwartz test on physical
`L²`. -/
def spatialPrimitiveMulCLM (phi : SchwartzMap ℝ ℂ) : L2 →L[ℂ] L2 :=
  boundedMulCLM (spatialPrimitive phi) (continuous_spatialPrimitive phi)
    (spatialPrimitiveBound phi) (spatialPrimitiveBound_nonneg phi)
    (norm_spatialPrimitive_le phi)

lemma coe_spatialPrimitiveMulCLM (phi : SchwartzMap ℝ ℂ) (f : L2) :
    (spatialPrimitiveMulCLM phi f : ℝ → ℂ) =ᵐ[volume]
      fun x => spatialPrimitive phi x * (f : ℝ → ℂ) x := by
  exact coe_boundedMulCLM (spatialPrimitive phi)
    (continuous_spatialPrimitive phi) (spatialPrimitiveBound phi)
    (spatialPrimitiveBound_nonneg phi) (norm_spatialPrimitive_le phi) f

/-- The complex Hilbert pairing, regarded as a continuous real-bilinear map.
The first slot of the complex inner product is conjugate-linear, hence only
real linearity is available simultaneously in both slots. -/
def innerRealCLM : L2 →L[ℝ] L2 →L[ℝ] ℂ :=
  (LinearMap.mk₂ ℝ (fun f : L2 => fun g : L2 => inner ℂ f g)
    (fun f g h => inner_add_left f g h)
    (fun c f g => by
      change inner ℂ ((c : ℂ) • f) g = (c : ℂ) * inner ℂ f g
      rw [inner_smul_left]
      simp)
    (fun f g h => inner_add_right f g h)
    (fun c f g => by
      change inner ℂ f ((c : ℂ) • g) = (c : ℂ) * inner ℂ f g
      rw [inner_smul_right])).mkContinuous₂ 1 (fun f g => by
        simpa using norm_inner_le_norm f g)

@[simp] lemma innerRealCLM_apply (f g : L2) :
    innerRealCLM f g = inner ℂ f g := rfl

/-- The regularized density moment tested against a bounded primitive. -/
def regularizedDensityMoment (n : ℕ) {σ : ℝ} (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  inner ℂ (frequencySmoothCLM n (u.u t))
    (spatialPrimitiveMulCLM phi (frequencySmoothCLM n (u.u t)))

lemma regularizedDensityMoment_absolutelyContinuousOnInterval
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (regularizedDensityMoment n u phi) a b := by
  have hw := frequencySmooth_solution_absolutelyContinuousOnInterval n σ u a b
  have hMw : AbsolutelyContinuousOnInterval
      (fun t => spatialPrimitiveMulCLM phi
        (frequencySmoothCLM n (u.u t))) a b :=
    AbsolutelyContinuousOnInterval.comp_continuousLinearMap hw
      ((spatialPrimitiveMulCLM phi).restrictScalars ℝ)
  exact AbsolutelyContinuousOnInterval.clm_apply hw hMw innerRealCLM

/-- Pointwise derivative formula for the regularized moment. -/
lemma regularizedDensityMoment_hasDerivAt
    (n : ℕ) {σ : ℝ} (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (t : ℝ) (d : L2)
    (h : HasDerivAt (fun s => frequencySmoothCLM n (u.u s)) d t) :
    HasDerivAt (regularizedDensityMoment n u phi)
      (inner ℂ (frequencySmoothCLM n (u.u t))
          (spatialPrimitiveMulCLM phi d) +
        inner ℂ d
          (spatialPrimitiveMulCLM phi (frequencySmoothCLM n (u.u t)))) t := by
  have hM : HasDerivAt
      (fun s => spatialPrimitiveMulCLM phi (frequencySmoothCLM n (u.u s)))
      (spatialPrimitiveMulCLM phi d) t := by
    exact ((spatialPrimitiveMulCLM phi).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  exact h.inner ℂ hM

lemma IntervalIntegrable.comp_continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (L : E →L[ℝ] F) :
    IntervalIntegrable (fun t => L (f t)) volume a b := by
  exact ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

/-- A finite-dimensional complex-valued version of the standard fact that
the a.e. derivative of an absolutely continuous curve is integrable. -/
lemma intervalIntegrable_of_ae_hasDerivAt_complex
    {f f' : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt f (f' x) x) :
    IntervalIntegrable f' volume a b := by
  have hreAC : AbsolutelyContinuousOnInterval (fun t => (f t).re) a b :=
    AbsolutelyContinuousOnInterval.comp_continuousLinearMap hf Complex.reCLM
  have himAC : AbsolutelyContinuousOnInterval (fun t => (f t).im) a b :=
    AbsolutelyContinuousOnInterval.comp_continuousLinearMap hf Complex.imCLM
  have hreEq : (fun t => deriv (fun s => (f s).re) t) =ᵐ[volume.restrict (Set.uIoc a b)]
      fun t => (f' t).re := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae hderiv] with t ht ht'
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht' (Set.uIoc_subset_uIcc ht))
    exact h.deriv
  have himEq : (fun t => deriv (fun s => (f s).im) t) =ᵐ[volume.restrict (Set.uIoc a b)]
      fun t => (f' t).im := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae hderiv] with t ht ht'
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht' (Set.uIoc_subset_uIcc ht))
    exact h.deriv
  have hre : IntervalIntegrable (fun t => (f' t).re) volume a b :=
    hreAC.intervalIntegrable_deriv.congr_ae hreEq
  have him : IntervalIntegrable (fun t => (f' t).im) volume a b :=
    himAC.intervalIntegrable_deriv.congr_ae himEq
  have hreC : IntervalIntegrable (fun t => ((f' t).re : ℂ)) volume a b :=
    IntervalIntegrable.comp_continuousLinearMap hre Complex.ofRealCLM
  have himC0 : IntervalIntegrable (fun t => ((f' t).im : ℂ)) volume a b :=
    IntervalIntegrable.comp_continuousLinearMap him Complex.ofRealCLM
  have himC : IntervalIntegrable
      (fun t => ((f' t).im : ℂ) * Complex.I) volume a b :=
    himC0.mul_const Complex.I
  exact (hreC.add himC).congr_ae (Filter.Eventually.of_forall fun t =>
    Complex.re_add_im (f' t))

/-- Strong derivative selected by the frequency-regularized equation. -/
def frequencySmoothSolutionDerivative (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (t : ℝ) : L2 :=
  freePropDerivative (regularizedInteraction n u t)
      (regularizedInteraction_generator_memLp n u t) t -
    (Complex.I * (σ : ℂ)) • frequencySmoothCLM n (u.nonlin t)

/-- The a.e. derivative of the regularized density moment. -/
def regularizedDensityMomentDerivative (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (phi : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  inner ℂ (frequencySmoothCLM n (u.u t))
      (spatialPrimitiveMulCLM phi (frequencySmoothSolutionDerivative n u t)) +
    inner ℂ (frequencySmoothSolutionDerivative n u t)
      (spatialPrimitiveMulCLM phi (frequencySmoothCLM n (u.u t)))

lemma regularizedDensityMoment_ae_hasDerivAt
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt (regularizedDensityMoment n u phi)
        (regularizedDensityMomentDerivative n u phi t) t := by
  have hu := frequencySmooth_solution_ae_hasDerivAt n σ u a b
  filter_upwards [hu] with t ht htI
  exact regularizedDensityMoment_hasDerivAt n u phi t
    (frequencySmoothSolutionDerivative n u t) (ht htI)

lemma regularizedDensityMomentDerivative_intervalIntegrable
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    IntervalIntegrable (regularizedDensityMomentDerivative n u phi)
      volume a b := by
  exact intervalIntegrable_of_ae_hasDerivAt_complex
    (regularizedDensityMoment_absolutelyContinuousOnInterval n σ u phi a b)
    (regularizedDensityMoment_ae_hasDerivAt n σ u phi a b)

/-- Fundamental theorem for the frequency-regularized density moment. -/
theorem regularizedDensityMoment_integral_eq_sub
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    (∫ t in a..b, regularizedDensityMomentDerivative n u phi t) =
      regularizedDensityMoment n u phi b -
        regularizedDensityMoment n u phi a := by
  exact AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt
    (regularizedDensityMoment_absolutelyContinuousOnInterval n σ u phi a b)
    (regularizedDensityMomentDerivative_intervalIntegrable n σ u phi a b)
    (regularizedDensityMoment_ae_hasDerivAt n σ u phi a b)

/-- The unsmoothed bounded density moment. -/
def densityMoment (f : L2) (phi : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ f (spatialPrimitiveMulCLM phi f)

lemma continuous_densityMoment (phi : SchwartzMap ℝ ℂ) :
    Continuous (fun f : L2 => densityMoment f phi) := by
  unfold densityMoment
  exact (innerRealCLM.continuous.comp continuous_id).clm_apply
    ((spatialPrimitiveMulCLM phi).continuous)

lemma regularizedDensityMoment_tendsto
    {σ : ℝ} (u : GlobalSolution σ) (phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    Tendsto (fun n : ℕ => regularizedDensityMoment n u phi t) atTop
      (nhds (densityMoment (u.u t) phi)) := by
  exact (continuous_densityMoment phi).continuousAt.tendsto.comp
    (frequencySmoothCLM_tendsto (u.u t))

lemma densityMoment_eq_of_norm_sq_ae (f g : L2)
    (phi : SchwartzMap ℝ ℂ)
    (h : ∀ᵐ x : ℝ ∂volume,
      ‖(f : ℝ → ℂ) x‖ ^ 2 = ‖(g : ℝ → ℂ) x‖ ^ 2) :
    densityMoment f phi = densityMoment g phi := by
  rw [densityMoment, densityMoment, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_spatialPrimitiveMulCLM phi f,
    coe_spatialPrimitiveMulCLM phi g, h] with x hf hg hx
  rw [hf, hg]
  simp only [RCLike.inner_apply]
  ring_nf
  rw [mul_assoc, mul_assoc, Complex.mul_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hx]

lemma densityMoment_eq_on_open (σ : ℝ) (u v : GlobalSolution σ)
    (I : Set ℝ) (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (phi : SchwartzMap ℝ ℂ) {t : ℝ} (ht : t ∈ I) :
    densityMoment (u.u t) phi = densityMoment (v.u t) phi := by
  exact densityMoment_eq_of_norm_sq_ae (u.u t) (v.u t) phi
    (density_on_open σ u v I hI hmod t ht)

/-- The nonlinear part of the regularized moment derivative. -/
def nonlinearMomentContribution (σ : ℝ) (f q : L2)
    (phi : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ f
      (spatialPrimitiveMulCLM phi
        (-((Complex.I * (σ : ℂ)) • q))) +
    inner ℂ (-((Complex.I * (σ : ℂ)) • q))
      (spatialPrimitiveMulCLM phi f)

/-- The free-generator part of the regularized moment derivative. -/
def regularizedGeneratorMomentContribution (n : ℕ) {σ : ℝ}
    (u : GlobalSolution σ) (phi : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  let g := freePropDerivative (regularizedInteraction n u t)
    (regularizedInteraction_generator_memLp n u t) t
  inner ℂ (frequencySmoothCLM n (u.u t))
      (spatialPrimitiveMulCLM phi g) +
    inner ℂ g
      (spatialPrimitiveMulCLM phi (frequencySmoothCLM n (u.u t)))

lemma regularizedDensityMomentDerivative_eq_generator_add_nonlinear
    (n : ℕ) {σ : ℝ} (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    regularizedDensityMomentDerivative n u phi t =
      regularizedGeneratorMomentContribution n u phi t +
        nonlinearMomentContribution σ (frequencySmoothCLM n (u.u t))
          (frequencySmoothCLM n (u.nonlin t)) phi := by
  simp only [regularizedDensityMomentDerivative,
    frequencySmoothSolutionDerivative,
    regularizedGeneratorMomentContribution, nonlinearMomentContribution,
    map_sub, map_neg, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right]
  ring

lemma nonlinearMomentContribution_zero_of_cubic
    (σ : ℝ) (f q : L2) (phi : SchwartzMap ℝ ℂ)
    (hq : (q : ℝ → ℂ) =ᵐ[volume]
      fun x => ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) *
        (f : ℝ → ℂ) x) :
    nonlinearMomentContribution σ f q phi = 0 := by
  rw [nonlinearMomentContribution, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def, ← integral_add]
  · apply integral_eq_zero_of_ae
    filter_upwards [coe_spatialPrimitiveMulCLM phi
        (-((Complex.I * (σ : ℂ)) • q)),
      coe_spatialPrimitiveMulCLM phi f,
      Lp.coeFn_neg ((Complex.I * (σ : ℂ)) • q),
      Lp.coeFn_smul (Complex.I * (σ : ℂ)) q, hq] with x hMnon hMf hneg hsmul hq
    simp only [Pi.neg_apply] at hneg
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hMnon, hMf, hneg, hsmul, hq]
    simp only [RCLike.inner_apply, map_neg, map_mul,
      Complex.conj_I, Complex.conj_ofReal, Pi.zero_apply]
    ring
  · exact MeasureTheory.L2.integrable_inner _ _
  · exact MeasureTheory.L2.integrable_inner _ _

lemma nonlinearMomentContribution_tendsto (σ : ℝ) (f q : L2)
    (phi : SchwartzMap ℝ ℂ) :
    Tendsto (fun n : ℕ => nonlinearMomentContribution σ
        (frequencySmoothCLM n f) (frequencySmoothCLM n q) phi) atTop
      (nhds (nonlinearMomentContribution σ f q phi)) := by
  have hf := frequencySmoothCLM_tendsto f
  have hq := frequencySmoothCLM_tendsto q
  have hcq : Tendsto (fun n : ℕ =>
      -((Complex.I * (σ : ℂ)) • frequencySmoothCLM n q)) atTop
      (nhds (-((Complex.I * (σ : ℂ)) • q))) :=
    (hq.const_smul (Complex.I * (σ : ℂ))).neg
  have hMnon := (spatialPrimitiveMulCLM phi).continuous.continuousAt.tendsto.comp hcq
  have hMf := (spatialPrimitiveMulCLM phi).continuous.continuousAt.tendsto.comp hf
  exact (Filter.Tendsto.inner hf hMnon).add
    (Filter.Tendsto.inner hcq hMf)

lemma nonlinearMomentContribution_tendsto_zero_of_cubic
    (σ : ℝ) (f q : L2) (phi : SchwartzMap ℝ ℂ)
    (hq : (q : ℝ → ℂ) =ᵐ[volume]
      fun x => ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) *
        (f : ℝ → ℂ) x) :
    Tendsto (fun n : ℕ => nonlinearMomentContribution σ
        (frequencySmoothCLM n f) (frequencySmoothCLM n q) phi) atTop
      (nhds 0) := by
  simpa [nonlinearMomentContribution_zero_of_cubic σ f q phi hq] using
    nonlinearMomentContribution_tendsto σ f q phi

lemma norm_nonlinearMomentContribution_le (σ : ℝ) (f q : L2)
    (phi : SchwartzMap ℝ ℂ) :
    ‖nonlinearMomentContribution σ f q phi‖ ≤
      2 * ‖spatialPrimitiveMulCLM phi‖ * |σ| * ‖f‖ * ‖q‖ := by
  let c : ℂ := Complex.I * (σ : ℂ)
  let M := spatialPrimitiveMulCLM phi
  have hc : ‖c‖ = |σ| := by
    simp [c, norm_mul, Real.norm_eq_abs]
  calc
    ‖nonlinearMomentContribution σ f q phi‖ ≤
        ‖inner ℂ f (M (-(c • q)))‖ +
          ‖inner ℂ (-(c • q)) (M f)‖ := norm_add_le _ _
    _ ≤ ‖f‖ * ‖M (-(c • q))‖ +
          ‖-(c • q)‖ * ‖M f‖ := by
      gcongr <;> exact norm_inner_le_norm _ _
    _ ≤ ‖f‖ * (‖M‖ * ‖-(c • q)‖) +
          ‖-(c • q)‖ * (‖M‖ * ‖f‖) := by
      gcongr <;> exact M.le_opNorm _
    _ = 2 * ‖spatialPrimitiveMulCLM phi‖ * |σ| * ‖f‖ * ‖q‖ := by
      simp only [M, norm_neg, norm_smul, hc]
      ring

lemma norm_regularized_nonlinearMomentContribution_le
    (n : ℕ) (σ : ℝ) (f q : L2) (phi : SchwartzMap ℝ ℂ) :
    ‖nonlinearMomentContribution σ (frequencySmoothCLM n f)
        (frequencySmoothCLM n q) phi‖ ≤
      2 * ‖spatialPrimitiveMulCLM phi‖ * |σ| * ‖f‖ * ‖q‖ := by
  refine (norm_nonlinearMomentContribution_le σ _ _ phi).trans ?_
  have hf := norm_frequencySmoothCLM_le n f
  have hq := norm_frequencySmoothCLM_le n q
  gcongr

/-- The nonlinear curve itself is Bochner-integrable on compact intervals.
The solution interface records this after a time-dependent unitary; applying
the inverse unitary preserves both measurability and norm. -/
lemma nonlin_intervalIntegrable (σ : ℝ) (u : GlobalSolution σ)
    (a b : ℝ) : IntervalIntegrable u.nonlin volume a b := by
  by_cases hab : a ≤ b
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (endpoint_nonlin_integrableOn_Icc σ u a b hab)
  · rw [IntervalIntegrable.symm_iff]
    have hba : b ≤ a := le_of_not_ge hab
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hba).mpr
      (endpoint_nonlin_integrableOn_Icc σ u b a hba)

lemma regularizedNonlinearMoment_aestronglyMeasurable
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ)
    (phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    AEStronglyMeasurable
      (fun t => nonlinearMomentContribution σ
        (frequencySmoothCLM n (u.u t))
        (frequencySmoothCLM n (u.nonlin t)) phi)
      (volume.restrict (Set.uIoc a b)) := by
  have hf : AEStronglyMeasurable
      (fun t => frequencySmoothCLM n (u.u t))
      (volume.restrict (Set.uIoc a b)) :=
    ((frequencySmoothCLM n).continuous.comp u.continuous).aestronglyMeasurable
  have hq0 := (nonlin_intervalIntegrable σ u a b).aestronglyMeasurable_restrict_uIoc
  have hq : AEStronglyMeasurable
      (fun t => frequencySmoothCLM n (u.nonlin t))
      (volume.restrict (Set.uIoc a b)) :=
    (frequencySmoothCLM n).continuous.comp_aestronglyMeasurable hq0
  have hcq : AEStronglyMeasurable (fun t =>
      -((Complex.I * (σ : ℂ)) • frequencySmoothCLM n (u.nonlin t)))
      (volume.restrict (Set.uIoc a b)) :=
    (hq.const_smul (Complex.I * (σ : ℂ))).neg
  have hMnon := (spatialPrimitiveMulCLM phi).continuous.comp_aestronglyMeasurable hcq
  have hMf := (spatialPrimitiveMulCLM phi).continuous.comp_aestronglyMeasurable hf
  exact (hf.inner hMnon).add (hcq.inner hMf)

/-- The cubic contribution vanishes after integration in time as the spatial
resolvent is removed. -/
theorem regularizedNonlinearMoment_integral_tendsto_zero
    (σ : ℝ) (u : GlobalSolution σ) (phi : SchwartzMap ℝ ℂ)
    (a b : ℝ) :
    Tendsto (fun n : ℕ => ∫ t in a..b,
        nonlinearMomentContribution σ
          (frequencySmoothCLM n (u.u t))
          (frequencySmoothCLM n (u.nonlin t)) phi) atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := isCompact_uIcc.bddAbove_image
    u.continuous.norm.continuousOn
  let A : ℝ := 2 * ‖spatialPrimitiveMulCLM phi‖ * |σ|
  let K : ℝ := A * B
  have hboundInt : IntervalIntegrable (fun t => K * ‖u.nonlin t‖)
      volume a b := (nonlin_intervalIntegrable σ u a b).norm.const_mul K
  have hout := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (a := a) (b := b) (f := fun _ => (0 : ℂ))
    (fun t => K * ‖u.nonlin t‖)
    (Filter.Eventually.of_forall fun n =>
      regularizedNonlinearMoment_aestronglyMeasurable n σ u phi a b)
    (Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun t ht => by
        calc
          ‖nonlinearMomentContribution σ
              (frequencySmoothCLM n (u.u t))
              (frequencySmoothCLM n (u.nonlin t)) phi‖ ≤
              A * ‖u.u t‖ * ‖u.nonlin t‖ := by
            simpa [A] using norm_regularized_nonlinearMomentContribution_le
              n σ (u.u t) (u.nonlin t) phi
          _ ≤ K * ‖u.nonlin t‖ := by
            have hBt : ‖u.u t‖ ≤ B := hB ⟨t, Set.uIoc_subset_uIcc ht, rfl⟩
            dsimp [K]
            gcongr)
    hboundInt
    (by
      filter_upwards [u.nonlin_eq] with t ht tmem
      exact nonlinearMomentContribution_tendsto_zero_of_cubic σ
        (u.u t) (u.nonlin t) phi ht)
  simpa using hout

end CubicNLSPhaseRetrieval
