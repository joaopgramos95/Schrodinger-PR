import Lean_Code.RegularizedCurrentIdentity

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology ComplexConjugate

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- The unsmoothed density paired with the derivative of a spatial test. -/
def densityDerivativeTest (f : L2) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  inner ℂ f (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ) f)

lemma continuous_densityDerivativeTest (φ : SchwartzMap ℝ ℂ) :
    Continuous (fun f : L2 => densityDerivativeTest f φ) := by
  unfold densityDerivativeTest
  exact Continuous.inner continuous_id
    (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)).continuous

lemma regularizedDensityDerivativeTest_tendsto (f : L2)
    (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n : ℕ => regularizedDensityDerivativeTest n f φ) atTop
      (nhds (densityDerivativeTest f φ)) := by
  exact (continuous_densityDerivativeTest φ).continuousAt.tendsto.comp
    (frequencySmoothCLM_tendsto f)

lemma densityDerivativeTest_eq_of_norm_sq_ae (f g : L2)
    (φ : SchwartzMap ℝ ℂ)
    (h : ∀ᵐ x : ℝ ∂volume,
      ‖(f : ℝ → ℂ) x‖ ^ 2 = ‖(g : ℝ → ℂ) x‖ ^ 2) :
    densityDerivativeTest f φ = densityDerivativeTest g φ := by
  rw [densityDerivativeTest, densityDerivativeTest,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ) f,
    coe_cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ) g, h]
      with x hf hg hx
  rw [hf, hg]
  simp only [RCLike.inner_apply]
  have hnormf : conj ((f : ℝ → ℂ) x) * (f : ℝ → ℂ) x =
      ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' ((f : ℝ → ℂ) x)
  have hnormg : conj ((g : ℝ → ℂ) x) * (g : ℝ → ℂ) x =
      ((‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' ((g : ℝ → ℂ) x)
  calc
    (SchwartzMap.derivCLM ℂ ℂ φ) x * (f : ℝ → ℂ) x *
        conj ((f : ℝ → ℂ) x) =
      (SchwartzMap.derivCLM ℂ ℂ φ) x *
        (conj ((f : ℝ → ℂ) x) * (f : ℝ → ℂ) x) := by ring
    _ = (SchwartzMap.derivCLM ℂ ℂ φ) x *
        (conj ((g : ℝ → ℂ) x) * (g : ℝ → ℂ) x) := by
      rw [hnormf, hnormg, hx]
    _ = (SchwartzMap.derivCLM ℂ ℂ φ) x * (g : ℝ → ℂ) x *
        conj ((g : ℝ → ℂ) x) := by ring

lemma norm_regularizedDensityDerivativeTest_le (n : ℕ) (f : L2)
    (φ : SchwartzMap ℝ ℂ) :
    ‖regularizedDensityDerivativeTest n f φ‖ ≤
      ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ * ‖f‖ ^ 2 := by
  unfold regularizedDensityDerivativeTest
  calc
    ‖inner ℂ (frequencySmoothCLM n f)
        (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)
          (frequencySmoothCLM n f))‖ ≤
      ‖frequencySmoothCLM n f‖ *
        ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)
          (frequencySmoothCLM n f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖frequencySmoothCLM n f‖ *
        (‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ *
          ‖frequencySmoothCLM n f‖) := by
      gcongr
      exact (cutoffL2CLM
        (SchwartzMap.derivCLM ℂ ℂ φ)).le_opNorm _
    _ = ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ *
        ‖frequencySmoothCLM n f‖ ^ 2 := by ring
    _ ≤ ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ * ‖f‖ ^ 2 := by
      gcongr
      exact norm_frequencySmoothCLM_le n f

lemma regularizedDensityDerivative_difference_integral_tendsto_zero
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (φ : SchwartzMap ℝ ℂ) {a b : ℝ} (habI : uIcc a b ⊆ I) :
    Tendsto (fun n : ℕ => ∫ t in a..b,
      (regularizedDensityDerivativeTest n (u.u t) φ -
        regularizedDensityDerivativeTest n (v.u t) φ)) atTop (nhds 0) := by
  obtain ⟨Bu, hBu⟩ := (isCompact_uIcc (a := a) (b := b)).bddAbove_image
    u.continuous.norm.continuousOn
  obtain ⟨Bv, hBv⟩ := (isCompact_uIcc (a := a) (b := b)).bddAbove_image
    v.continuous.norm.continuousOn
  have hBu0 : 0 ≤ Bu :=
    (norm_nonneg (u.u a)).trans (hBu ⟨a, left_mem_uIcc, rfl⟩)
  have hBv0 : 0 ≤ Bv :=
    (norm_nonneg (v.u a)).trans (hBv ⟨a, left_mem_uIcc, rfl⟩)
  let C : ℝ := ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ *
    (Bu ^ 2 + Bv ^ 2)
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun t =>
      regularizedDensityDerivativeTest n (u.u t) φ -
        regularizedDensityDerivativeTest n (v.u t) φ)
      (volume.restrict (uIoc a b)) := by
    exact (((continuous_regularizedDensityDerivativeTest n φ).comp
      u.continuous).sub
        ((continuous_regularizedDensityDerivativeTest n φ).comp
          v.continuous)).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ t ∈ uIoc a b,
      ‖regularizedDensityDerivativeTest n (u.u t) φ -
        regularizedDensityDerivativeTest n (v.u t) φ‖ ≤ C := by
    intro n t ht
    have huB : ‖u.u t‖ ≤ Bu := hBu ⟨t, uIoc_subset_uIcc ht, rfl⟩
    have hvB : ‖v.u t‖ ≤ Bv := hBv ⟨t, uIoc_subset_uIcc ht, rfl⟩
    calc
      ‖regularizedDensityDerivativeTest n (u.u t) φ -
          regularizedDensityDerivativeTest n (v.u t) φ‖ ≤
        ‖regularizedDensityDerivativeTest n (u.u t) φ‖ +
          ‖regularizedDensityDerivativeTest n (v.u t) φ‖ := norm_sub_le _ _
      _ ≤ ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ * ‖u.u t‖ ^ 2 +
          ‖cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ)‖ * ‖v.u t‖ ^ 2 :=
        add_le_add (norm_regularizedDensityDerivativeTest_le n (u.u t) φ)
          (norm_regularizedDensityDerivativeTest_le n (v.u t) φ)
      _ ≤ C := by
        dsimp [C]
        have hu2 : ‖u.u t‖ ^ 2 ≤ Bu ^ 2 := by gcongr
        have hv2 : ‖v.u t‖ ^ 2 ≤ Bv ^ 2 := by gcongr
        nlinarith [ContinuousLinearMap.opNorm_nonneg
          (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ φ))]
  have hCint : IntervalIntegrable (fun _ : ℝ => C) volume a b :=
    intervalIntegrable_const
  have hpoint (t : ℝ) (ht : t ∈ uIoc a b) :
      Tendsto (fun n : ℕ =>
        regularizedDensityDerivativeTest n (u.u t) φ -
          regularizedDensityDerivativeTest n (v.u t) φ) atTop (nhds 0) := by
    have htI : t ∈ I := habI (uIoc_subset_uIcc ht)
    have heq := densityDerivativeTest_eq_of_norm_sq_ae
      (u.u t) (v.u t) φ (density_on_open σ u v I hI hmod t htI)
    simpa [heq] using
      (regularizedDensityDerivativeTest_tendsto (u.u t) φ).sub
        (regularizedDensityDerivativeTest_tendsto (v.u t) φ)
  have hout := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (a := a) (b := b) (f := fun _ => (0 : ℂ))
    (fun _ => C)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun t => hbound n t)
    hCint
    (Filter.Eventually.of_forall hpoint)
  simpa using hout

lemma regularizedGeneratorMoment_integral_eq
    (n : ℕ) (σ : ℝ) (u : GlobalSolution σ)
    (φ : SchwartzMap ℝ ℂ) (a b : ℝ) :
    (∫ t in a..b, regularizedGeneratorMomentContribution n u φ t) =
      regularizedDensityMoment n u φ b -
        regularizedDensityMoment n u φ a -
      ∫ t in a..b, nonlinearMomentContribution σ
        (frequencySmoothCLM n (u.u t))
        (frequencySmoothCLM n (u.nonlin t)) φ := by
  have hgen : IntervalIntegrable
      (regularizedGeneratorMomentContribution n u φ) volume a b := by
    have heq : regularizedGeneratorMomentContribution n u φ =
        fun t => regularizedGeneratorForm n (u.u t) φ := by
      funext t
      rw [regularizedGeneratorMomentContribution,
        regularizedGenerator_eq_i_second]
      rfl
    rw [heq]
    exact ((continuous_regularizedGeneratorForm n φ).comp
      u.continuous).intervalIntegrable a b
  have hnon : IntervalIntegrable (fun t => nonlinearMomentContribution σ
      (frequencySmoothCLM n (u.u t))
      (frequencySmoothCLM n (u.nonlin t)) φ) volume a b := by
    have hder := regularizedDensityMomentDerivative_intervalIntegrable
      n σ u φ a b
    have heq := regularizedDensityMomentDerivative_eq_generator_add_nonlinear
      (n := n) (u := u) (phi := φ)
    have hdiff := hder.sub hgen
    refine hdiff.congr ?_
    intro t ht
    change regularizedDensityMomentDerivative n u φ t -
      regularizedGeneratorMomentContribution n u φ t = _
    rw [heq]
    ring
  have hsplit : (∫ t in a..b,
      regularizedDensityMomentDerivative n u φ t) =
      (∫ t in a..b, regularizedGeneratorMomentContribution n u φ t) +
        ∫ t in a..b, nonlinearMomentContribution σ
          (frequencySmoothCLM n (u.u t))
          (frequencySmoothCLM n (u.nonlin t)) φ := by
    rw [intervalIntegral.integral_congr (fun t _ =>
      regularizedDensityMomentDerivative_eq_generator_add_nonlinear
        (n := n) (u := u) (phi := φ) t)]
    exact intervalIntegral.integral_add hgen hnon
  rw [regularizedDensityMoment_integral_eq_sub] at hsplit
  linear_combination -hsplit

theorem regularizedForwardCurrent_difference_integral_tendsto_zero
    (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u)
    (φ : SchwartzMap ℝ ℂ) {a b : ℝ} (habI : uIcc a b ⊆ I) :
    Tendsto (fun n : ℕ => ∫ t in a..b,
      (regularizedForwardCurrent n (u.u t) φ -
        regularizedForwardCurrent n (v.u t) φ)) atTop (nhds 0) := by
  have hgendiff : Tendsto (fun n : ℕ =>
      (∫ t in a..b, regularizedGeneratorMomentContribution n u φ t) -
        ∫ t in a..b, regularizedGeneratorMomentContribution n v φ t)
      atTop (nhds 0) := by
    have hendb := (regularizedDensityMoment_tendsto u φ b).sub
      (regularizedDensityMoment_tendsto v φ b)
    have henda := (regularizedDensityMoment_tendsto u φ a).sub
      (regularizedDensityMoment_tendsto v φ a)
    have hnb := densityMoment_eq_on_open σ u v I hI hmod φ
      (habI right_mem_uIcc)
    have hna := densityMoment_eq_on_open σ u v I hI hmod φ
      (habI left_mem_uIcc)
    have hnonu := regularizedNonlinearMoment_integral_tendsto_zero
      σ u φ a b
    have hnonv := regularizedNonlinearMoment_integral_tendsto_zero
      σ v φ a b
    convert ((hendb.sub henda).sub (hnonu.sub hnonv)) using 1
    · funext n
      rw [regularizedGeneratorMoment_integral_eq n σ u φ a b,
        regularizedGeneratorMoment_integral_eq n σ v φ a b]
      ring
    · rw [hnb, hna]
      simp
  have hdens := regularizedDensityDerivative_difference_integral_tendsto_zero
    σ u v I hI hmod φ habI
  have hidentity (n : ℕ) :
      2 * (∫ t in a..b,
        (regularizedForwardCurrent n (u.u t) φ -
          regularizedForwardCurrent n (v.u t) φ)) =
        Complex.I *
          ((∫ t in a..b, regularizedGeneratorMomentContribution n u φ t) -
            ∫ t in a..b, regularizedGeneratorMomentContribution n v φ t) -
        ∫ t in a..b,
          (regularizedDensityDerivativeTest n (u.u t) φ -
            regularizedDensityDerivativeTest n (v.u t) φ) := by
    have hu (t : ℝ) := two_mul_regularizedForwardCurrent_eq n (u.u t) φ
    have hv (t : ℝ) := two_mul_regularizedForwardCurrent_eq n (v.u t) φ
    have hGu (t : ℝ) : regularizedGeneratorForm n (u.u t) φ =
        regularizedGeneratorMomentContribution n u φ t := by
      rw [regularizedGeneratorMomentContribution,
        regularizedGenerator_eq_i_second]
      rfl
    have hGv (t : ℝ) : regularizedGeneratorForm n (v.u t) φ =
        regularizedGeneratorMomentContribution n v φ t := by
      rw [regularizedGeneratorMomentContribution,
        regularizedGenerator_eq_i_second]
      rfl
    have hp (t : ℝ) :
        2 * (regularizedForwardCurrent n (u.u t) φ -
          regularizedForwardCurrent n (v.u t) φ) =
        Complex.I *
          (regularizedGeneratorMomentContribution n u φ t -
            regularizedGeneratorMomentContribution n v φ t) -
          (regularizedDensityDerivativeTest n (u.u t) φ -
            regularizedDensityDerivativeTest n (v.u t) φ) := by
      rw [← hGu, ← hGv]
      linear_combination hu t - hv t
    have hFu : IntervalIntegrable
        (fun t => regularizedForwardCurrent n (u.u t) φ) volume a b :=
      ((continuous_regularizedForwardCurrent n φ).comp
        u.continuous).intervalIntegrable a b
    have hFv : IntervalIntegrable
        (fun t => regularizedForwardCurrent n (v.u t) φ) volume a b :=
      ((continuous_regularizedForwardCurrent n φ).comp
        v.continuous).intervalIntegrable a b
    have hGuInt : IntervalIntegrable
        (fun t => regularizedGeneratorMomentContribution n u φ t)
        volume a b := by
      apply ((continuous_regularizedGeneratorForm n φ).comp
        u.continuous).intervalIntegrable a b |>.congr
      intro t ht
      exact hGu t
    have hGvInt : IntervalIntegrable
        (fun t => regularizedGeneratorMomentContribution n v φ t)
        volume a b := by
      apply ((continuous_regularizedGeneratorForm n φ).comp
        v.continuous).intervalIntegrable a b |>.congr
      intro t ht
      exact hGv t
    have hDu : IntervalIntegrable
        (fun t => regularizedDensityDerivativeTest n (u.u t) φ)
        volume a b :=
      ((continuous_regularizedDensityDerivativeTest n φ).comp
        u.continuous).intervalIntegrable a b
    have hDv : IntervalIntegrable
        (fun t => regularizedDensityDerivativeTest n (v.u t) φ)
        volume a b :=
      ((continuous_regularizedDensityDerivativeTest n φ).comp
        v.continuous).intervalIntegrable a b
    calc
      2 * (∫ t in a..b,
          (regularizedForwardCurrent n (u.u t) φ -
            regularizedForwardCurrent n (v.u t) φ)) =
          ∫ t in a..b, 2 *
            (regularizedForwardCurrent n (u.u t) φ -
              regularizedForwardCurrent n (v.u t) φ) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ t in a..b,
          (Complex.I *
            (regularizedGeneratorMomentContribution n u φ t -
              regularizedGeneratorMomentContribution n v φ t) -
            (regularizedDensityDerivativeTest n (u.u t) φ -
              regularizedDensityDerivativeTest n (v.u t) φ)) := by
            exact intervalIntegral.integral_congr (fun t _ => hp t)
      _ = _ := by
        rw [intervalIntegral.integral_sub
              ((hGuInt.sub hGvInt).const_mul Complex.I) (hDu.sub hDv),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hGuInt hGvInt,
          intervalIntegral.integral_sub hDu hDv]
  have hscaled : Tendsto (fun n : ℕ =>
      2 * (∫ t in a..b,
        (regularizedForwardCurrent n (u.u t) φ -
          regularizedForwardCurrent n (v.u t) φ))) atTop (nhds 0) := by
    convert (hgendiff.const_mul Complex.I).sub hdens using 1
    · funext n
      exact hidentity n
    · simp
  have hhalf := hscaled.const_mul ((2 : ℂ)⁻¹)
  simpa using hhalf

end CubicNLSPhaseRetrieval
