import Lean_Code.FreeSchrodinger

open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology ContDiff

noncomputable section

set_option maxHeartbeats 2000000

namespace CubicNLSPhaseRetrieval

private def largeBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := n + 1
  rOut := n + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by norm_num

private lemma largeBump_eventually_one (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, largeBump n x = 1 := by
  filter_upwards [eventually_ge_atTop (Nat.ceil |x|)] with n hn
  apply (largeBump n).one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  dsimp [largeBump]
  calc
    |x| ≤ (Nat.ceil |x| : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ n + 1 := by norm_num

private lemma smooth_l1_l2_fourierInv_bridge (g : ℝ → ℂ)
    (hg_smooth : ContDiff ℝ ∞ g) (hg1 : MemLp g 1 volume)
    (hg2 : MemLp g 2 volume) :
    ((𝓕⁻ (hg2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] (𝓕⁻ g) := by
  let gn : ℕ → ℝ → ℂ := fun n x => ((largeBump n x : ℝ) : ℂ) * g x
  have hgn_smooth (n : ℕ) : ContDiff ℝ ∞ (gn n) := by
    dsimp [gn]
    exact (Complex.ofRealCLM.contDiff.comp (largeBump n).contDiff).mul hg_smooth
  have hgn_compact (n : ℕ) : HasCompactSupport (gn n) := by
    have hb : HasCompactSupport (fun x : ℝ => ((largeBump n x : ℝ) : ℂ)) := by
      have hbc := (largeBump n).hasCompactSupport
      rw [hasCompactSupport_iff_eventuallyEq] at hbc ⊢
      exact hbc.mono fun x hx => by simp [hx]
    dsimp [gn]
    exact hb.mul_right
  let sn : ℕ → SchwartzMap ℝ ℂ := fun n =>
    (hgn_compact n).toSchwartzMap (hgn_smooth n)
  have hsn_coe (n : ℕ) : (sn n : ℝ → ℂ) = gn n := rfl
  have hgn1 (n : ℕ) : MemLp (gn n) 1 volume := (sn n).memLp 1 volume
  have hgn2 (n : ℕ) : MemLp (gn n) 2 volume := (sn n).memLp 2 volume
  have hpoint (x : ℝ) : Tendsto (fun n => gn n x) atTop (𝓝 (g x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [largeBump_eventually_one x] with n hn
    simp [gn, hn]
  have hdiff_bound (n : ℕ) (x : ℝ) :
      ‖gn n x - g x‖ₑ ^ (2 : ℝ) ≤ 4 * ‖g x‖ₑ ^ (2 : ℝ) := by
    have hb0 : 0 ≤ largeBump n x := (largeBump n).nonneg
    have hb1 : largeBump n x ≤ 1 := (largeBump n).le_one
    have hnrm : ‖gn n x - g x‖ ≤ 2 * ‖g x‖ := by
      dsimp [gn]
      calc
        ‖((largeBump n x : ℝ) : ℂ) * g x - g x‖ =
            ‖(((largeBump n x : ℝ) : ℂ) - 1) * g x‖ := by ring_nf
        _ = |largeBump n x - 1| * ‖g x‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          norm_cast
        _ ≤ 2 * ‖g x‖ := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
    have hen : ‖gn n x - g x‖ₑ ≤ 2 * ‖g x‖ₑ := by
      simpa [← ofReal_norm, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using
        ENNReal.ofReal_le_ofReal hnrm
    calc
      ‖gn n x - g x‖ₑ ^ (2 : ℝ) ≤ (2 * ‖g x‖ₑ) ^ (2 : ℝ) := by gcongr
      _ = 4 * ‖g x‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  have hdiff_meas (n : ℕ) : AEMeasurable
      (fun x => ‖gn n x - g x‖ₑ ^ (2 : ℝ)) volume :=
    ((hgn_smooth n).continuous.aestronglyMeasurable.sub hg2.1).enorm.pow_const _
  have hdom2 : (∫⁻ x : ℝ, 4 * ‖g x‖ₑ ^ (2 : ℝ) ∂volume) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hg2.2).ne
  have hlin2 : Tendsto
      (fun n => ∫⁻ x : ℝ, ‖gn n x - g x‖ₑ ^ (2 : ℝ) ∂volume)
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_of_dominated_convergence'
        (f := fun _ => 0) (fun x => 4 * ‖g x‖ₑ ^ (2 : ℝ)) hdiff_meas
        (fun n => Filter.Eventually.of_forall (hdiff_bound n)) hdom2 (by
          filter_upwards with x
          have hx : Tendsto (fun n => gn n x - g x) atTop (𝓝 0) := by
            simpa only [sub_self] using (hpoint x).sub (tendsto_const_nhds (x := g x))
          convert (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hx.enorm using 1 <;>
            simp [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]))
  have help2 : Tendsto (fun n => eLpNorm (gn n - g) 2 volume) atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
    convert (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hlin2 using 1 <;>
      simp [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
  have hLp2 : Tendsto (fun n => (sn n).toLp 2 volume) atTop (𝓝 (hg2.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    apply help2.congr'
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [(sn n).coeFn_toLp 2 volume] with x hx
    simp only [Pi.sub_apply]
    rw [hx]
    rfl
  have hInvLp2 : Tendsto (fun n => (𝓕⁻ (sn n)).toLp 2 volume) atTop
      (𝓝 (𝓕⁻ (hg2.toLp g))) := by
    have h : Tendsto (fun n => (𝓕⁻ ((sn n).toLp 2 volume) : Lp ℂ 2 volume)) atTop
        (𝓝 (𝓕⁻ (hg2.toLp g))) :=
      (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous.continuousAt.tendsto.comp hLp2
    apply h.congr'
    filter_upwards with n
    exact SchwartzMap.toLp_fourierInv_eq (sn n)
  have hdiff1_bound (n : ℕ) (x : ℝ) : ‖gn n x - g x‖ ≤ 2 * ‖g x‖ := by
    have hb0 : 0 ≤ largeBump n x := (largeBump n).nonneg
    have hb1 : largeBump n x ≤ 1 := (largeBump n).le_one
    dsimp [gn]
    calc
      ‖((largeBump n x : ℝ) : ℂ) * g x - g x‖ =
          ‖(((largeBump n x : ℝ) : ℂ) - 1) * g x‖ := by ring_nf
      _ = |largeBump n x - 1| * ‖g x‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_cast
      _ ≤ 2 * ‖g x‖ := by
        gcongr
        rw [abs_le]
        constructor <;> linarith
  have hIntDom : Integrable (fun x => (2 : ℝ) * ‖g x‖) volume := by
    exact (memLp_one_iff_integrable.1 hg1).norm.const_mul 2
  have hIntDiff : Tendsto (fun n => ∫ x, ‖gn n x - g x‖ ∂volume) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence
        (F := fun n x => ‖gn n x - g x‖) (f := fun _ => 0)
        (bound := fun x => 2 * ‖g x‖)
        (Filter.Eventually.of_forall fun n => ((hgn2 n).1.sub hg2.1).norm)
        (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdiff1_bound n x)
        hIntDom (by
          filter_upwards with x
          have hx : Tendsto (fun n => gn n x - g x) atTop (𝓝 0) := by
            simpa only [sub_self] using (hpoint x).sub (tendsto_const_nhds (x := g x))
          simpa only [norm_zero] using hx.norm))
  have hFourierInvUniform (x : ℝ) : Tendsto (fun n => (𝓕⁻ (gn n)) x) atTop (𝓝 ((𝓕⁻ g) x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnonneg : ∀ n : ℕ, 0 ≤ ‖(𝓕⁻ (gn n)) x - (𝓕⁻ g) x‖ :=
      fun n => norm_nonneg _
    have hle : ∀ n : ℕ, ‖(𝓕⁻ (gn n)) x - (𝓕⁻ g) x‖ ≤
        ∫ ξ, ‖gn n ξ - g ξ‖ ∂volume := by
      intro n
      have hphase (h : ℝ → ℂ) (hint : Integrable h volume) :
          Integrable (fun ξ : ℝ =>
            Complex.exp (((2 * Real.pi * @inner ℝ ℝ _ ξ x : ℝ) : ℂ) * Complex.I) • h ξ)
            volume := by
        apply Integrable.mono hint
        · exact (by fun_prop : Continuous (fun ξ : ℝ =>
              Complex.exp (((2 * Real.pi * @inner ℝ ℝ _ ξ x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable.smul
            hint.1
        · filter_upwards with ξ
          rw [norm_smul, Complex.norm_exp]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, sub_zero, Real.exp_zero, one_mul]
          norm_num
      rw [Real.fourierInv_eq', Real.fourierInv_eq']
      rw [← integral_sub]
      · apply norm_integral_le_of_norm_le
          ((memLp_one_iff_integrable.1 (hgn1 n)).sub
            (memLp_one_iff_integrable.1 hg1)).norm
        filter_upwards with ξ
        rw [← smul_sub, norm_smul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, sub_zero, Real.exp_zero, one_mul, Pi.sub_apply]
        norm_num
      · exact hphase (gn n) (memLp_one_iff_integrable.1 (hgn1 n))
      · exact hphase g (memLp_one_iff_integrable.1 hg1)
    exact squeeze_zero hnonneg hle hIntDiff
  obtain ⟨ns, hns, hsubAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hInvLp2).exists_seq_tendsto_ae
  filter_upwards [hsubAE,
    ae_all_iff.2 fun n => (𝓕⁻ (sn n)).coeFn_toLp 2 volume] with x hx hcoe
  have hraw := (hFourierInvUniform x).comp hns.tendsto_atTop
  have hraw' : Tendsto
      (fun i => (((𝓕⁻ (sn (ns i))).toLp 2 volume : ℝ → ℂ) x))
      atTop (𝓝 ((𝓕⁻ g) x)) := by
    apply hraw.congr'
    filter_upwards with i
    rw [hcoe (ns i)]
    change (𝓕⁻ (⇑(sn (ns i)) : ℝ → ℂ)) x = (𝓕⁻ (sn (ns i))) x
    exact (congrFun (SchwartzMap.fourierInv_coe (sn (ns i))) x).symm
  exact tendsto_nhds_unique hx hraw'

lemma schwartz_freeProp_eq_raw_fourierInv (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (freeProp t (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      𝓕⁻ (fun ξ : ℝ => schrodingerSymbol t ξ * (𝓕 φ) ξ) := by
  let g : ℝ → ℂ := fun ξ => schrodingerSymbol t ξ * (𝓕 φ) ξ
  have hg_smooth : ContDiff ℝ ∞ g := by
    have hreal : ContDiff ℝ ∞ (fun ξ : ℝ => -(4 * Real.pi ^ 2 * t * ξ ^ 2)) := by
      fun_prop
    have hsymbol : ContDiff ℝ ∞ (schrodingerSymbol t) := by
      unfold schrodingerSymbol
      exact Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const)
    have hfourierSmooth : ContDiff ℝ ∞ (fun x : ℝ => (𝓕 φ) x) := by
      simpa using (𝓕 φ).smooth (⊤ : ℕ∞)
    exact hsymbol.mul hfourierSmooth
  have hnorm (ξ : ℝ) : ‖g ξ‖ = ‖(𝓕 φ) ξ‖ := by
    dsimp [g]
    rw [norm_mul, norm_schrodingerSymbol, one_mul]
  have hg1 : MemLp g 1 volume := by
    exact ((𝓕 φ).memLp 1 volume).congr_norm hg_smooth.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => (hnorm ξ).symm)
  have hg2 : MemLp g 2 volume := by
    exact ((𝓕 φ).memLp 2 volume).congr_norm hg_smooth.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => (hnorm ξ).symm)
  have hbridge := smooth_l1_l2_fourierInv_bridge g hg_smooth hg1 hg2
  have hfreq : hg2.toLp g = fourierL2 (freeProp t (φ.toLp 2 volume)) := by
    have hφ : (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
        fun ξ => (𝓕 φ) ξ := by
      have heq : fourierL2 (φ.toLp 2 volume) = (𝓕 φ).toLp 2 volume := by
        exact SchwartzMap.toLp_fourier_eq φ
      rw [heq]
      exact (𝓕 φ).coeFn_toLp 2 volume
    apply Lp.ext
    filter_upwards [hg2.coeFn_toLp, fourier_freeProp t (φ.toLp 2 volume),
      hφ] with ξ hgξ hfree hφξ
    rw [hgξ, hfree, hφξ]
  have hinv : (𝓕⁻ (hg2.toLp g) : Lp ℂ 2 volume) = freeProp t (φ.toLp 2 volume) := by
    rw [hfreq]
    exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply _
  filter_upwards [hbridge] with x hx
  rw [hinv] at hx
  exact hx

private def gaussianEpsilon (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private def gaussianZ (t : ℝ) (n : ℕ) : ℂ :=
  (gaussianEpsilon n : ℂ) + ((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I

private def regularizedFreeKernel (t : ℝ) (n : ℕ) (w : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt (gaussianZ t n))⁻¹ *
    Complex.exp (-(((Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ)) / gaussianZ t n)

private def gaussianBoundaryKernel (t w : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℝ) : ℂ) *
    (Complex.sqrt ((((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I)))⁻¹ *
    Complex.exp (Complex.I * (((w ^ 2 / (4 * t) : ℝ) : ℂ)))

private lemma gaussianEpsilon_pos (n : ℕ) : 0 < gaussianEpsilon n := by
  dsimp [gaussianEpsilon]
  positivity

private lemma gaussianEpsilon_tendsto : Tendsto gaussianEpsilon atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private lemma gaussianZ_tendsto (t : ℝ) :
    Tendsto (gaussianZ t) atTop
      (𝓝 ((((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I))) := by
  change Tendsto
    (fun n => (gaussianEpsilon n : ℂ) + ((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I)
    atTop (𝓝 ((((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I)))
  have hreal : Tendsto (fun n => (gaussianEpsilon n : ℂ)) atTop (𝓝 0) :=
    Complex.ofRealCLM.continuous.continuousAt.tendsto.comp gaussianEpsilon_tendsto
  simpa only [zero_add] using
    hreal.add_const ((((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I))

private lemma regularizedFreeKernel_tendsto (t : ℝ) (ht : t ≠ 0) (w : ℝ) :
    Tendsto (fun n => regularizedFreeKernel t n w) atTop
      (𝓝 (gaussianBoundaryKernel t w)) := by
  let z0 : ℂ := (((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I)
  have hz0 : z0 ≠ 0 := by
    dsimp [z0]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by positivity) ht)) Complex.I_ne_zero
  have hzlim : Tendsto (gaussianZ t) atTop (𝓝 z0) := gaussianZ_tendsto t
  have hsqrt : Tendsto (fun n => Complex.sqrt (gaussianZ t n)) atTop
      (𝓝 (Complex.sqrt z0)) := by
    exact (Complex.continuousAt_sqrt (Or.inr (by
      dsimp [z0]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
      change 4 * Real.pi ^ 2 * t ≠ 0
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)) ht
      ))).tendsto.comp hzlim
  have hsqrt0 : Complex.sqrt z0 ≠ 0 := by
    unfold Complex.sqrt
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hpref : Tendsto (fun n =>
      ((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt (gaussianZ t n))⁻¹) atTop
      (𝓝 (((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt z0)⁻¹)) :=
    tendsto_const_nhds.mul (hsqrt.inv₀ hsqrt0)
  have hexp : Tendsto (fun n =>
      Complex.exp (-(((Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ)) / gaussianZ t n)) atTop
      (𝓝 (Complex.exp (Complex.I * (((w ^ 2 / (4 * t) : ℝ) : ℂ))))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    have hdiv : Tendsto (fun n => (((Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ)) / gaussianZ t n)
        atTop (𝓝 ((((Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ)) / z0)) :=
      (tendsto_const_nhds (x := (((Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ)))).div hzlim hz0
    convert hdiv.neg using 1
    · funext n
      ring
    · congr 1
      dsimp [z0]
      push_cast
      field_simp [Real.pi_ne_zero, ht, Complex.I_ne_zero]
      rw [Complex.I_sq]
      ring
  simpa only [regularizedFreeKernel, gaussianBoundaryKernel, z0] using hpref.mul hexp

private lemma regularizedFreeKernel_uniform_bound (t : ℝ) (ht : t ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ w : ℝ, ‖regularizedFreeKernel t n w‖ ≤ C := by
  let z0 : ℂ := (((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I)
  have hz0 : z0 ≠ 0 := by
    dsimp [z0]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by positivity) ht)) Complex.I_ne_zero
  have hzlim : Tendsto (gaussianZ t) atTop (𝓝 z0) := gaussianZ_tendsto t
  have hsqrt : Tendsto (fun n => Complex.sqrt (gaussianZ t n)) atTop
      (𝓝 (Complex.sqrt z0)) := by
    apply (Complex.continuousAt_sqrt (Or.inr ?_)).tendsto.comp hzlim
    dsimp [z0]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)) ht
  have hsqrt0 : Complex.sqrt z0 ≠ 0 := by
    unfold Complex.sqrt
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hpref : Tendsto (fun n =>
      ((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt (gaussianZ t n))⁻¹) atTop
      (𝓝 (((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt z0)⁻¹)) :=
    tendsto_const_nhds.mul (hsqrt.inv₀ hsqrt0)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hpref).exists_norm_le
  let C' := max C 0
  refine ⟨C', le_max_right _ _, ?_⟩
  intro n w
  have hzn_re : (gaussianZ t n).re = gaussianEpsilon n := by
    unfold gaussianZ
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzn_ne : gaussianZ t n ≠ 0 := by
    intro hz
    have he : gaussianEpsilon n = 0 := by
      calc
        gaussianEpsilon n = (gaussianZ t n).re := hzn_re.symm
        _ = (0 : ℂ).re := congrArg Complex.re hz
        _ = 0 := rfl
    exact (gaussianEpsilon_pos n).ne' he
  have hexp : ‖Complex.exp (-(((Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ)) / gaussianZ t n)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    rw [Complex.div_re]
    simp only [map_neg, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, neg_zero]
    rw [hzn_re]
    rw [zero_div, add_zero]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg (sq_nonneg Real.pi) (sq_nonneg w)))
        (gaussianEpsilon_pos n).le
    · exact Complex.normSq_nonneg _
  rw [regularizedFreeKernel, norm_mul]
  calc
    ‖((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt (gaussianZ t n))⁻¹‖ *
          ‖Complex.exp (-↑(Real.pi ^ 2 * w ^ 2) / gaussianZ t n)‖ ≤
        ‖((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt (gaussianZ t n))⁻¹‖ * 1 := by
      gcongr
    _ ≤ C' := by
      rw [mul_one]
      exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)

set_option maxHeartbeats 200000 in
private lemma regularized_fourierInv_eq_kernel (t : ℝ) (n : ℕ)
    (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕⁻ (fun ξ : ℝ =>
      Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ)) *
        schrodingerSymbol t ξ * (𝓕 φ) ξ)) x =
      ∫ y : ℝ, regularizedFreeKernel t n (x - y) * φ y := by
  let D : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (Complex.I * ((2 * Real.pi * (p.1 * x - p.2 * p.1) : ℝ) : ℂ)) *
      Complex.exp (-gaussianZ t n * (p.1 : ℂ) ^ 2) * φ p.2
  have hzre : (gaussianZ t n).re = gaussianEpsilon n := by
    unfold gaussianZ
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hgauss : Integrable (fun ξ : ℝ =>
      Complex.exp (-gaussianZ t n * (ξ : ℂ) ^ 2)) volume := by
    apply integrable_cexp_neg_mul_sq
    rw [hzre]
    exact gaussianEpsilon_pos n
  have hz_ne : gaussianZ t n ≠ 0 := by
    intro hz
    have he : gaussianEpsilon n = 0 := by
      calc
        gaussianEpsilon n = (gaussianZ t n).re := hzre.symm
        _ = (0 : ℂ).re := congrArg Complex.re hz
        _ = 0 := rfl
    exact (gaussianEpsilon_pos n).ne' he
  have hbase : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (-gaussianZ t n * (p.1 : ℂ) ^ 2) * φ p.2)
      (volume.prod volume) := hgauss.mul_prod φ.integrable
  have hD : Integrable D (volume.prod volume) := by
    apply Integrable.mono hbase
    · dsimp [D]
      fun_prop
    · filter_upwards with p
      dsimp [D]
      rw [norm_mul, norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, Real.exp_zero, one_mul]
      norm_num
  rw [Real.fourierInv_eq']
  rw [SchwartzMap.fourier_coe]
  simp_rw [Real.fourier_eq']
  simp_rw [Real.inner_apply]
  calc
    (∫ ξ : ℝ, Complex.exp (↑(2 * Real.pi * (ξ * x)) * Complex.I) •
        (Complex.exp (-↑(gaussianEpsilon n * ξ ^ 2)) *
          schrodingerSymbol t ξ *
          ∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * ξ)) * Complex.I) • φ y)) =
      ∫ ξ : ℝ, ∫ y : ℝ, D (ξ, y) := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [smul_eq_mul]
        rw [show
          Complex.exp (↑(2 * Real.pi * (ξ * x)) * Complex.I) *
              (Complex.exp (-↑(gaussianEpsilon n * ξ ^ 2)) *
                schrodingerSymbol t ξ *
                ∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * ξ)) * Complex.I) * φ y) =
            (Complex.exp (↑(2 * Real.pi * (ξ * x)) * Complex.I) *
              Complex.exp (-↑(gaussianEpsilon n * ξ ^ 2)) *
              schrodingerSymbol t ξ) *
                ∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * ξ)) * Complex.I) * φ y by
          ring]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        dsimp [D, schrodingerSymbol, gaussianZ]
        have hphase :
          (Complex.exp (((2 * Real.pi * (ξ * x) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ)) *
            Complex.exp (((-(4 * Real.pi ^ 2 * t * ξ ^ 2) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-2 * Real.pi * (y * ξ) : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (Complex.I * (((2 * Real.pi * (ξ * x - y * ξ) : ℝ) : ℂ))) *
            Complex.exp (-((gaussianEpsilon n : ℂ) +
              ((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I) * (ξ : ℂ) ^ 2) := by
          rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
            ← Complex.exp_add]
          congr 1
          push_cast
          ring
        let A : ℂ := Complex.exp (((2 * Real.pi * (ξ * x) : ℝ) : ℂ) * Complex.I)
        let B : ℂ := Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ))
        let C : ℂ := Complex.exp (((-(4 * Real.pi ^ 2 * t * ξ ^ 2) : ℝ) : ℂ) * Complex.I)
        let E : ℂ := Complex.exp (((-2 * Real.pi * (y * ξ) : ℝ) : ℂ) * Complex.I)
        change A * B * C * (E * φ y) = _
        calc
          A * B * C * (E * φ y) = (A * B * C * E) * φ y := by ring
          _ = (Complex.exp (Complex.I * (((2 * Real.pi * (ξ * x - y * ξ) : ℝ) : ℂ))) *
                Complex.exp (-((gaussianEpsilon n : ℂ) +
                  ((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I) * (ξ : ℂ) ^ 2)) * φ y := by
              dsimp [A, B, C, E]
              rw [hphase]
    _ = ∫ y : ℝ, ∫ ξ : ℝ, D (ξ, y) := integral_integral_swap hD
    _ = ∫ y : ℝ, regularizedFreeKernel t n (x - y) * φ y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [show (∫ ξ : ℝ, D (ξ, y)) =
          (∫ ξ : ℝ, Complex.exp
            (-gaussianZ t n * (ξ : ℂ) ^ 2 +
              Complex.I * ((2 * Real.pi * (x - y) * ξ : ℝ) : ℂ))) * φ y by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp [D]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring]
      rw [complex_gaussian_kernel (gaussianZ t n) (by
        rw [hzre]
        exact gaussianEpsilon_pos n) (2 * Real.pi * (x - y))]
      unfold regularizedFreeKernel
      congr 2
      apply congrArg Complex.exp
      field_simp [hz_ne]
      norm_cast
      ring

private lemma raw_fourierInv_eq_gaussianBoundaryKernel (t : ℝ) (ht : t ≠ 0)
    (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕⁻ (fun ξ : ℝ => schrodingerSymbol t ξ * (𝓕 φ) ξ)) x =
      ∫ y : ℝ, gaussianBoundaryKernel t (x - y) * φ y := by
  let F : ℕ → ℝ → ℂ := fun n ξ =>
    Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ)) *
      schrodingerSymbol t ξ * (𝓕 φ) ξ
  let f : ℝ → ℂ := fun ξ => schrodingerSymbol t ξ * (𝓕 φ) ξ
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    dsimp [F]
    have heps : Continuous (fun ξ : ℝ =>
        Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ))) := by
      fun_prop
    exact (heps.mul (continuous_schrodingerSymbol t)).aestronglyMeasurable.mul
      (𝓕 φ).continuous.aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable f volume := by
    exact (continuous_schrodingerSymbol t).aestronglyMeasurable.mul
      (𝓕 φ).continuous.aestronglyMeasurable
  have hreg_norm_le (n : ℕ) (ξ : ℝ) :
      ‖Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [map_neg, Complex.neg_re, Complex.ofReal_re]
    exact neg_nonpos.mpr (mul_nonneg (gaussianEpsilon_pos n).le (sq_nonneg ξ))
  have hF_bound (n : ℕ) (ξ : ℝ) : ‖F n ξ‖ ≤ ‖(𝓕 φ) ξ‖ := by
    dsimp [F]
    rw [norm_mul, norm_mul, norm_schrodingerSymbol]
    calc
      ‖Complex.exp (-↑(gaussianEpsilon n * ξ ^ 2))‖ * 1 * ‖(𝓕 φ) ξ‖ ≤
          1 * 1 * ‖(𝓕 φ) ξ‖ := by
            gcongr
            exact hreg_norm_le n ξ
      _ = ‖(𝓕 φ) ξ‖ := by ring
  have hF_point (ξ : ℝ) : Tendsto (fun n => F n ξ) atTop (𝓝 (f ξ)) := by
    have hepsReal : Tendsto (fun n => gaussianEpsilon n * ξ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using gaussianEpsilon_tendsto.mul_const (ξ ^ 2)
    have heps : Tendsto
        (fun n => ((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ)) atTop (𝓝 0) :=
      Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hepsReal
    have hexp : Tendsto
        (fun n => Complex.exp (-((gaussianEpsilon n * ξ ^ 2 : ℝ) : ℂ)))
        atTop (𝓝 1) := by
      convert Complex.continuous_exp.continuousAt.tendsto.comp heps.neg using 1 <;>
        simp [Function.comp_def]
    simpa only [F, f, one_mul, mul_assoc] using
      hexp.mul_const (schrodingerSymbol t ξ * (𝓕 φ) ξ)
  have hleft : Tendsto (fun n => (𝓕⁻ (F n)) x) atTop (𝓝 ((𝓕⁻ f) x)) := by
    simp_rw [Real.fourierInv_eq', Real.inner_apply]
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun ξ => ‖(𝓕 φ) ξ‖)
    · filter_upwards with n
      exact (by fun_prop : Continuous (fun ξ : ℝ =>
        Complex.exp ((((2 * Real.pi * (ξ * x) : ℝ) : ℂ)) * Complex.I))).aestronglyMeasurable.smul
          (hF_meas n)
    · filter_upwards with n
      filter_upwards with ξ
      rw [norm_smul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, Real.exp_zero, one_mul]
      norm_num
      exact hF_bound n ξ
    · exact (𝓕 φ).integrable.norm
    · filter_upwards with ξ
      exact tendsto_const_nhds.smul (hF_point ξ)
  obtain ⟨C, hC0, hC⟩ := regularizedFreeKernel_uniform_bound t ht
  have hright : Tendsto
      (fun n => ∫ y : ℝ, regularizedFreeKernel t n (x - y) * φ y)
      atTop (𝓝 (∫ y : ℝ, gaussianBoundaryKernel t (x - y) * φ y)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun y => C * ‖φ y‖)
    · filter_upwards with n
      have hc : Continuous (fun y : ℝ =>
          regularizedFreeKernel t n (x - y) * φ y) := by
        unfold regularizedFreeKernel gaussianZ gaussianEpsilon
        fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards with n
      filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n (x - y)) (norm_nonneg (φ y))
    · exact φ.integrable.norm.const_mul C
    · filter_upwards with y
      exact (regularizedFreeKernel_tendsto t ht (x - y)).mul_const (φ y)
  have hleft' : Tendsto
      (fun n => ∫ y : ℝ, regularizedFreeKernel t n (x - y) * φ y)
      atTop (𝓝 ((𝓕⁻ f) x)) := by
    apply hleft.congr'
    filter_upwards with n
    simpa only [F] using regularized_fourierInv_eq_kernel t n φ x
  exact tendsto_nhds_unique hleft' hright

private lemma free_kernel_explicit_gaussian (t : ℝ) (ht : t ≠ 0)
    (φ : 𝓢(ℝ, ℂ)) :
    (freeProp t (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y : ℝ, gaussianBoundaryKernel t (x - y) * φ y := by
  filter_upwards [schwartz_freeProp_eq_raw_fourierInv t φ] with x hx
  rw [hx]
  exact raw_fourierInv_eq_gaussianBoundaryKernel t ht φ x

/-- `lem:free-kernel-explicit`: equality of Fourier and kernel realizations on
Schwartz data, obtained as the boundary value of absolutely convergent
complex Gaussian integrals. -/
theorem free_kernel_explicit (t : ℝ) (ht : t ≠ 0) (φ : 𝓢(ℝ, ℂ)) :
    (freeProp t (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume] freeKernelOp t φ := by
  filter_upwards [free_kernel_explicit_gaussian t ht φ] with x hx
  rw [hx]
  unfold freeKernelOp freeKernel gaussianBoundaryKernel
  apply integral_congr_ae
  filter_upwards with y
  ring

private lemma norm_gaussianBoundaryKernel (t : ℝ) (ht : t ≠ 0) (w : ℝ) :
    ‖gaussianBoundaryKernel t w‖ =
      (4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ)) := by
  unfold gaussianBoundaryKernel
  rw [norm_mul, norm_mul, norm_inv]
  have hsqrtNorm :
      ‖(((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I) ^ (2⁻¹ : ℂ)‖ =
        ‖((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I‖ ^ (1 / 2 : ℝ) := by
    convert
      (Complex.norm_cpow_inv_nat (((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I) 2) using 1 <;>
        norm_num
  simp only [Complex.sqrt, hsqrtNorm, Complex.norm_exp,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_mul, Real.exp_zero, mul_one]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have habs : |4 * Real.pi ^ 2 * t| = Real.pi * (4 * Real.pi * |t|) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2)]
    ring
  rw [habs]
  have hbase : 0 < 4 * Real.pi * |t| := by positivity
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le]
  rw [Real.rpow_neg hbase.le, ← Real.sqrt_eq_rpow]
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

end CubicNLSPhaseRetrieval
