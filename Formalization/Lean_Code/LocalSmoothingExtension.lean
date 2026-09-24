import Lean_Code.LocalSmoothing1D
import Lean_Code.L1L2FourierBridge
import Lean_Code.YoungConvolution

open Filter MeasureTheory Set
open scoped Convolution ENNReal FourierTransform SchwartzMap Topology
noncomputable section
set_option maxHeartbeats 500000

namespace CubicNLSPhaseRetrieval

private def smoothingBSchwartz (x : ℝ) (φ : 𝓢(ℝ, ℂ)) (w : ℝ) : ℂ :=
  if 0 < w then
    ((w ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ)) *
          (𝓕 φ) (Real.sqrt w) +
        Complex.exp (-Complex.I * ((2 * Real.pi * x * Real.sqrt w : ℝ) : ℂ)) *
          (𝓕 φ) (-Real.sqrt w))
  else 0

private def linearWeightedSchwartz (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => (((1 + y : ℝ) : ℂ))) φ

private lemma linearWeightedSchwartz_apply (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    linearWeightedSchwartz φ y = ((1 + y : ℝ) : ℂ) * φ y := by
  have h := SchwartzMap.smulLeftCLM_apply
    (show (fun y : ℝ => (((1 + y : ℝ) : ℂ))).HasTemperateGrowth by fun_prop) φ
  exact congrFun h y

private lemma weighted_schwartz_integrable_Ioi (φ : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun y : ℝ => (1 + y) * ‖φ y‖) (Ioi 0) := by
  have h := (linearWeightedSchwartz φ).integrable (μ := volume) |>.norm
  apply h.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [linearWeightedSchwartz_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by have := (show 0 < y from hy); linarith)]

private lemma sqrt_weight_le (y : ℝ) (hy : 0 < y) :
    y ^ (1 / 2 : ℝ) ≤ 1 + y := by
  rw [← Real.sqrt_eq_rpow]
  nlinarith [Real.sq_sqrt hy.le, Real.sqrt_nonneg y]

private lemma sq_image_Ioi' : (fun y : ℝ => y ^ 2) '' Ioi 0 = Ioi 0 := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact sq_pos_of_pos (show 0 < y from hy)
  · intro hw
    refine ⟨Real.sqrt w, Real.sqrt_pos.2 hw, Real.sq_sqrt hw.le⟩

private lemma smoothingBSchwartz_aestronglyMeasurable (x : ℝ)
    (φ : 𝓢(ℝ, ℂ)) : AEStronglyMeasurable (smoothingBSchwartz x φ) volume := by
  apply AEMeasurable.aestronglyMeasurable
  apply Measurable.aemeasurable
  unfold smoothingBSchwartz
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const

private lemma lintegral_norm_smoothingBSchwartz_lt_top (x : ℝ)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫⁻ w : ℝ, ‖smoothingBSchwartz x φ w‖ₑ) < ⊤ := by
  let U : ℝ → ℝ≥0∞ := fun w => ‖smoothingBSchwartz x φ w‖ₑ
  have hzero : ∀ w ≤ 0, U w = 0 := by
    intro w hw
    simp [U, smoothingBSchwartz, not_lt_of_ge hw]
  have hall : (∫⁻ w : ℝ, U w) = ∫⁻ w : ℝ in Ioi 0, U w := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro w
    by_cases hw : 0 < w
    · simp [Set.indicator, hw]
    · simp [Set.indicator, hw, hzero w (le_of_not_gt hw)]
  rw [hall]
  have hchange := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Ioi (0 : ℝ)) (f := fun y : ℝ => y ^ 2) (f' := fun y => 2 * y)
    measurableSet_Ioi
    (fun y _ => by simpa [pow_two] using (hasDerivAt_pow 2 y).hasDerivWithinAt)
    (fun y hy z hz hyz => by
      nlinarith [mul_nonneg (sub_nonneg.mpr hyz)
        (add_nonneg hy.le hz.le)]) U
  rw [sq_image_Ioi'] at hchange
  rw [hchange]
  have hpoint : ∀ y ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (2 * y) * U (y ^ 2) ≤
        ENNReal.ofReal (2 * ((1 + y) *
          (‖(𝓕 φ) y‖ + ‖(𝓕 φ) (-y)‖))) := by
    intro y hy
    have hy0 : 0 < y := hy
    have hsqrt : Real.sqrt (y ^ 2) = y := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hy0]
    have hweight : (y ^ 2) ^ (-(1 / 4 : ℝ)) = y ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    have hnorm : ‖smoothingBSchwartz x φ (y ^ 2)‖ ≤
        y ^ (-(1 / 2 : ℝ)) * (‖(𝓕 φ) y‖ + ‖(𝓕 φ) (-y)‖) := by
      rw [smoothingBSchwartz, if_pos (sq_pos_of_pos hy0), hsqrt, hweight,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
      have he₁ : ‖Complex.exp
          (Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ))‖ = 1 := by
        simp [Complex.norm_exp, Complex.mul_re]
      have he₂ : ‖Complex.exp
          (-Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ))‖ = 1 := by
        simp [Complex.norm_exp, Complex.mul_re]
      calc
        y ^ (-(1 / 2 : ℝ)) *
            ‖Complex.exp (Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ)) * (𝓕 φ) y +
              Complex.exp (-Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ)) *
                (𝓕 φ) (-y)‖ ≤
            y ^ (-(1 / 2 : ℝ)) *
              (‖Complex.exp (Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ)) *
                  (𝓕 φ) y‖ +
                ‖Complex.exp (-Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ)) *
                  (𝓕 φ) (-y)‖) := by gcongr; exact norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_mul, he₁, he₂, one_mul, one_mul]
    rw [show U (y ^ 2) = ‖smoothingBSchwartz x φ (y ^ 2)‖ₑ by rfl,
      ← ofReal_norm]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * y)]
    apply ENNReal.ofReal_le_ofReal
    have hwcalc : (2 * y) * y ^ (-(1 / 2 : ℝ)) = 2 * y ^ (1 / 2 : ℝ) := by
      calc
        (2 * y) * y ^ (-(1 / 2 : ℝ)) =
            2 * (y * y ^ (-(1 / 2 : ℝ))) := by ring
        _ = 2 * (y ^ (1 : ℝ) * y ^ (-(1 / 2 : ℝ))) := by rw [Real.rpow_one]
        _ = 2 * y ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
    calc
      (2 * y) * ‖smoothingBSchwartz x φ (y ^ 2)‖ ≤
          (2 * y) * (y ^ (-(1 / 2 : ℝ)) *
            (‖(𝓕 φ) y‖ + ‖(𝓕 φ) (-y)‖)) := by gcongr
      _ = 2 * y ^ (1 / 2 : ℝ) *
          (‖(𝓕 φ) y‖ + ‖(𝓕 φ) (-y)‖) := by rw [← mul_assoc, hwcalc]
      _ ≤ 2 * (1 + y) * (‖(𝓕 φ) y‖ + ‖(𝓕 φ) (-y)‖) := by
        gcongr
        exact sqrt_weight_le y hy0
      _ = _ := by ring
  let D : ℝ → ℝ := fun y => 2 * ((1 + y) *
    (‖(𝓕 φ) y‖ + ‖(𝓕 φ) (-y)‖))
  have hdom : IntegrableOn D (Ioi 0) := by
    have hp := weighted_schwartz_integrable_Ioi (𝓕 φ)
    have hnraw := weighted_schwartz_integrable_Ioi
      (SchwartzMap.compCLM ℂ (g := fun y : ℝ => -y)
        (by fun_prop) (by exact ⟨1, 1, fun y => by simp⟩) (𝓕 φ))
    have hn : IntegrableOn (fun y : ℝ => (1 + y) * ‖(𝓕 φ) (-y)‖) (Ioi 0) := by
      simpa using hnraw
    apply ((hp.add hn).const_mul 2).congr
    filter_upwards with y
    dsimp [D]
    ring
  calc
    (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (2 * y) * U (y ^ 2)) ≤
        ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (D y) := by
      simpa [D] using
      setLIntegral_mono' measurableSet_Ioi (fun y hy => hpoint y hy)
    _ = ∫⁻ y : ℝ in Ioi 0,
        ‖D y‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.enorm_eq_ofReal]
      dsimp [D]
      have hy0 : 0 < y := hy
      positivity
    _ < ⊤ := hdom.hasFiniteIntegral

private theorem smoothingBSchwartz_memLp_one (x : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    MemLp (smoothingBSchwartz x φ) 1 volume := by
  rw [memLp_one_iff_integrable]
  exact ⟨smoothingBSchwartz_aestronglyMeasurable x φ,
    lintegral_norm_smoothingBSchwartz_lt_top x φ⟩

private lemma sq_image_Ioi_schwartz :
    (fun x : ℝ => x ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sq_pos_of_pos (show 0 < x from hx)
  · intro hy
    exact ⟨Real.sqrt y, Real.sqrt_pos.2 hy, Real.sq_sqrt hy.le⟩

private lemma qmp_sqrt_Ioi_schwartz :
    Measure.QuasiMeasurePreserving Real.sqrt
      (volume.restrict (Set.Ioi 0)) volume := by
  refine ⟨Real.continuous_sqrt.measurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hnull
  rw [Measure.map_apply_of_aemeasurable Real.continuous_sqrt.aemeasurable hs,
    Measure.restrict_apply (hs.preimage Real.continuous_sqrt.measurable)]
  let u : ℝ → ℝ≥0∞ := (Real.sqrt ⁻¹' s).indicator 1
  have hchange := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Set.Ioi (0 : ℝ)) (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x)
    measurableSet_Ioi
    (fun x _ => by simpa [pow_two] using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
        (add_nonneg (show 0 ≤ x from hx.le) (show 0 ≤ y from hy.le))]) u
  rw [sq_image_Ioi_schwartz] at hchange
  have hs_ae : ∀ᵐ x : ℝ ∂volume, x ∉ s := by
    rw [ae_iff]
    simpa using hnull
  have hright :
      (∫⁻ x : ℝ in Set.Ioi 0, ENNReal.ofReal (2 * x) * u (x ^ 2)) = 0 := by
    rw [← lintegral_zero]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hs_ae]
      with x hx hxs
    simp [u, Real.sqrt_sq_eq_abs, abs_of_pos (show 0 < x from hx), hxs]
  have hleft : (∫⁻ y : ℝ in Set.Ioi 0, u y) = 0 := hchange.trans hright
  rw [show u = (Real.sqrt ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) by rfl,
    setLIntegral_indicator (hs.preimage Real.continuous_sqrt.measurable),
    setLIntegral_one] at hleft
  simpa [Set.inter_comm] using hleft

private lemma smoothingB_schwartz_ae (x : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    smoothingB x (φ.toLp 2 volume) =ᵐ[volume]
      smoothingBSchwartz x φ := by
  have hfourier : fourierL2 (φ.toLp 2 volume) = (𝓕 φ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq φ
  have hcoe :
      (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
        (fun ξ => (𝓕 φ) ξ) := by
    rw [hfourier]
    exact MemLp.coeFn_toLp ((𝓕 φ).memLp 2 volume)
  have hpos : ∀ᵐ w : ℝ ∂volume.restrict (Set.Ioi 0),
      (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) (Real.sqrt w) = (𝓕 φ) (Real.sqrt w) :=
    qmp_sqrt_Ioi_schwartz.ae hcoe
  have hqneg : Measure.QuasiMeasurePreserving (fun w : ℝ => -Real.sqrt w)
      (volume.restrict (Set.Ioi 0)) volume := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp
        qmp_sqrt_Ioi_schwartz
  have hneg : ∀ᵐ w : ℝ ∂volume.restrict (Set.Ioi 0),
      (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) (-Real.sqrt w) =
        (𝓕 φ) (-Real.sqrt w) := hqneg.ae hcoe
  have hin : ∀ᵐ w : ℝ ∂volume.restrict (Set.Ioi 0),
      smoothingB x (φ.toLp 2 volume) w = smoothingBSchwartz x φ w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hpos, hneg] with w hw hp hn
    have hw0 : 0 < w := hw
    simp [smoothingB, smoothingBSchwartz, hw0, hp, hn]
  have hin' := (ae_restrict_iff' measurableSet_Ioi).mp hin
  filter_upwards [hin'] with w hwimp
  by_cases hw : 0 < w
  · exact hwimp hw
  · simp [smoothingB, smoothingBSchwartz, hw]

private theorem smoothingB_schwartz_memLp_one (x : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    MemLp (smoothingB x (φ.toLp 2 volume)) 1 volume :=
  (smoothingBSchwartz_memLp_one x φ).congr_norm
    (homogeneous_smoothing_identity (φ.toLp 2 volume) x).1.1
    ((smoothingB_schwartz_ae x φ).mono fun _ h => by rw [h])

private theorem AxRepresentative_schwartz_ae_inverseIntegral
    (x : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      inverseIntegral (smoothingBSchwartz x φ) := by
  have hactual := l1_l2_fourierInv_bridge
    (smoothingB_schwartz_memLp_one x φ)
    (homogeneous_smoothing_identity (φ.toLp 2 volume) x).1
  have hcanonical : inverseIntegral (smoothingB x (φ.toLp 2 volume)) =
      inverseIntegral (smoothingBSchwartz x φ) := by
    unfold inverseIntegral
    exact VectorFourier.fourierIntegral_congr_ae 𝐞 volume (-innerₗ ℝ)
      (smoothingB_schwartz_ae x φ)
  unfold AxRepresentative
  change ((𝓕⁻ ((homogeneous_smoothing_identity
    (φ.toLp 2 volume) x).1.toLp
      (smoothingB x (φ.toLp 2 volume))) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
        inverseIntegral (smoothingBSchwartz x φ)
  simpa only [hcanonical] using hactual

private def quadraticWeightedSchwartz (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => (((1 + y ^ 2 : ℝ) : ℂ))) φ

private lemma quadraticWeightedSchwartz_apply (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    quadraticWeightedSchwartz φ y = ((1 + y ^ 2 : ℝ) : ℂ) * φ y := by
  have h := SchwartzMap.smulLeftCLM_apply
    (show (fun y : ℝ => (((1 + y ^ 2 : ℝ) : ℂ))).HasTemperateGrowth by fun_prop) φ
  exact congrFun h y

private def canonicalHalfIntegrand (φ : 𝓢(ℝ, ℂ)) (x τ ξ : ℝ) : ℂ :=
  (((|ξ| ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (x * ξ + τ * ξ ^ 2) : ℝ) : ℂ) * Complex.I)) *
      (𝓕 φ) ξ

private lemma canonicalHalfIntegrand_integrable (φ : 𝓢(ℝ, ℂ)) (x τ : ℝ) :
    Integrable (canonicalHalfIntegrand φ x τ) := by
  have hdom := (quadraticWeightedSchwartz (𝓕 φ)).integrable (μ := volume) |>.norm
  apply hdom.mono'
  · unfold canonicalHalfIntegrand
    fun_prop
  · filter_upwards with ξ
    rw [quadraticWeightedSchwartz_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + ξ ^ 2)]
    unfold canonicalHalfIntegrand
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) _)]
    have he : ‖Complex.exp
        (((2 * Real.pi * (x * ξ + τ * ξ ^ 2) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      exact Complex.norm_exp_ofReal_mul_I _
    rw [he, mul_one]
    gcongr
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 1 + ξ ^ 2)).2
    have habs : |ξ| ≤ 1 + ξ ^ 2 := by
      nlinarith [sq_nonneg (|ξ| - 1), sq_abs ξ]
    nlinarith [sq_nonneg ξ]

private def canonicalHalfIntegral (φ : 𝓢(ℝ, ℂ)) (x τ : ℝ) : ℂ :=
  ∫ ξ : ℝ, canonicalHalfIntegrand φ x τ ξ

private def smoothingInverseIntegrand (φ : 𝓢(ℝ, ℂ)) (x τ w : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (w * τ) : ℝ) : ℂ) * Complex.I) *
    smoothingBSchwartz x φ w

private lemma smoothingInverseIntegrand_zero_of_nonpos (φ : 𝓢(ℝ, ℂ))
    (x τ w : ℝ) (hw : w ≤ 0) : smoothingInverseIntegrand φ x τ w = 0 := by
  simp [smoothingInverseIntegrand, smoothingBSchwartz, not_lt_of_ge hw]

set_option maxHeartbeats 300000 in
private lemma inverseIntegral_smoothingBSchwartz_eq_half
    (φ : 𝓢(ℝ, ℂ)) (x τ : ℝ) :
    inverseIntegral (smoothingBSchwartz x φ) τ =
      2 * canonicalHalfIntegral φ x τ := by
  have hbint : Integrable (smoothingBSchwartz x φ) :=
    memLp_one_iff_integrable.mp (smoothingBSchwartz_memLp_one x φ)
  have hKint : Integrable (smoothingInverseIntegrand φ x τ) := by
    refine @Integrable.mono' ℝ ℂ _ volume _
      (smoothingInverseIntegrand φ x τ) (fun w => ‖smoothingBSchwartz x φ w‖)
      hbint.norm ?_ ?_
    · unfold smoothingInverseIntegrand
      fun_prop
    · filter_upwards with w
      unfold smoothingInverseIntegrand
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsource : inverseIntegral (smoothingBSchwartz x φ) τ =
      ∫ w : ℝ, smoothingInverseIntegrand φ x τ w := by
    unfold inverseIntegral
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with w
    simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
    unfold smoothingInverseIntegrand
    congr 2
    push_cast
    ring
  have hsourceIoi : (∫ w : ℝ, smoothingInverseIntegrand φ x τ w) =
      ∫ w : ℝ in Set.Ioi 0, smoothingInverseIntegrand φ x τ w := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : 0 < w
    · simp [Set.indicator, hw]
    · simp [Set.indicator, hw,
        smoothingInverseIntegrand_zero_of_nonpos φ x τ w (le_of_not_gt hw)]
  have hchange := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Ioi (0 : ℝ)) (f := fun y : ℝ => y ^ 2) (f' := fun y => 2 * y)
    measurableSet_Ioi
    (fun y _ => by simpa [pow_two] using (hasDerivAt_pow 2 y).hasDerivWithinAt)
    (fun y hy z hz hyz => by
      nlinarith [mul_nonneg (sub_nonneg.mpr hyz)
        (add_nonneg (show 0 ≤ y from hy.le) (show 0 ≤ z from hz.le))])
    (smoothingInverseIntegrand φ x τ)
  rw [sq_image_Ioi_schwartz] at hchange
  have hpoint (y : ℝ) (hy : y ∈ Set.Ioi (0 : ℝ)) :
      (2 * y) • smoothingInverseIntegrand φ x τ (y ^ 2) =
        (2 : ℂ) * (canonicalHalfIntegrand φ x τ y +
          canonicalHalfIntegrand φ x τ (-y)) := by
    have hy0 : 0 < y := hy
    have hsqrt : Real.sqrt (y ^ 2) = y := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hy0]
    have hweight : (y ^ 2) ^ (-(1 / 4 : ℝ)) = y ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    have habsy : |-y| = y := by rw [abs_neg, abs_of_pos hy0]
    have hcancel : y * y ^ (-(1 / 2 : ℝ)) = y ^ (1 / 2 : ℝ) := by
      calc
        y * y ^ (-(1 / 2 : ℝ)) = y ^ (1 : ℝ) * y ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_one]
        _ = y ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
    have hEplus :
        Complex.exp (((2 * Real.pi * (y ^ 2 * τ) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ)) = Complex.exp
        (((2 * Real.pi * (x * y + τ * y ^ 2) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hEminus :
        Complex.exp (((2 * Real.pi * (y ^ 2 * τ) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ)) = Complex.exp
        (((2 * Real.pi * (x * (-y) + τ * y ^ 2) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hcoef : ((2 * y : ℝ) : ℂ) * ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (2 : ℂ) * ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      calc
        ((2 * y : ℝ) : ℂ) * ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
            (((2 * y) * y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
          (Complex.ofReal_mul _ _).symm
        _ = ((2 * y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
          congr 1
          calc
            2 * y * y ^ (-(1 / 2 : ℝ)) =
                2 * (y * y ^ (-(1 / 2 : ℝ))) := by ring
            _ = 2 * y ^ (1 / 2 : ℝ) := by rw [hcancel]
        _ = (2 : ℂ) * ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
          simpa using Complex.ofReal_mul (2 : ℝ) (y ^ (1 / 2 : ℝ))
    unfold smoothingInverseIntegrand smoothingBSchwartz canonicalHalfIntegrand
    rw [if_pos (sq_pos_of_pos hy0), hsqrt, hweight]
    simp only [Complex.real_smul, neg_sq, habsy]
    rw [abs_of_pos hy0]
    rw [← hEplus, ← hEminus]
    ring_nf at hcoef ⊢
    linear_combination
      (Complex.exp
          (((y ^ 2 * Real.pi * τ * 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (((y * Real.pi * x * 2 : ℝ) : ℂ))) *
          (𝓕 φ) y +
       Complex.exp
          (((y ^ 2 * Real.pi * τ * 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(Complex.I * (((y * Real.pi * x * 2 : ℝ) : ℂ)))) *
          (𝓕 φ) (-y)) * hcoef
  have hchanged :
      (∫ w : ℝ in Set.Ioi 0, smoothingInverseIntegrand φ x τ w) =
        ∫ y : ℝ in Set.Ioi 0,
          (2 : ℂ) * (canonicalHalfIntegrand φ x τ y +
            canonicalHalfIntegrand φ x τ (-y)) := by
    rw [hchange]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hpoint y hy
  have hP := canonicalHalfIntegrand_integrable φ x τ
  have hPneg : Integrable (fun y => canonicalHalfIntegrand φ x τ (-y)) := by
    simpa using hP.comp_neg
  have hneg : (∫ y : ℝ in Set.Ioi 0,
      canonicalHalfIntegrand φ x τ (-y)) =
        ∫ y : ℝ in Set.Iio 0, canonicalHalfIntegrand φ x τ y := by
    have h := integral_comp_neg_Ioi 0 (canonicalHalfIntegrand φ x τ)
    rw [neg_zero, integral_Iic_eq_integral_Iio] at h
    exact h
  have hsplit := integral_add_compl (s := Set.Iio (0 : ℝ))
    measurableSet_Iio hP
  rw [show (Set.Iio (0 : ℝ))ᶜ = Set.Ici 0 by ext y; simp] at hsplit
  rw [integral_Ici_eq_integral_Ioi] at hsplit
  calc
    inverseIntegral (smoothingBSchwartz x φ) τ =
        ∫ w : ℝ in Set.Ioi 0, smoothingInverseIntegrand φ x τ w :=
      hsource.trans hsourceIoi
    _ = ∫ y : ℝ in Set.Ioi 0,
          (2 : ℂ) * (canonicalHalfIntegrand φ x τ y +
            canonicalHalfIntegrand φ x τ (-y)) := hchanged
    _ = (2 : ℂ) * (∫ y : ℝ in Set.Ioi 0,
          (canonicalHalfIntegrand φ x τ y +
            canonicalHalfIntegrand φ x τ (-y))) := by rw [integral_const_mul]
    _ = (2 : ℂ) * ((∫ y : ℝ in Set.Ioi 0,
          canonicalHalfIntegrand φ x τ y) +
        ∫ y : ℝ in Set.Ioi 0,
          canonicalHalfIntegrand φ x τ (-y)) := by
      rw [integral_add hP.integrableOn hPneg.integrableOn]
    _ = (2 : ℂ) * ((∫ y : ℝ in Set.Ioi 0,
          canonicalHalfIntegrand φ x τ y) +
        ∫ y : ℝ in Set.Iio 0,
          canonicalHalfIntegrand φ x τ y) := by rw [hneg]
    _ = 2 * canonicalHalfIntegral φ x τ := by
      unfold canonicalHalfIntegral
      rw [add_comm, hsplit]

private def halfFreeFrequency (φ : 𝓢(ℝ, ℂ)) (t ξ : ℝ) : ℂ :=
  (((|ξ| ^ (1 / 2 : ℝ) : ℝ) : ℂ) * schrodingerSymbol t ξ) * (𝓕 φ) ξ

private lemma halfFreeFrequency_norm_le (φ : 𝓢(ℝ, ℂ)) (t ξ : ℝ) :
    ‖halfFreeFrequency φ t ξ‖ ≤
      ‖quadraticWeightedSchwartz (𝓕 φ) ξ‖ := by
  rw [quadraticWeightedSchwartz_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + ξ ^ 2)]
  unfold halfFreeFrequency
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) _),
    norm_schrodingerSymbol, mul_one]
  gcongr
  rw [← Real.sqrt_eq_rpow]
  apply (Real.sqrt_le_left (by positivity : 0 ≤ 1 + ξ ^ 2)).2
  have habs : |ξ| ≤ 1 + ξ ^ 2 := by
    nlinarith [sq_nonneg (|ξ| - 1), sq_abs ξ]
  nlinarith [sq_nonneg ξ]

private lemma halfFreeFrequency_memLp_one (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    MemLp (halfFreeFrequency φ t) 1 volume := by
  rw [memLp_one_iff_integrable]
  have hmeas : AEStronglyMeasurable (halfFreeFrequency φ t) volume := by
    apply Continuous.aestronglyMeasurable
    unfold halfFreeFrequency
    exact (((Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs)).mul
        (continuous_schrodingerSymbol t)).mul (𝓕 φ).continuous)
  exact ((quadraticWeightedSchwartz (𝓕 φ)).integrable
    (μ := volume) |>.norm).mono'
    hmeas
    (Filter.Eventually.of_forall (halfFreeFrequency_norm_le φ t))

private lemma halfFreeFrequency_memLp_two (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    MemLp (halfFreeFrequency φ t) 2 volume :=
  ((quadraticWeightedSchwartz (𝓕 φ)).memLp 2 volume).mono
    (by
      apply Continuous.aestronglyMeasurable
      unfold halfFreeFrequency
      exact (((Complex.continuous_ofReal.comp
        ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs)).mul
          (continuous_schrodingerSymbol t)).mul (𝓕 φ).continuous))
    (Filter.Eventually.of_forall (halfFreeFrequency_norm_le φ t))

private def halfFreeL2 (φ : 𝓢(ℝ, ℂ)) (t : ℝ) : L2 :=
  fourierL2.symm ((halfFreeFrequency_memLp_two φ t).toLp
    (halfFreeFrequency φ t))

set_option maxHeartbeats 300000 in
private lemma inverseIntegral_halfFreeFrequency (φ : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    inverseIntegral (halfFreeFrequency φ t) x =
      canonicalHalfIntegral φ x (-2 * Real.pi * t) := by
  unfold inverseIntegral canonicalHalfIntegral
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  unfold halfFreeFrequency canonicalHalfIntegrand schrodingerSymbol
  ring_nf
  calc
    Complex.exp (((Real.pi * x * ξ * 2 : ℝ) : ℂ) * Complex.I) *
          (((|ξ| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (((-(Real.pi ^ 2 * ξ ^ 2 * t * 4) : ℝ) : ℂ))) *
        (𝓕 φ) ξ =
      (((|ξ| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * (𝓕 φ) ξ *
        (Complex.exp (((Real.pi * x * ξ * 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (((-(Real.pi ^ 2 * ξ ^ 2 * t * 4) : ℝ) : ℂ)))) := by ring
    _ = (((|ξ| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * (𝓕 φ) ξ *
        Complex.exp
          (((Real.pi * x * ξ * 2 : ℝ) : ℂ) * Complex.I +
            Complex.I * (((-(Real.pi ^ 2 * ξ ^ 2 * t * 4) : ℝ) : ℂ))) := by
      rw [Complex.exp_add]
    _ = _ := by
      congr 2
      push_cast
      ring

private lemma halfFreeL2_ae_canonical (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (halfFreeL2 φ t : ℝ → ℂ) =ᵐ[volume]
      (fun x => canonicalHalfIntegral φ x (-2 * Real.pi * t)) := by
  have h := l1_l2_fourierInv_bridge
    (halfFreeFrequency_memLp_one φ t) (halfFreeFrequency_memLp_two φ t)
  unfold halfFreeL2
  change ((𝓕⁻ ((halfFreeFrequency_memLp_two φ t).toLp
    (halfFreeFrequency φ t)) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] _
  exact h.trans (Filter.Eventually.of_forall fun x =>
    inverseIntegral_halfFreeFrequency φ t x)

private lemma AxRepresentative_schwartz_scaled_ae (x : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (fun t => (AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ)
      (-2 * Real.pi * t)) =ᵐ[volume]
      fun t => 2 * canonicalHalfIntegral φ x (-2 * Real.pi * t) := by
  have hscale : Measure.QuasiMeasurePreserving (fun t : ℝ => -2 * Real.pi * t)
      volume volume := by
    have hn : -2 * Real.pi ≠ 0 := by positivity
    simpa [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hn)
  filter_upwards [hscale.ae
      (AxRepresentative_schwartz_ae_inverseIntegral x φ)] with t ht
  rw [ht, inverseIntegral_smoothingBSchwartz_eq_half]

private def freeFrequencySchwartz (φ : 𝓢(ℝ, ℂ)) (t ξ : ℝ) : ℂ :=
  schrodingerSymbol t ξ * (𝓕 φ) ξ

private lemma freeFrequencySchwartz_memLp_one (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    MemLp (freeFrequencySchwartz φ t) 1 volume := by
  rw [memLp_one_iff_integrable]
  refine ((𝓕 φ).integrable (μ := volume)).mono ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (continuous_schrodingerSymbol t).mul (𝓕 φ).continuous
  · filter_upwards with ξ
    show ‖freeFrequencySchwartz φ t ξ‖ ≤ ‖(𝓕 φ) ξ‖
    simp [freeFrequencySchwartz, norm_schrodingerSymbol]

private lemma freeFrequencySchwartz_memLp_two (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    MemLp (freeFrequencySchwartz φ t) 2 volume := by
  exact (𝓕 φ).memLp 2 volume |>.congr_norm
    (by
      apply Continuous.aestronglyMeasurable
      exact (continuous_schrodingerSymbol t).mul (𝓕 φ).continuous)
    (Filter.Eventually.of_forall fun ξ => by
      simp [freeFrequencySchwartz, norm_schrodingerSymbol])

private def freeFrequencyL2 (φ : 𝓢(ℝ, ℂ)) (t : ℝ) : L2 :=
  (freeFrequencySchwartz_memLp_two φ t).toLp (freeFrequencySchwartz φ t)

private lemma freeFrequencyL2_eq_fourier_freeProp (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    freeFrequencyL2 φ t = fourierL2 (freeProp t (φ.toLp 2 volume)) := by
  have hφfourier : (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (𝓕 φ) ξ := by
    have heq : fourierL2 (φ.toLp 2 volume) = (𝓕 φ).toLp 2 volume := by
      exact SchwartzMap.toLp_fourier_eq φ
    rw [heq]
    exact MemLp.coeFn_toLp ((𝓕 φ).memLp 2 volume)
  apply Lp.ext
  filter_upwards [(freeFrequencySchwartz_memLp_two φ t).coeFn_toLp,
    fourier_freeProp t (φ.toLp 2 volume), hφfourier]
      with ξ hleft hfree hφ
  change ((freeFrequencySchwartz_memLp_two φ t).toLp
    (freeFrequencySchwartz φ t) : ℝ → ℂ) ξ = _
  rw [hleft, hfree, hφ]
  rfl

private lemma freeProp_schwartz_ae_inverseIntegral (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (freeProp t (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      inverseIntegral (freeFrequencySchwartz φ t) := by
  have hbridge := l1_l2_fourierInv_bridge
    (freeFrequencySchwartz_memLp_one φ t)
    (freeFrequencySchwartz_memLp_two φ t)
  have heq : fourierL2.symm (freeFrequencyL2 φ t) =
      freeProp t (φ.toLp 2 volume) := by
    rw [freeFrequencyL2_eq_fourier_freeProp, LinearIsometryEquiv.symm_apply_apply]
  rw [← heq]
  change ((𝓕⁻ ((freeFrequencySchwartz_memLp_two φ t).toLp
    (freeFrequencySchwartz φ t)) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] _
  exact hbridge

private def cutoffFreeFrequency (χ φ : 𝓢(ℝ, ℂ)) (t : ℝ) : ℝ → ℂ :=
  (⇑(FourierTransform.fourier χ) : ℝ → ℂ) ⋆[complexMulCLM]
    freeFrequencySchwartz φ t

private lemma cutoffFreeFrequency_integrable (χ φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Integrable (cutoffFreeFrequency χ φ t) := by
  exact (𝓕 χ).integrable.integrable_convolution complexMulCLM
    (memLp_one_iff_integrable.mp (freeFrequencySchwartz_memLp_one φ t))

private lemma cutoffFreeFrequency_memLp_two (χ φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    MemLp (cutoffFreeFrequency χ φ t) 2 volume := by
  exact convolution_mul_memLp_two (⇑(FourierTransform.fourier χ) : ℝ → ℂ)
    (freeFrequencySchwartz φ t) (𝓕 χ).continuous.measurable
    ((continuous_schrodingerSymbol t).mul (𝓕 φ).continuous).measurable
    (𝓕 χ).integrable (freeFrequencySchwartz_memLp_two φ t)

private lemma inverseIntegral_fourier_schwartz (χ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    inverseIntegral (⇑(FourierTransform.fourier χ) : ℝ → ℂ) x = χ x := by
  unfold inverseIntegral
  rw [← SchwartzMap.fourierInv_coe]
  simp

private lemma inverseIntegral_cutoffFreeFrequency (χ φ : 𝓢(ℝ, ℂ))
    (t x : ℝ) :
    inverseIntegral (cutoffFreeFrequency χ φ t) x =
      χ x * inverseIntegral (freeFrequencySchwartz φ t) x := by
  rw [cutoffFreeFrequency, inverseIntegral_convolution_mul
    (⇑(FourierTransform.fourier χ) : ℝ → ℂ) (freeFrequencySchwartz φ t)
    (𝓕 χ).integrable
    (memLp_one_iff_integrable.mp (freeFrequencySchwartz_memLp_one φ t)),
    inverseIntegral_fourier_schwartz]

private lemma sqrt_abs_sub_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a hb ha (le_of_not_ge hab)
    simpa [abs_sub_comm] using h
  have hsqa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hsqb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have hsle : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hdiff : 0 ≤ Real.sqrt b - Real.sqrt a := sub_nonneg.mpr hsle
  have hsq : (Real.sqrt b - Real.sqrt a) ^ 2 ≤ b - a := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [abs_sub_comm, abs_of_nonneg hdiff, abs_of_nonpos (sub_nonpos.mpr hab)]
  have heq : -(a - b) = b - a := by ring
  rw [heq]
  exact (Real.le_sqrt (by positivity) (sub_nonneg.mpr hab)).2 hsq

private lemma sqrt_abs_difference_le (xi y : ℝ) :
    abs (|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ)) ≤
      |y| ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  calc
    abs (Real.sqrt |xi| - Real.sqrt |xi - y|) ≤
        Real.sqrt (abs (|xi| - |xi - y|)) := by
      exact sqrt_abs_sub_le _ _ (abs_nonneg _) (abs_nonneg _)
    _ ≤ Real.sqrt |y| := by
      apply Real.sqrt_le_sqrt
      calc
        abs (|xi| - |xi - y|) ≤ |xi - (xi - y)| :=
          abs_abs_sub_abs_le_abs_sub _ _
        _ = |y| := by ring_nf

private def cutoffHalfFrequency (χ φ : SchwartzMap ℝ ℂ) (t : ℝ) : ℝ → ℂ :=
  (⇑(FourierTransform.fourier χ) : ℝ → ℂ) ⋆[complexMulCLM]
    halfFreeFrequency φ t

private def cutoffCommutatorFrequency (χ φ : SchwartzMap ℝ ℂ)
    (t xi : ℝ) : ℂ :=
  ∫ y : ℝ, (𝓕 χ) y *
    (((|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
      freeFrequencySchwartz φ t (xi - y)

private def homogeneousCutoffFrequency (χ φ : SchwartzMap ℝ ℂ)
    (t xi : ℝ) : ℂ :=
  (((|xi| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * cutoffFreeFrequency χ φ t xi

private def commutatorKernel (χ : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ :=
  (((|y| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * (𝓕 χ) y

private lemma commutatorKernel_memLp_two (χ : SchwartzMap ℝ ℂ) :
    MemLp (commutatorKernel χ) 2 volume := by
  refine (quadraticWeightedSchwartz (𝓕 χ)).memLp 2 volume |>.mono ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold commutatorKernel
    fun_prop
  · filter_upwards with y
    rw [quadraticWeightedSchwartz_apply, commutatorKernel, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _),
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + y ^ 2)]
    gcongr
    rw [← Real.sqrt_eq_rpow]
    have hsqrt := Real.sq_sqrt (abs_nonneg y)
    have hsqrt0 := Real.sqrt_nonneg |y|
    by_cases hy : |y| ≤ 1
    · nlinarith [sq_nonneg y]
    · have hy' : 1 ≤ |y| := le_of_not_ge hy
      nlinarith [sq_abs y, sq_nonneg (Real.sqrt |y| - 1)]

private lemma main_integrand_integrable (χ φ : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    Integrable (fun y : ℝ => (𝓕 χ) y * halfFreeFrequency φ t (xi - y)) := by
  have htrans : MemLp (fun y : ℝ => halfFreeFrequency φ t (xi - y)) 2 volume := by
    simpa [Function.comp_def] using
      (halfFreeFrequency_memLp_two φ t).comp_measurePreserving
        ((volume : Measure ℝ).measurePreserving_sub_left xi)
  exact memLp_one_iff_integrable.mp (htrans.mul' ((𝓕 χ).memLp 2 volume))

private lemma commutator_integrand_integrable (χ φ : SchwartzMap ℝ ℂ)
    (t xi : ℝ) : Integrable (fun y : ℝ => (𝓕 χ) y *
      (((|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
        freeFrequencySchwartz φ t (xi - y)) := by
  let majorant : ℝ → ℂ := fun y =>
    commutatorKernel χ y * (𝓕 φ) (xi - y)
  have htrans : MemLp (fun y : ℝ => (𝓕 φ) (xi - y)) 2 volume := by
    simpa [Function.comp_def] using
      ((𝓕 φ).memLp 2 volume).comp_measurePreserving
        ((volume : Measure ℝ).measurePreserving_sub_left xi)
  have hmajorant : Integrable majorant :=
    memLp_one_iff_integrable.mp (htrans.mul' (commutatorKernel_memLp_two χ))
  refine hmajorant.mono ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have hweight : Continuous (fun y : ℝ =>
        ((|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        (continuous_const.sub
          ((continuous_abs.comp (continuous_const.sub continuous_id)).rpow_const
            (fun _ => Or.inr (by norm_num))))
    exact ((𝓕 χ).continuous.measurable.mul hweight.measurable).mul
      (((continuous_schrodingerSymbol t).mul (𝓕 φ).continuous).measurable.comp
        (measurable_const.sub measurable_id))
  · filter_upwards with y
    dsimp only [majorant]
    change ‖(𝓕 χ) y *
        (((|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          freeFrequencySchwartz φ t (xi - y)‖ ≤
      ‖commutatorKernel χ y * (𝓕 φ) (xi - y)‖
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsymbol : ‖schrodingerSymbol t (xi - y)‖ = 1 :=
      norm_schrodingerSymbol _ _
    unfold freeFrequencySchwartz
    rw [norm_mul, hsymbol, one_mul]
    calc
      ‖(𝓕 χ) y‖ *
          abs (|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ)) *
            ‖(𝓕 φ) (xi - y)‖ ≤
        ‖(𝓕 χ) y‖ * |y| ^ (1 / 2 : ℝ) *
            ‖(𝓕 φ) (xi - y)‖ := by
          gcongr
          exact sqrt_abs_difference_le xi y
      _ = ‖commutatorKernel χ y‖ * ‖(𝓕 φ) (xi - y)‖ := by
        rw [commutatorKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
        ring

private lemma homogeneousCutoffFrequency_eq (χ φ : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    homogeneousCutoffFrequency χ φ t xi =
      cutoffHalfFrequency χ φ t xi + cutoffCommutatorFrequency χ φ t xi := by
  unfold homogeneousCutoffFrequency cutoffFreeFrequency cutoffHalfFrequency
    cutoffCommutatorFrequency convolution
  rw [← integral_const_mul]
  change (∫ a : ℝ, (((|xi| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
      ((𝓕 χ) a * freeFrequencySchwartz φ t (xi - a))) =
    (∫ a : ℝ, (𝓕 χ) a * halfFreeFrequency φ t (xi - a)) +
      ∫ a : ℝ, (𝓕 χ) a *
        (((|xi| ^ (1 / 2 : ℝ) - |xi - a| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          freeFrequencySchwartz φ t (xi - a)
  rw [← integral_add (main_integrand_integrable χ φ t xi)
    (commutator_integrand_integrable χ φ t xi)]
  apply integral_congr_ae
  filter_upwards with y
  unfold halfFreeFrequency freeFrequencySchwartz
  push_cast
  ring

private def commutatorKernelReal (χ : SchwartzMap ℝ ℂ) (y : ℝ) : ℝ :=
  |y| ^ (1 / 2 : ℝ) * ‖(𝓕 χ) y‖

private def fourierNormReal (φ : SchwartzMap ℝ ℂ) (y : ℝ) : ℝ :=
  ‖(𝓕 φ) y‖

private def commutatorMajorant (χ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  (fun y => ((commutatorKernelReal χ y : ℝ) : ℂ)) ⋆[complexMulCLM]
    fun y => ((fourierNormReal φ y : ℝ) : ℂ)

private lemma commutatorKernelReal_integrable (χ : SchwartzMap ℝ ℂ) :
    Integrable (commutatorKernelReal χ) := by
  refine (quadraticWeightedSchwartz (𝓕 χ)).integrable.norm.mono ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold commutatorKernelReal
    exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs).mul
      (𝓕 χ).continuous.norm
  · filter_upwards with y
    unfold commutatorKernelReal
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (abs_nonneg y) _) (norm_nonneg _)),
      abs_of_nonneg (norm_nonneg _)]
    rw [quadraticWeightedSchwartz_apply, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 + y ^ 2)]
    gcongr
    rw [← Real.sqrt_eq_rpow]
    have hsqrt := Real.sq_sqrt (abs_nonneg y)
    have hsqrt0 := Real.sqrt_nonneg |y|
    by_cases hy : |y| ≤ 1
    · nlinarith [sq_nonneg y]
    · have hy' : 1 ≤ |y| := le_of_not_ge hy
      nlinarith [sq_abs y, sq_nonneg (Real.sqrt |y| - 1)]

private lemma fourierNormReal_memLp_two (φ : SchwartzMap ℝ ℂ) :
    MemLp (fourierNormReal φ) 2 volume := by
  simpa [fourierNormReal] using (𝓕 φ).memLp 2 volume |>.norm

private lemma commutatorMajorant_memLp_two (χ φ : SchwartzMap ℝ ℂ) :
    MemLp (commutatorMajorant χ φ) 2 volume := by
  apply convolution_mul_memLp_two
  · exact (Complex.continuous_ofReal.comp (by
      unfold commutatorKernelReal
      exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs).mul
        (𝓕 χ).continuous.norm)).measurable
  · exact (Complex.continuous_ofReal.comp (by
      unfold fourierNormReal
      fun_prop)).measurable
  · exact Complex.ofRealCLM.integrable_comp
      (commutatorKernelReal_integrable χ)
  · exact (fourierNormReal_memLp_two φ).ofReal

private lemma norm_cutoffCommutatorFrequency_le (χ φ : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    ‖cutoffCommutatorFrequency χ φ t xi‖ ≤ ‖commutatorMajorant χ φ xi‖ := by
  let r : ℝ → ℝ := fun y =>
    commutatorKernelReal χ y * fourierNormReal φ (xi - y)
  have hr : Integrable r := by
    have htrans : MemLp (fun y : ℝ => fourierNormReal φ (xi - y)) 2 volume := by
      simpa [Function.comp_def] using
        (fourierNormReal_memLp_two φ).comp_measurePreserving
          ((volume : Measure ℝ).measurePreserving_sub_left xi)
    exact memLp_one_iff_integrable.mp
      (htrans.mul' (by
        exact (commutatorKernel_memLp_two χ).congr_norm
          (by
            apply Continuous.aestronglyMeasurable
            unfold commutatorKernelReal
            exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs).mul
              (𝓕 χ).continuous.norm)
          (Filter.Eventually.of_forall fun y => by
            rw [commutatorKernelReal, commutatorKernel, norm_mul,
              Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _),
              Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
                (Real.rpow_nonneg (abs_nonneg y) _) (norm_nonneg _))])))
  have hmajorant : commutatorMajorant χ φ xi = ((∫ y, r y : ℝ) : ℂ) := by
    unfold commutatorMajorant convolution
    simpa [r, complexMulCLM] using Complex.ofRealCLM.integral_comp_comm hr
  calc
    ‖cutoffCommutatorFrequency χ φ t xi‖ ≤
        ∫ y, ‖(𝓕 χ) y *
          (((|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
            freeFrequencySchwartz φ t (xi - y)‖ := by
      unfold cutoffCommutatorFrequency
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, r y := by
      apply integral_mono_ae
      · exact (commutator_integrand_integrable χ φ t xi).norm
      · exact hr
      · filter_upwards with y
        dsimp only [r]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        unfold freeFrequencySchwartz
        rw [norm_mul, norm_schrodingerSymbol, one_mul, commutatorKernelReal,
          fourierNormReal]
        calc
          ‖(𝓕 χ) y‖ *
                abs (|xi| ^ (1 / 2 : ℝ) - |xi - y| ^ (1 / 2 : ℝ)) *
              ‖(𝓕 φ) (xi - y)‖ ≤
            ‖(𝓕 χ) y‖ * |y| ^ (1 / 2 : ℝ) *
              ‖(𝓕 φ) (xi - y)‖ := by
                gcongr
                exact sqrt_abs_difference_le xi y
          _ = |y| ^ (1 / 2 : ℝ) * ‖(𝓕 χ) y‖ *
              ‖(𝓕 φ) (xi - y)‖ := by ring
    _ = ‖commutatorMajorant χ φ xi‖ := by
      rw [hmajorant, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact integral_nonneg (fun y => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (abs_nonneg y) _) (norm_nonneg _))
        (norm_nonneg _))

private lemma cutoffCommutatorFrequency_memLp_two (χ φ : SchwartzMap ℝ ℂ)
    (t : ℝ) : MemLp (cutoffCommutatorFrequency χ φ t) 2 volume := by
  refine (commutatorMajorant_memLp_two χ φ).mono ?_ ?_
  · have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (𝓕 χ) p.2 *
          (((|p.1| ^ (1 / 2 : ℝ) - |p.1 - p.2| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
            freeFrequencySchwartz φ t (p.1 - p.2)) (volume.prod volume) := by
      apply Continuous.aestronglyMeasurable
      unfold freeFrequencySchwartz
      have hweight : Continuous (fun p : ℝ × ℝ =>
          ((|p.1| ^ (1 / 2 : ℝ) - |p.1 - p.2| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
        exact Complex.continuous_ofReal.comp
          (((Real.continuous_rpow_const (by norm_num)).comp
              (continuous_abs.comp continuous_fst)).sub
            ((Real.continuous_rpow_const (by norm_num)).comp
              (continuous_abs.comp (continuous_fst.sub continuous_snd))))
      exact (((𝓕 χ).continuous.comp continuous_snd).mul hweight).mul
        (((continuous_schrodingerSymbol t).mul (𝓕 φ).continuous).comp
          (continuous_fst.sub continuous_snd))
    exact hjoint.integral_prod_right'
  · exact Filter.Eventually.of_forall (norm_cutoffCommutatorFrequency_le χ φ t)

private lemma cutoffHalfFrequency_integrable (χ φ : SchwartzMap ℝ ℂ)
    (t : ℝ) : Integrable (cutoffHalfFrequency χ φ t) := by
  exact (𝓕 χ).integrable.integrable_convolution complexMulCLM
    (memLp_one_iff_integrable.mp (halfFreeFrequency_memLp_one φ t))

private lemma cutoffHalfFrequency_memLp_two (χ φ : SchwartzMap ℝ ℂ)
    (t : ℝ) : MemLp (cutoffHalfFrequency χ φ t) 2 volume := by
  exact convolution_mul_memLp_two (⇑(FourierTransform.fourier χ) : ℝ → ℂ)
    (halfFreeFrequency φ t) (𝓕 χ).continuous.measurable
    (by
      unfold halfFreeFrequency
      exact (((Complex.continuous_ofReal.comp
        ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs)).mul
          (continuous_schrodingerSymbol t)).mul (𝓕 φ).continuous).measurable)
    (𝓕 χ).integrable (halfFreeFrequency_memLp_two φ t)

private lemma inverseIntegral_cutoffHalfFrequency (χ φ : SchwartzMap ℝ ℂ)
    (t x : ℝ) :
    inverseIntegral (cutoffHalfFrequency χ φ t) x =
      χ x * canonicalHalfIntegral φ x (-2 * Real.pi * t) := by
  rw [cutoffHalfFrequency, inverseIntegral_convolution_mul
    (⇑(FourierTransform.fourier χ) : ℝ → ℂ) (halfFreeFrequency φ t)
    (𝓕 χ).integrable
    (memLp_one_iff_integrable.mp (halfFreeFrequency_memLp_one φ t)),
    inverseIntegral_fourier_schwartz, inverseIntegral_halfFreeFrequency]

private lemma lintegral_enorm_sq_toLp {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ)) =
      ‖hf.toLp f‖ₑ ^ (2 : ℕ) := by
  calc
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ)) =
        eLpNorm f 2 volume ^ (2 : ℝ) := by
      symm
      simpa using (eLpNorm_nnreal_pow_eq_lintegral
        (f := f) (p := (2 : NNReal)) (show (2 : NNReal) ≠ 0 by norm_num))
    _ = ‖hf.toLp f‖ₑ ^ (2 : ℕ) := by
      rw [Lp.enorm_toLp hf]
      norm_num

private lemma lintegral_cutoffHalfFrequency_eq_physical
    (χ φ : SchwartzMap ℝ ℂ) (t : ℝ) :
    (∫⁻ xi : ℝ, ‖cutoffHalfFrequency χ φ t xi‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x : ℝ, ‖χ x * canonicalHalfIntegral φ x (-2 * Real.pi * t)‖ₑ ^
        (2 : ℝ) := by
  let q : L2 := (cutoffHalfFrequency_memLp_two χ φ t).toLp
    (cutoffHalfFrequency χ φ t)
  let qInv : L2 := fourierL2.symm q
  have hqInv : (qInv : ℝ → ℂ) =ᵐ[volume]
      fun x => χ x * canonicalHalfIntegral φ x (-2 * Real.pi * t) := by
    have hbridge := l1_l2_fourierInv_bridge
      (by simpa [cutoffHalfFrequency] using
        (memLp_one_iff_integrable.mpr (cutoffHalfFrequency_integrable χ φ t)))
      (cutoffHalfFrequency_memLp_two χ φ t)
    change ((𝓕⁻ ((cutoffHalfFrequency_memLp_two χ φ t).toLp
      (cutoffHalfFrequency χ φ t)) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] _
    exact hbridge.trans (Filter.Eventually.of_forall
      (inverseIntegral_cutoffHalfFrequency χ φ t))
  have hphysMem : MemLp
      (fun x => χ x * canonicalHalfIntegral φ x (-2 * Real.pi * t)) 2 volume :=
    (Lp.memLp qInv).congr_norm
      ((Lp.aestronglyMeasurable qInv).congr hqInv)
      (hqInv.mono fun x hx => by rw [hx])
  calc
    (∫⁻ xi : ℝ, ‖cutoffHalfFrequency χ φ t xi‖ₑ ^ (2 : ℝ)) =
        ‖q‖ₑ ^ (2 : ℕ) := lintegral_enorm_sq_toLp _
    _ = ‖qInv‖ₑ ^ (2 : ℕ) := by
      rw [show qInv = fourierL2.symm q by rfl, LinearIsometryEquiv.enorm_map]
    _ = ‖hphysMem.toLp
          (fun x => χ x * canonicalHalfIntegral φ x (-2 * Real.pi * t))‖ₑ ^
          (2 : ℕ) := by
      have heqLp : qInv = hphysMem.toLp
          (fun x => χ x * canonicalHalfIntegral φ x (-2 * Real.pi * t)) := by
        apply Lp.ext
        filter_upwards [hphysMem.coeFn_toLp, hqInv] with x hx hq
        rw [hx, hq]
      rw [heqLp]
    _ = _ := (lintegral_enorm_sq_toLp hphysMem).symm

private def cutoffHalfPhysicalSquare (χ φ : SchwartzMap ℝ ℂ)
    (p : ℝ × ℝ) : ℝ :=
  ‖χ p.1 * canonicalHalfIntegral φ p.1 (-2 * Real.pi * p.2)‖ ^ 2

private lemma cutoffHalfPhysicalSquare_aestronglyMeasurable
    (χ φ : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (cutoffHalfPhysicalSquare χ φ)
      (volume.prod volume) := by
  have hjoint : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      canonicalHalfIntegrand φ p.1.1 (-2 * Real.pi * p.1.2) p.2)
      ((volume.prod volume).prod volume) := by
    apply Continuous.aestronglyMeasurable
    unfold canonicalHalfIntegrand
    have hweight : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        (((|p.2| ^ (1 / 2 : ℝ) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp
        ((Real.continuous_rpow_const (by norm_num)).comp
          (continuous_abs.comp continuous_snd))
    have hphase : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        Complex.exp (((2 * Real.pi *
          (p.1.1 * p.2 + (-2 * Real.pi * p.1.2) * p.2 ^ 2) : ℝ) : ℂ) *
            Complex.I)) := by fun_prop
    exact (hweight.mul hphase).mul ((𝓕 φ).continuous.comp continuous_snd)
  have hcomp : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonicalHalfIntegral φ p.1 (-2 * Real.pi * p.2))
      (volume.prod volume) := by
    simpa [canonicalHalfIntegral] using hjoint.integral_prod_right'
  unfold cutoffHalfPhysicalSquare
  have hm :=
    (((χ.continuous.comp continuous_fst).aestronglyMeasurable.mul hcomp).norm.pow 2)
  exact hm.congr (Filter.Eventually.of_forall fun p => by
    simp only [Pi.pow_apply, Pi.mul_apply, Function.comp_apply, norm_mul])

private lemma cutoffHalfPhysicalSquare_section_integrable
    (χ φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun t => cutoffHalfPhysicalSquare χ φ (x, t)) := by
  have hAxSq : Integrable (fun tau : ℝ =>
      ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) tau‖ ^ 2) := by
    exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (AxRepresentative x (φ.toLp 2 volume)))).mp
        (Lp.memLp (AxRepresentative x (φ.toLp 2 volume)))
  have hscale := hAxSq.comp_mul_left'
    (show -2 * Real.pi ≠ 0 by positivity)
  have hdom : Integrable (fun t : ℝ =>
      ‖χ x‖ ^ 2 / 4 *
        ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ)
          (-2 * Real.pi * t)‖ ^ 2) := by
    exact hscale.const_mul (‖χ x‖ ^ 2 / 4)
  apply hdom.congr
  filter_upwards [AxRepresentative_schwartz_scaled_ae x φ] with t ht
  unfold cutoffHalfPhysicalSquare
  rw [ht, norm_mul, norm_mul]
  norm_num
  ring

private def cutoffHalfBoundConstant (φ : SchwartzMap ℝ ℂ) : ℝ :=
  abs ((-2 * Real.pi)⁻¹) *
    ((Classical.choose point_smoothing *
      ENNReal.ofReal ‖φ.toLp 2 volume‖).toReal) ^ 2 / 4

private lemma cutoffHalfBoundConstant_nonneg (φ : SchwartzMap ℝ ℂ) :
    0 ≤ cutoffHalfBoundConstant φ := by
  unfold cutoffHalfBoundConstant
  positivity

private lemma integral_cutoffHalfPhysicalSquare_le
    (χ φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ∫ t, cutoffHalfPhysicalSquare χ φ (x, t) ≤
      cutoffHalfBoundConstant φ * ‖χ x‖ ^ 2 := by
  let C0 : ℝ≥0∞ := Classical.choose point_smoothing
  have hC0top : C0 < ⊤ := (Classical.choose_spec point_smoothing).1
  have hC0 := (Classical.choose_spec point_smoothing).2
  let A : ℝ := (C0 * ENNReal.ofReal ‖φ.toLp 2 volume‖).toReal
  have hAtop : C0 * ENNReal.ofReal ‖φ.toLp 2 volume‖ ≠ ⊤ :=
    (ENNReal.mul_lt_top hC0top (by finiteness)).ne
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hAxNorm : ‖AxRepresentative x (φ.toLp 2 volume)‖ ≤ A := by
    have hE : ENNReal.ofReal ‖AxRepresentative x (φ.toLp 2 volume)‖ ≤
        C0 * ENNReal.ofReal ‖φ.toLp 2 volume‖ :=
      hC0 (φ.toLp 2 volume) x
    rw [← ENNReal.toReal_ofReal (norm_nonneg _)]
    exact ENNReal.toReal_mono hAtop hE
  have hAxSq : Integrable (fun tau : ℝ =>
      ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) tau‖ ^ 2) := by
    exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (AxRepresentative x (φ.toLp 2 volume)))).mp
        (Lp.memLp (AxRepresentative x (φ.toLp 2 volume)))
  have hformula : ∫ t, cutoffHalfPhysicalSquare χ φ (x, t) =
      ‖χ x‖ ^ 2 / 4 * abs ((-2 * Real.pi)⁻¹) *
        ‖AxRepresentative x (φ.toLp 2 volume)‖ ^ 2 := by
    calc
      ∫ t, cutoffHalfPhysicalSquare χ φ (x, t) =
          ∫ t, ‖χ x‖ ^ 2 / 4 *
            ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ)
              (-2 * Real.pi * t)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [AxRepresentative_schwartz_scaled_ae x φ] with t ht
        unfold cutoffHalfPhysicalSquare
        rw [ht, norm_mul, norm_mul]
        norm_num
        ring
      _ = ‖χ x‖ ^ 2 / 4 * ∫ t,
            ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ)
              (-2 * Real.pi * t)‖ ^ 2 := by rw [integral_const_mul]
      _ = ‖χ x‖ ^ 2 / 4 * abs ((-2 * Real.pi)⁻¹) *
          ∫ tau, ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) tau‖ ^ 2 := by
        have hscale := Measure.integral_comp_mul_left
          (fun tau : ℝ =>
            ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) tau‖ ^ 2)
          (-2 * Real.pi)
        simp only [smul_eq_mul] at hscale
        rw [hscale]
        ring
      _ = _ := by
        rw [show (∫ tau,
            ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) tau‖ ^ 2) =
            ‖AxRepresentative x (φ.toLp 2 volume)‖ ^ 2 by
          have h := lpNorm_eq_integral_norm_rpow_toReal
            (f := (AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ))
            (p := (2 : ENNReal)) (by norm_num) (by norm_num)
            (Lp.aestronglyMeasurable (AxRepresentative x (φ.toLp 2 volume)))
          have hlp : lpNorm
              (AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) 2 volume =
              ‖AxRepresentative x (φ.toLp 2 volume)‖ := by
            rw [lpNorm, if_pos
              (Lp.aestronglyMeasurable (AxRepresentative x (φ.toLp 2 volume))),
              Lp.norm_def]
          rw [hlp] at h
          norm_num at h
          rw [← Real.sqrt_eq_rpow] at h
          have hi : 0 ≤ ∫ tau,
              ‖(AxRepresentative x (φ.toLp 2 volume) : ℝ → ℂ) tau‖ ^ 2 :=
            integral_nonneg (fun _ => sq_nonneg _)
          rw [h, Real.sq_sqrt hi]]
  rw [hformula]
  have hsquare : ‖AxRepresentative x (φ.toLp 2 volume)‖ ^ 2 ≤ A ^ 2 := by
    gcongr
  calc
    ‖χ x‖ ^ 2 / 4 * abs ((-2 * Real.pi)⁻¹) *
        ‖AxRepresentative x (φ.toLp 2 volume)‖ ^ 2 ≤
      ‖χ x‖ ^ 2 / 4 * abs ((-2 * Real.pi)⁻¹) * A ^ 2 := by
        gcongr
    _ = cutoffHalfBoundConstant φ * ‖χ x‖ ^ 2 := by
      simp only [cutoffHalfBoundConstant, A, C0]
      ring

private lemma cutoffHalfPhysicalSquare_integrable
    (chi phi : SchwartzMap ℝ ℂ) :
    Integrable (cutoffHalfPhysicalSquare chi phi)
      (volume.prod volume) := by
  rw [integrable_prod_iff
    (cutoffHalfPhysicalSquare_aestronglyMeasurable chi phi)]
  constructor
  · exact Filter.Eventually.of_forall
      (cutoffHalfPhysicalSquare_section_integrable chi phi)
  · have hchiSq : Integrable (fun x : ℝ => ‖chi x‖ ^ 2) volume := by
      exact (memLp_two_iff_integrable_sq_norm
        chi.continuous.aestronglyMeasurable).mp (chi.memLp 2 volume)
    have houterMeas : AEStronglyMeasurable (fun x : ℝ =>
        ∫ t : ℝ, ‖cutoffHalfPhysicalSquare chi phi (x, t)‖) volume :=
      (cutoffHalfPhysicalSquare_aestronglyMeasurable chi phi).norm.integral_prod_right'
    refine (hchiSq.const_mul (cutoffHalfBoundConstant phi)).mono'
      houterMeas ?_
    filter_upwards with x
    have hnonneg : 0 ≤ ∫ t : ℝ, cutoffHalfPhysicalSquare chi phi (x, t) :=
      integral_nonneg fun t => by
        unfold cutoffHalfPhysicalSquare
        positivity
    have hintNorm :
        (∫ t : ℝ, ‖cutoffHalfPhysicalSquare chi phi (x, t)‖) =
          ∫ t : ℝ, cutoffHalfPhysicalSquare chi phi (x, t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold cutoffHalfPhysicalSquare
      positivity
    calc
      ‖∫ t : ℝ, ‖cutoffHalfPhysicalSquare chi phi (x, t)‖‖ =
          ∫ t : ℝ, cutoffHalfPhysicalSquare chi phi (x, t) := by
        rw [hintNorm, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ cutoffHalfBoundConstant phi * ‖chi x‖ ^ 2 :=
        integral_cutoffHalfPhysicalSquare_le chi phi x

private lemma cutoffHalfFrequency_joint_aestronglyMeasurable
    (chi phi : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      cutoffHalfFrequency chi phi p.1 p.2) (volume.prod volume) := by
  have hjoint : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (FourierTransform.fourier chi) p.2 *
        halfFreeFrequency phi p.1.1 (p.1.2 - p.2))
      ((volume.prod volume).prod volume) := by
    apply Continuous.aestronglyMeasurable
    unfold halfFreeFrequency
    have hdiff : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1.2 - p.2) :=
      (continuous_snd.comp continuous_fst).sub continuous_snd
    have hweight : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        (((|p.1.2 - p.2| ^ (1 / 2 : ℝ) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp
        ((Real.continuous_rpow_const (by norm_num)).comp
          (continuous_abs.comp hdiff))
    have hsymbol : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        schrodingerSymbol p.1.1 (p.1.2 - p.2)) := by
      unfold schrodingerSymbol
      fun_prop
    convert ((((FourierTransform.fourier chi).continuous.comp continuous_snd).mul
      hweight).mul
        (hsymbol.mul ((FourierTransform.fourier phi).continuous.comp hdiff))) using 1
    funext p
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  simpa [cutoffHalfFrequency, convolution, complexMulCLM] using
    hjoint.integral_prod_right'

private lemma cutoffHalfFrequency_memLp_two_prod
    (chi phi : SchwartzMap ℝ ℂ) :
    MemLp (fun p : ℝ × ℝ => cutoffHalfFrequency chi phi p.1 p.2) 2
      (volume.prod volume) := by
  let Q : ℝ × ℝ → ℂ := fun p => cutoffHalfFrequency chi phi p.1 p.2
  let P : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ‖chi p.1 * canonicalHalfIntegral phi p.1 (-2 * Real.pi * p.2)‖ₑ ^
      (2 : ℝ)
  have hQmeas : AEStronglyMeasurable Q (volume.prod volume) :=
    cutoffHalfFrequency_joint_aestronglyMeasurable chi phi
  have hPmeas : AEMeasurable P (volume.prod volume) := by
    have hsquare := cutoffHalfPhysicalSquare_aestronglyMeasurable chi phi
    refine hsquare.enorm.congr ?_
    filter_upwards with p
    unfold P cutoffHalfPhysicalSquare
    rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
    norm_num [← ofReal_norm]
  refine ⟨hQmeas, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  norm_num only [ENNReal.toReal_ofNat]
  apply ne_of_lt
  rw [lintegral_prod _ (hQmeas.enorm.pow_const 2)]
  calc
    (∫⁻ t : ℝ, ∫⁻ xi : ℝ, ‖Q (t, xi)‖ₑ ^ (2 : ℝ)) =
        ∫⁻ t : ℝ, ∫⁻ x : ℝ, P (x, t) := by
      apply lintegral_congr
      intro t
      exact lintegral_cutoffHalfFrequency_eq_physical chi phi t
    _ = ∫⁻ x : ℝ, ∫⁻ t : ℝ, P (x, t) := by
      exact lintegral_lintegral_swap hPmeas.prod_swap
    _ = ∫⁻ p : ℝ × ℝ, P p := lintegral_lintegral hPmeas
    _ = ∫⁻ p : ℝ × ℝ, ‖cutoffHalfPhysicalSquare chi phi p‖ₑ := by
      apply lintegral_congr
      intro p
      unfold P cutoffHalfPhysicalSquare
      rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
      norm_num [← ofReal_norm]
    _ < ⊤ := (cutoffHalfPhysicalSquare_integrable chi phi).hasFiniteIntegral

private lemma cutoffCommutatorFrequency_joint_aestronglyMeasurable
    (chi phi : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      cutoffCommutatorFrequency chi phi p.1 p.2) (volume.prod volume) := by
  have hjoint : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (FourierTransform.fourier chi) p.2 *
        (((|p.1.2| ^ (1 / 2 : ℝ) -
          |p.1.2 - p.2| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          freeFrequencySchwartz phi p.1.1 (p.1.2 - p.2))
      ((volume.prod volume).prod volume) := by
    apply Continuous.aestronglyMeasurable
    unfold freeFrequencySchwartz
    have hdiff : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1.2 - p.2) :=
      (continuous_snd.comp continuous_fst).sub continuous_snd
    have hweight : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        (((|p.1.2| ^ (1 / 2 : ℝ) -
          |p.1.2 - p.2| ^ (1 / 2 : ℝ) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp
        (((Real.continuous_rpow_const (by norm_num)).comp
          (continuous_abs.comp (continuous_snd.comp continuous_fst))).sub
        ((Real.continuous_rpow_const (by norm_num)).comp
          (continuous_abs.comp hdiff)))
    have hsymbol : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        schrodingerSymbol p.1.1 (p.1.2 - p.2)) := by
      unfold schrodingerSymbol
      fun_prop
    convert (((((FourierTransform.fourier chi).continuous.comp continuous_snd).mul
      hweight).mul hsymbol).mul
        ((FourierTransform.fourier phi).continuous.comp hdiff)) using 1
    funext p
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  simpa [cutoffCommutatorFrequency] using hjoint.integral_prod_right'

private lemma cutoffCommutatorFrequency_memLp_two_prod_Icc
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    MemLp (fun p : ℝ × ℝ => cutoffCommutatorFrequency chi phi p.1 p.2) 2
      ((volume.restrict (Icc a b)).prod volume) := by
  have hmeasure :
      ((volume : Measure ℝ).restrict (Icc a b)).prod (volume : Measure ℝ) ≤
        (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hmeas :=
    (cutoffCommutatorFrequency_joint_aestronglyMeasurable chi phi).mono_measure
      hmeasure
  have hmajorant : MemLp (fun p : ℝ × ℝ =>
      commutatorMajorant chi phi p.2) 2
      ((volume.restrict (Icc a b)).prod volume) :=
    (commutatorMajorant_memLp_two chi phi).comp_snd
      (volume.restrict (Icc a b))
  exact hmajorant.mono hmeas (Filter.Eventually.of_forall fun p =>
    norm_cutoffCommutatorFrequency_le chi phi p.1 p.2)

private lemma homogeneousCutoffFrequency_memLp_two_prod_Icc
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    MemLp (fun p : ℝ × ℝ => homogeneousCutoffFrequency chi phi p.1 p.2) 2
      ((volume.restrict (Icc a b)).prod volume) := by
  have hmeasure :
      ((volume : Measure ℝ).restrict (Icc a b)).prod (volume : Measure ℝ) ≤
        (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hhalf := (cutoffHalfFrequency_memLp_two_prod chi phi).mono_measure
    hmeasure
  have hcomm := cutoffCommutatorFrequency_memLp_two_prod_Icc chi phi a b
  have hsum := hhalf.add hcomm
  have heq : (fun p : ℝ × ℝ => homogeneousCutoffFrequency chi phi p.1 p.2) =
      (fun p => cutoffHalfFrequency chi phi p.1 p.2) +
        fun p => cutoffCommutatorFrequency chi phi p.1 p.2 := by
    funext p
    exact homogeneousCutoffFrequency_eq chi phi p.1 p.2
  rw [heq]
  exact hsum

private def freeMajorant (chi phi : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  (fun y => ((‖(FourierTransform.fourier chi) y‖ : ℝ) : ℂ)) ⋆[complexMulCLM]
    fun y => ((‖(FourierTransform.fourier phi) y‖ : ℝ) : ℂ)

private lemma freeMajorant_memLp_two (chi phi : SchwartzMap ℝ ℂ) :
    MemLp (freeMajorant chi phi) 2 volume := by
  apply convolution_mul_memLp_two
  · exact (Complex.continuous_ofReal.comp
      (FourierTransform.fourier chi).continuous.norm).measurable
  · exact (Complex.continuous_ofReal.comp
      (FourierTransform.fourier phi).continuous.norm).measurable
  · exact Complex.ofRealCLM.integrable_comp
      (FourierTransform.fourier chi).integrable.norm
  · convert (FourierTransform.fourier phi).memLp 2 volume |>.norm.ofReal using 1
    funext x
    rfl

private lemma norm_cutoffFreeFrequency_le (chi phi : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    ‖cutoffFreeFrequency chi phi t xi‖ ≤ ‖freeMajorant chi phi xi‖ := by
  let r : ℝ → ℝ := fun y =>
    ‖(FourierTransform.fourier chi) y‖ *
      ‖(FourierTransform.fourier phi) (xi - y)‖
  have hr : Integrable r := by
    have htrans : MemLp (fun y : ℝ =>
        ‖(FourierTransform.fourier phi) (xi - y)‖) 2 volume := by
      simpa [Function.comp_def] using
        ((FourierTransform.fourier phi).memLp 2 volume).norm.comp_measurePreserving
          ((volume : Measure ℝ).measurePreserving_sub_left xi)
    exact memLp_one_iff_integrable.mp
      (htrans.mul' ((FourierTransform.fourier chi).memLp 2 volume).norm)
  have hmajorant : freeMajorant chi phi xi = ((∫ y, r y : ℝ) : ℂ) := by
    unfold freeMajorant convolution
    simpa [r, complexMulCLM] using Complex.ofRealCLM.integral_comp_comm hr
  calc
    ‖cutoffFreeFrequency chi phi t xi‖ ≤
        ∫ y, ‖(FourierTransform.fourier chi) y *
          freeFrequencySchwartz phi t (xi - y)‖ := by
      unfold cutoffFreeFrequency
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, r y := by
      apply integral_mono_ae
      · have htrans : MemLp (fun y : ℝ =>
            freeFrequencySchwartz phi t (xi - y)) 2 volume := by
          simpa [Function.comp_def] using
            (freeFrequencySchwartz_memLp_two phi t).comp_measurePreserving
              ((volume : Measure ℝ).measurePreserving_sub_left xi)
        exact (memLp_one_iff_integrable.mp
          (htrans.mul' ((FourierTransform.fourier chi).memLp 2 volume))).norm
      · exact hr
      · filter_upwards with y
        unfold freeFrequencySchwartz r
        rw [norm_mul, norm_mul, norm_schrodingerSymbol, one_mul]
    _ = ‖freeMajorant chi phi xi‖ := by
      rw [hmajorant, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)

private lemma cutoffFreeFrequency_joint_aestronglyMeasurable
    (chi phi : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      cutoffFreeFrequency chi phi p.1 p.2) (volume.prod volume) := by
  have hjoint : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (FourierTransform.fourier chi) p.2 *
        freeFrequencySchwartz phi p.1.1 (p.1.2 - p.2))
      ((volume.prod volume).prod volume) := by
    apply Continuous.aestronglyMeasurable
    unfold freeFrequencySchwartz schrodingerSymbol
    fun_prop
  simpa [cutoffFreeFrequency, convolution, complexMulCLM] using
    hjoint.integral_prod_right'

private lemma cutoffFreeFrequency_memLp_two_prod_Icc
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    MemLp (fun p : ℝ × ℝ => cutoffFreeFrequency chi phi p.1 p.2) 2
      ((volume.restrict (Icc a b)).prod volume) := by
  have hmeasure :
      ((volume : Measure ℝ).restrict (Icc a b)).prod (volume : Measure ℝ) ≤
        (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hmeas := (cutoffFreeFrequency_joint_aestronglyMeasurable chi phi).mono_measure
    hmeasure
  have hmajorant : MemLp (fun p : ℝ × ℝ => freeMajorant chi phi p.2) 2
      ((volume.restrict (Icc a b)).prod volume) :=
    (freeMajorant_memLp_two chi phi).comp_snd (volume.restrict (Icc a b))
  exact hmajorant.mono hmeas (Filter.Eventually.of_forall fun p =>
    norm_cutoffFreeFrequency_le chi phi p.1 p.2)

private def weightedCutoffFrequency (chi phi : SchwartzMap ℝ ℂ)
    (p : ℝ × ℝ) : ℂ :=
  positiveHalfWeight p.2 * cutoffFreeFrequency chi phi p.1 p.2

private lemma norm_positiveHalfWeight_le (xi : ℝ) :
    ‖positiveHalfWeight xi‖ ≤ 1 + |xi| ^ (1 / 2 : ℝ) := by
  have hnorm : ‖positiveHalfWeight xi‖ =
      (1 + xi ^ 2) ^ ((1 : ℝ) / 4) := by
    rw [positiveHalfWeight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hsq : ‖positiveHalfWeight xi‖ ^ 2 = Real.sqrt (1 + xi ^ 2) := by
    rw [hnorm, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : 0 ≤ 1 + xi ^ 2), Real.sqrt_eq_rpow]
    norm_num
  have hsqrt : Real.sqrt (1 + xi ^ 2) ≤ 1 + |xi| := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg xi, abs_nonneg xi, sq_abs xi]
  have hr0 : 0 ≤ |xi| ^ (1 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg xi) _
  have hrsq : (|xi| ^ (1 / 2 : ℝ)) ^ 2 = |xi| := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg xi)]
    norm_num
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hsq]
  nlinarith [hrsq]

private lemma weightedCutoffFrequency_memLp_two_prod_Icc
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    MemLp (weightedCutoffFrequency chi phi) 2
      ((volume.restrict (Icc a b)).prod volume) := by
  have hfree := cutoffFreeFrequency_memLp_two_prod_Icc chi phi a b
  have hhom := homogeneousCutoffFrequency_memLp_two_prod_Icc chi phi a b
  have hmajorant := hfree.norm.add hhom.norm
  have hmeas : AEStronglyMeasurable (weightedCutoffFrequency chi phi)
      ((volume.restrict (Icc a b)).prod volume) := by
    have hglobal := continuous_positiveHalfWeight.aestronglyMeasurable.comp_snd.mul
      (cutoffFreeFrequency_joint_aestronglyMeasurable chi phi)
    exact hglobal.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  refine hmajorant.mono hmeas (Filter.Eventually.of_forall fun p => ?_)
  unfold weightedCutoffFrequency
  rw [norm_mul]
  calc
    ‖positiveHalfWeight p.2‖ * ‖cutoffFreeFrequency chi phi p.1 p.2‖ ≤
        (1 + |p.2| ^ (1 / 2 : ℝ)) *
          ‖cutoffFreeFrequency chi phi p.1 p.2‖ := by
      gcongr
      exact norm_positiveHalfWeight_le p.2
    _ = ‖cutoffFreeFrequency chi phi p.1 p.2‖ +
        ‖homogeneousCutoffFrequency chi phi p.1 p.2‖ := by
      unfold homogeneousCutoffFrequency
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg p.2) _)]
      ring
    _ = ‖‖cutoffFreeFrequency chi phi p.1 p.2‖ +
        ‖homogeneousCutoffFrequency chi phi p.1 p.2‖‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity

private def halfInputMajorant (phi : SchwartzMap ℝ ℂ) (xi : ℝ) : ℂ :=
  (((|xi| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
    ((‖(FourierTransform.fourier phi) xi‖ : ℝ) : ℂ)

private lemma halfInputMajorant_memLp_two (phi : SchwartzMap ℝ ℂ) :
    MemLp (halfInputMajorant phi) 2 volume := by
  refine (halfFreeFrequency_memLp_two phi 0).congr_norm ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold halfInputMajorant
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs)).mul
        (Complex.continuous_ofReal.comp
          (FourierTransform.fourier phi).continuous.norm)
  · filter_upwards with xi
    unfold halfInputMajorant halfFreeFrequency
    simp [norm_mul, norm_schrodingerSymbol, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg xi) _),
      abs_of_nonneg (norm_nonneg _)]

private def halfMajorant (chi phi : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  (fun y => ((‖(FourierTransform.fourier chi) y‖ : ℝ) : ℂ)) ⋆[complexMulCLM]
    halfInputMajorant phi

private lemma halfMajorant_memLp_two (chi phi : SchwartzMap ℝ ℂ) :
    MemLp (halfMajorant chi phi) 2 volume := by
  apply convolution_mul_memLp_two
  · exact (Complex.continuous_ofReal.comp
      (FourierTransform.fourier chi).continuous.norm).measurable
  · apply Continuous.measurable
    unfold halfInputMajorant
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs)).mul
        (Complex.continuous_ofReal.comp
          (FourierTransform.fourier phi).continuous.norm)
  · exact Complex.ofRealCLM.integrable_comp
      (FourierTransform.fourier chi).integrable.norm
  · exact halfInputMajorant_memLp_two phi

private lemma norm_cutoffHalfFrequency_le (chi phi : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    ‖cutoffHalfFrequency chi phi t xi‖ ≤ ‖halfMajorant chi phi xi‖ := by
  let r : ℝ → ℝ := fun y =>
    ‖(FourierTransform.fourier chi) y‖ *
      (|xi - y| ^ (1 / 2 : ℝ) *
        ‖(FourierTransform.fourier phi) (xi - y)‖)
  have hr : Integrable r := by
    have hinput : MemLp (fun y : ℝ =>
        |xi - y| ^ (1 / 2 : ℝ) *
          ‖(FourierTransform.fourier phi) (xi - y)‖) 2 volume := by
      have h := (halfInputMajorant_memLp_two phi).norm.comp_measurePreserving
        ((volume : Measure ℝ).measurePreserving_sub_left xi)
      refine h.congr_norm ?_ (Filter.Eventually.of_forall fun y => ?_)
      · apply Continuous.aestronglyMeasurable
        exact (((Real.continuous_rpow_const (by norm_num)).comp
          (continuous_abs.comp (continuous_const.sub continuous_id))).mul
            ((FourierTransform.fourier phi).continuous.norm.comp
              (continuous_const.sub continuous_id)))
      · unfold halfInputMajorant
        simp only [Function.comp_apply, Real.norm_eq_abs, norm_mul,
          Complex.norm_real]
        simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (xi - y)) _),
          abs_of_nonneg (norm_nonneg _)]
    exact memLp_one_iff_integrable.mp
      (hinput.mul' ((FourierTransform.fourier chi).memLp 2 volume).norm)
  have hmajorant : halfMajorant chi phi xi = ((∫ y, r y : ℝ) : ℂ) := by
    unfold halfMajorant convolution
    simpa [r, halfInputMajorant, complexMulCLM, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (norm_nonneg _)] using Complex.ofRealCLM.integral_comp_comm hr
  calc
    ‖cutoffHalfFrequency chi phi t xi‖ ≤
        ∫ y, ‖(FourierTransform.fourier chi) y *
          halfFreeFrequency phi t (xi - y)‖ := by
      unfold cutoffHalfFrequency
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, r y := by
      apply integral_mono_ae
      · exact (main_integrand_integrable chi phi t xi).norm
      · exact hr
      · filter_upwards with y
        unfold halfFreeFrequency r
        simp [norm_mul, norm_schrodingerSymbol, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (xi - y)) _)]
    _ = ‖halfMajorant chi phi xi‖ := by
      rw [hmajorant, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact integral_nonneg fun y => mul_nonneg (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _))

private def weightedMajorant (chi phi : SchwartzMap ℝ ℂ) (xi : ℝ) : ℝ :=
  ‖freeMajorant chi phi xi‖ + ‖halfMajorant chi phi xi‖ +
    ‖commutatorMajorant chi phi xi‖

private lemma weightedMajorant_memLp_two (chi phi : SchwartzMap ℝ ℂ) :
    MemLp (weightedMajorant chi phi) 2 volume := by
  exact ((freeMajorant_memLp_two chi phi).norm.add
    (halfMajorant_memLp_two chi phi).norm).add
      (commutatorMajorant_memLp_two chi phi).norm

private lemma norm_weightedCutoffFrequency_le
    (chi phi : SchwartzMap ℝ ℂ) (t xi : ℝ) :
    ‖weightedCutoffFrequency chi phi (t, xi)‖ ≤
      weightedMajorant chi phi xi := by
  have hhom :
      ‖homogeneousCutoffFrequency chi phi t xi‖ ≤
        ‖cutoffHalfFrequency chi phi t xi‖ +
          ‖cutoffCommutatorFrequency chi phi t xi‖ := by
    rw [homogeneousCutoffFrequency_eq]
    exact norm_add_le _ _
  unfold weightedCutoffFrequency
  rw [norm_mul]
  calc
    ‖positiveHalfWeight xi‖ * ‖cutoffFreeFrequency chi phi t xi‖ ≤
        (1 + |xi| ^ (1 / 2 : ℝ)) *
          ‖cutoffFreeFrequency chi phi t xi‖ := by
      gcongr
      exact norm_positiveHalfWeight_le xi
    _ = ‖cutoffFreeFrequency chi phi t xi‖ +
        ‖homogeneousCutoffFrequency chi phi t xi‖ := by
      unfold homogeneousCutoffFrequency
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg xi) _)]
      ring
    _ ≤ ‖cutoffFreeFrequency chi phi t xi‖ +
        (‖cutoffHalfFrequency chi phi t xi‖ +
          ‖cutoffCommutatorFrequency chi phi t xi‖) := by gcongr
    _ ≤ weightedMajorant chi phi xi := by
      unfold weightedMajorant
      have hfree := norm_cutoffFreeFrequency_le chi phi t xi
      have hhalf := norm_cutoffHalfFrequency_le chi phi t xi
      have hcomm := norm_cutoffCommutatorFrequency_le chi phi t xi
      linarith

private lemma weightedCutoffFrequency_memLp_two
    (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    MemLp (fun xi => weightedCutoffFrequency chi phi (t, xi)) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun xi => weightedCutoffFrequency chi phi (t, xi)) volume :=
    continuous_positiveHalfWeight.aestronglyMeasurable.mul
      (cutoffFreeFrequency_memLp_two chi phi t).1
  exact (weightedMajorant_memLp_two chi phi).mono hmeas
    (Filter.Eventually.of_forall fun xi => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact norm_weightedCutoffFrequency_le chi phi t xi
      · unfold weightedMajorant
        positivity)

private def weightedCutoffL2 (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) : L2 :=
  (weightedCutoffFrequency_memLp_two chi phi t).toLp
    (fun xi => weightedCutoffFrequency chi phi (t, xi))

private lemma coe_weightedCutoffL2 (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    (weightedCutoffL2 chi phi t : ℝ → ℂ) =ᵐ[volume]
      fun xi => weightedCutoffFrequency chi phi (t, xi) :=
  (weightedCutoffFrequency_memLp_two chi phi t).coeFn_toLp

private lemma continuous_cutoffFreeFrequency_point
    (chi phi : SchwartzMap ℝ ℂ) (xi : ℝ) :
    Continuous (fun t => cutoffFreeFrequency chi phi t xi) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let B : ℝ → ℝ := fun y =>
    ‖(FourierTransform.fourier chi) y‖ *
      ‖(FourierTransform.fourier phi) (xi - y)‖
  have hB : Integrable B := by
    have htrans : MemLp (fun y : ℝ =>
        ‖(FourierTransform.fourier phi) (xi - y)‖) 2 volume := by
      simpa [Function.comp_def] using
        ((FourierTransform.fourier phi).memLp 2 volume).norm.comp_measurePreserving
          ((volume : Measure ℝ).measurePreserving_sub_left xi)
    exact memLp_one_iff_integrable.mp
      (htrans.mul' ((FourierTransform.fourier chi).memLp 2 volume).norm)
  change Tendsto (fun t => ∫ y : ℝ,
      (FourierTransform.fourier chi) y *
        freeFrequencySchwartz phi t (xi - y)) (nhds t0)
    (nhds (∫ y : ℝ, (FourierTransform.fourier chi) y *
      freeFrequencySchwartz phi t0 (xi - y)))
  apply tendsto_integral_filter_of_dominated_convergence B
  · filter_upwards with t
    apply Continuous.aestronglyMeasurable
    unfold freeFrequencySchwartz
    exact (FourierTransform.fourier chi).continuous.mul
      (((continuous_schrodingerSymbol t).comp
        (continuous_const.sub continuous_id)).mul
        ((FourierTransform.fourier phi).continuous.comp
          (continuous_const.sub continuous_id)))
  · filter_upwards with t
    filter_upwards with y
    unfold B freeFrequencySchwartz
    rw [norm_mul, norm_mul, norm_schrodingerSymbol, one_mul]
  · exact hB
  · filter_upwards with y
    apply ContinuousAt.mul continuousAt_const
    unfold freeFrequencySchwartz schrodingerSymbol
    fun_prop

private lemma continuous_weightedCutoffFrequency_point
    (chi phi : SchwartzMap ℝ ℂ) (xi : ℝ) :
    Continuous (fun t => weightedCutoffFrequency chi phi (t, xi)) := by
  unfold weightedCutoffFrequency
  change Continuous (fun t => positiveHalfWeight xi *
    cutoffFreeFrequency chi phi t xi)
  exact continuous_const.mul (continuous_cutoffFreeFrequency_point chi phi xi)

private lemma integral_norm_sq_toLp {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ∫ x, ‖f x‖ ^ 2 = ‖hf.toLp f‖ ^ 2 := by
  let g : L2 := hf.toLp f
  have hfg : (g : ℝ → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  calc
    ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖(g : ℝ → ℂ) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]
    _ = ‖g‖ ^ 2 := by
      have h := lpNorm_eq_integral_norm_rpow_toReal
        (f := (g : ℝ → ℂ)) (p := (2 : ENNReal)) (by norm_num) (by norm_num)
          (Lp.aestronglyMeasurable g)
      have hlp : lpNorm (g : ℝ → ℂ) 2 volume = ‖g‖ := by
        rw [lpNorm, if_pos (Lp.aestronglyMeasurable g), Lp.norm_def]
      rw [hlp] at h
      norm_num at h
      rw [← Real.sqrt_eq_rpow] at h
      have hi : 0 ≤ ∫ x, ‖(g : ℝ → ℂ) x‖ ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      rw [h, Real.sq_sqrt hi]
    _ = ‖hf.toLp f‖ ^ 2 := rfl

private lemma continuous_weightedCutoffL2
    (chi phi : SchwartzMap ℝ ℂ) :
    Continuous (weightedCutoffL2 chi phi) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let M : ℝ → ℝ := weightedMajorant chi phi
  let F : ℝ → ℝ → ℝ := fun t xi =>
    ‖weightedCutoffFrequency chi phi (t, xi) -
      weightedCutoffFrequency chi phi (t0, xi)‖ ^ 2
  have hMnonneg (xi : ℝ) : 0 ≤ M xi := by
    unfold M weightedMajorant
    positivity
  have hM2 : Integrable (fun xi => M xi ^ 2) := by
    have h := (memLp_two_iff_integrable_sq_norm
      (weightedMajorant_memLp_two chi phi).1).mp
        (weightedMajorant_memLp_two chi phi)
    exact h.congr (Filter.Eventually.of_forall fun xi => by
      change ‖weightedMajorant chi phi xi‖ ^ 2 = M xi ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (hMnonneg xi)])
  have hboundInt : Integrable (fun xi => 4 * M xi ^ 2) := hM2.const_mul 4
  have hFmeas (t : ℝ) : AEStronglyMeasurable (F t) volume := by
    unfold F
    exact (((weightedCutoffFrequency_memLp_two chi phi t).1.sub
      (weightedCutoffFrequency_memLp_two chi phi t0).1).norm.pow 2)
  have hFbound (t xi : ℝ) : ‖F t xi‖ ≤ 4 * M xi ^ 2 := by
    have ht := norm_weightedCutoffFrequency_le chi phi t xi
    have h0 := norm_weightedCutoffFrequency_le chi phi t0 xi
    have hdiff : ‖weightedCutoffFrequency chi phi (t, xi) -
        weightedCutoffFrequency chi phi (t0, xi)‖ ≤ 2 * M xi := by
      calc
        _ ≤ ‖weightedCutoffFrequency chi phi (t, xi)‖ +
            ‖weightedCutoffFrequency chi phi (t0, xi)‖ := norm_sub_le _ _
        _ ≤ M xi + M xi := add_le_add ht h0
        _ = 2 * M xi := by ring
    unfold F
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖weightedCutoffFrequency chi phi (t, xi) -
          weightedCutoffFrequency chi phi (t0, xi)‖ ^ 2 ≤
          (2 * M xi) ^ 2 := by gcongr
      _ = 4 * M xi ^ 2 := by ring
  have hint : Tendsto (fun t => ∫ xi, F t xi) (nhds t0) (nhds 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (fun xi => 4 * M xi ^ 2)
      (Filter.Eventually.of_forall hFmeas)
      (Filter.Eventually.of_forall fun t =>
        Filter.Eventually.of_forall (hFbound t)) hboundInt
      (Filter.Eventually.of_forall fun xi => by
        show Tendsto (fun t => F t xi) (nhds t0) (nhds 0)
        have hc : ContinuousAt
            (fun t => weightedCutoffFrequency chi phi (t, xi)) t0 :=
          (continuous_weightedCutoffFrequency_point chi phi xi).continuousAt
        have hsub : Tendsto (fun t =>
            weightedCutoffFrequency chi phi (t, xi) -
              weightedCutoffFrequency chi phi (t0, xi))
            (nhds t0) (nhds 0) := by
          have hconst : ContinuousAt (fun _ : ℝ =>
              weightedCutoffFrequency chi phi (t0, xi)) t0 := continuousAt_const
          have hh := hc.sub hconst
          change Tendsto (fun t =>
              weightedCutoffFrequency chi phi (t, xi) -
                weightedCutoffFrequency chi phi (t0, xi))
            (nhds t0) (nhds
              (weightedCutoffFrequency chi phi (t0, xi) -
                weightedCutoffFrequency chi phi (t0, xi))) at hh
          simpa using hh
        simpa [F] using hsub.norm.pow 2)
    simpa using h
  have hnormsq (t : ℝ) :
      ∫ xi, F t xi = ‖weightedCutoffL2 chi phi t -
        weightedCutoffL2 chi phi t0‖ ^ 2 := by
    let d : ℝ → ℂ := fun xi => weightedCutoffFrequency chi phi (t, xi) -
      weightedCutoffFrequency chi phi (t0, xi)
    have hd : MemLp d 2 volume :=
      (weightedCutoffFrequency_memLp_two chi phi t).sub
        (weightedCutoffFrequency_memLp_two chi phi t0)
    have hdLp : hd.toLp d = weightedCutoffL2 chi phi t -
        weightedCutoffL2 chi phi t0 := by
      apply Lp.ext
      filter_upwards [hd.coeFn_toLp, coe_weightedCutoffL2 chi phi t,
        coe_weightedCutoffL2 chi phi t0,
        Lp.coeFn_sub (weightedCutoffL2 chi phi t)
          (weightedCutoffL2 chi phi t0)] with xi hd' ht h0 hout
      rw [hd', hout]
      simp only [Pi.sub_apply]
      rw [ht, h0]
    change ∫ xi, ‖d xi‖ ^ 2 = _
    rw [integral_norm_sq_toLp hd, hdLp]
  rw [show (fun t => ∫ xi, F t xi) = fun t =>
      ‖weightedCutoffL2 chi phi t - weightedCutoffL2 chi phi t0‖ ^ 2 by
    funext t
    exact hnormsq t] at hint
  change Tendsto (weightedCutoffL2 chi phi) (nhds t0)
    (nhds (weightedCutoffL2 chi phi t0))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hint
  convert hsqrt using 1
  · funext t
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  · simp

private def cutoffFreeL2 (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) : L2 :=
  (cutoffFreeFrequency_memLp_two chi phi t).toLp
    (cutoffFreeFrequency chi phi t)

private lemma coe_cutoffFreeL2 (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    (cutoffFreeL2 chi phi t : ℝ → ℂ) =ᵐ[volume]
      cutoffFreeFrequency chi phi t :=
  (cutoffFreeFrequency_memLp_two chi phi t).coeFn_toLp

private def cutoffPhysicalL2 (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) : L2 :=
  fourierL2.symm (cutoffFreeL2 chi phi t)

private lemma coe_cutoffPhysicalL2 (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    (cutoffPhysicalL2 chi phi t : ℝ → ℂ) =ᵐ[volume]
      fun x => chi x * (freeProp t (phi.toLp 2 volume) : ℝ → ℂ) x := by
  have hbridge := l1_l2_fourierInv_bridge
    (by simpa using
      (memLp_one_iff_integrable.mpr (cutoffFreeFrequency_integrable chi phi t)))
    (cutoffFreeFrequency_memLp_two chi phi t)
  have hfree := freeProp_schwartz_ae_inverseIntegral phi t
  filter_upwards [hbridge, hfree] with x hcut hfree'
  change (cutoffPhysicalL2 chi phi t : ℝ → ℂ) x = _
  rw [show (cutoffPhysicalL2 chi phi t : ℝ → ℂ) x =
      inverseIntegral (cutoffFreeFrequency chi phi t) x by
    exact hcut]
  rw [inverseIntegral_cutoffFreeFrequency, hfree']

private def localizedFreeSchwartzHs
    (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) : Hs (1 / 2 : ℝ) :=
  HsHalfOfWeightedFourier (weightedCutoffL2 chi phi t)

private lemma continuous_localizedFreeSchwartzHs
    (chi phi : SchwartzMap ℝ ℂ) :
    Continuous (localizedFreeSchwartzHs chi phi) := by
  unfold localizedFreeSchwartzHs HsHalfOfWeightedFourier
  exact sobolevFourier.symm.continuous.comp
    (continuous_weightedCutoffL2 chi phi)

private lemma localizedFreeSchwartzHs_toL2
    (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    Hs.toL2 (by norm_num) (localizedFreeSchwartzHs chi phi t) =
      cutoffPhysicalL2 chi phi t := by
  apply Hs_toL2_HsHalfOfWeightedFourier_eq
  filter_upwards [coe_weightedCutoffL2 chi phi t,
    coe_cutoffFreeL2 chi phi t] with xi hweighted hfree
  rw [hweighted]
  unfold weightedCutoffFrequency
  rw [show (sobolevFourier (cutoffPhysicalL2 chi phi t) : ℝ → ℂ) xi =
      (cutoffFreeL2 chi phi t : ℝ → ℂ) xi by
    have heq : sobolevFourier (cutoffPhysicalL2 chi phi t) =
        cutoffFreeL2 chi phi t := by
      unfold cutoffPhysicalL2 sobolevFourier fourierL2
      exact LinearIsometryEquiv.apply_symm_apply _ _
    exact congrArg (fun q : L2 => (q : ℝ → ℂ) xi) heq]
  rw [hfree]

private lemma localizedFreeSchwartzHs_represents
    (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    (Hs.toL2 (by norm_num) (localizedFreeSchwartzHs chi phi t) : ℝ → ℂ) =ᵐ[volume]
      fun x => chi x * (freeProp t (phi.toLp 2 volume) : ℝ → ℂ) x := by
  rw [localizedFreeSchwartzHs_toL2]
  exact coe_cutoffPhysicalL2 chi phi t

private lemma localizedFreeSchwartzHs_memLp_two_Icc
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    MemLp (localizedFreeSchwartzHs chi phi) 2
      (volume.restrict (Icc a b)) := by
  let mu : Measure ℝ := volume.restrict (Icc a b)
  have hprod := weightedCutoffFrequency_memLp_two_prod_Icc chi phi a b
  have hmeas : AEStronglyMeasurable (localizedFreeSchwartzHs chi phi) mu :=
    (continuous_localizedFreeSchwartzHs chi phi).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  norm_num only [ENNReal.toReal_ofNat]
  apply ne_of_lt
  calc
    (∫⁻ t : ℝ, ‖localizedFreeSchwartzHs chi phi t‖ₑ ^ (2 : ℝ) ∂mu) =
        ∫⁻ t : ℝ, ∫⁻ xi : ℝ,
          ‖weightedCutoffFrequency chi phi (t, xi)‖ₑ ^ (2 : ℝ) ∂volume ∂mu := by
      apply lintegral_congr
      intro t
      rw [show ‖localizedFreeSchwartzHs chi phi t‖ₑ =
          ‖weightedCutoffL2 chi phi t‖ₑ by
        unfold localizedFreeSchwartzHs HsHalfOfWeightedFourier
        rw [LinearIsometryEquiv.enorm_map]]
      convert (lintegral_enorm_sq_toLp
        (weightedCutoffFrequency_memLp_two chi phi t)).symm using 1 <;>
          norm_num [weightedCutoffL2]
    _ = ∫⁻ p : ℝ × ℝ,
        ‖weightedCutoffFrequency chi phi p‖ₑ ^ (2 : ℝ)
          ∂(mu.prod volume) := by
      have hm : AEMeasurable (Function.uncurry (fun t xi =>
          ‖weightedCutoffFrequency chi phi (t, xi)‖ₑ ^ (2 : ℝ)))
          (mu.prod volume) := by
        change AEMeasurable (fun p =>
          ‖weightedCutoffFrequency chi phi p‖ₑ ^ (2 : ℝ))
          (mu.prod volume)
        simpa [mu] using hprod.1.enorm.pow_const (2 : ℝ)
      exact lintegral_lintegral hm
    _ < ⊤ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hprod.2

private lemma freeFrequencySchwartz_add (phi psi : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    freeFrequencySchwartz (phi + psi) t xi =
      freeFrequencySchwartz phi t xi + freeFrequencySchwartz psi t xi := by
  unfold freeFrequencySchwartz
  rw [FourierAdd.fourier_add]
  rw [SchwartzMap.add_apply]
  ring

private lemma freeFrequencySchwartz_smul (c : ℂ) (phi : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    freeFrequencySchwartz (c • phi) t xi =
      c * freeFrequencySchwartz phi t xi := by
  unfold freeFrequencySchwartz
  rw [FourierSMul.fourier_smul]
  rw [SchwartzMap.smul_apply]
  simp only [smul_eq_mul]
  ring

private lemma cutoffFreeFrequency_add (chi phi psi : SchwartzMap ℝ ℂ)
    (t xi : ℝ) :
    cutoffFreeFrequency chi (phi + psi) t xi =
      cutoffFreeFrequency chi phi t xi + cutoffFreeFrequency chi psi t xi := by
  unfold cutoffFreeFrequency convolution complexMulCLM
  change (∫ y : ℝ, (FourierTransform.fourier chi) y *
      freeFrequencySchwartz (phi + psi) t (xi - y)) =
    (∫ y : ℝ, (FourierTransform.fourier chi) y *
      freeFrequencySchwartz phi t (xi - y)) +
    ∫ y : ℝ, (FourierTransform.fourier chi) y *
      freeFrequencySchwartz psi t (xi - y)
  rw [show (fun y : ℝ => (FourierTransform.fourier chi) y *
      freeFrequencySchwartz (phi + psi) t (xi - y)) =
      (fun y => (FourierTransform.fourier chi) y *
        freeFrequencySchwartz phi t (xi - y)) +
      (fun y => (FourierTransform.fourier chi) y *
        freeFrequencySchwartz psi t (xi - y)) by
    funext y
    rw [freeFrequencySchwartz_add]
    simp only [Pi.add_apply]
    ring]
  have hint (q : SchwartzMap ℝ ℂ) : Integrable (fun y : ℝ =>
      (FourierTransform.fourier chi) y *
        freeFrequencySchwartz q t (xi - y)) := by
    have htrans : MemLp (fun y : ℝ =>
        freeFrequencySchwartz q t (xi - y)) 2 volume := by
      simpa [Function.comp_def] using
        (freeFrequencySchwartz_memLp_two q t).comp_measurePreserving
          ((volume : Measure ℝ).measurePreserving_sub_left xi)
    exact memLp_one_iff_integrable.mp
      (htrans.mul' ((FourierTransform.fourier chi).memLp 2 volume))
  exact integral_add (hint phi) (hint psi)

private lemma cutoffFreeFrequency_smul (chi phi : SchwartzMap ℝ ℂ)
    (c : ℂ) (t xi : ℝ) :
    cutoffFreeFrequency chi (c • phi) t xi =
      c * cutoffFreeFrequency chi phi t xi := by
  unfold cutoffFreeFrequency convolution complexMulCLM
  change (∫ y : ℝ, (FourierTransform.fourier chi) y *
      freeFrequencySchwartz (c • phi) t (xi - y)) =
    c * ∫ y : ℝ, (FourierTransform.fourier chi) y *
      freeFrequencySchwartz phi t (xi - y)
  rw [show (fun y : ℝ => (FourierTransform.fourier chi) y *
      freeFrequencySchwartz (c • phi) t (xi - y)) =
      fun y => c * ((FourierTransform.fourier chi) y *
        freeFrequencySchwartz phi t (xi - y)) by
    funext y
    rw [freeFrequencySchwartz_smul]
    ring,
    integral_const_mul]

private lemma weightedCutoffFrequency_add (chi phi psi : SchwartzMap ℝ ℂ)
    (p : ℝ × ℝ) :
    weightedCutoffFrequency chi (phi + psi) p =
      weightedCutoffFrequency chi phi p +
        weightedCutoffFrequency chi psi p := by
  unfold weightedCutoffFrequency
  rw [cutoffFreeFrequency_add]
  ring

private lemma weightedCutoffFrequency_smul (chi phi : SchwartzMap ℝ ℂ)
    (c : ℂ) (p : ℝ × ℝ) :
    weightedCutoffFrequency chi (c • phi) p =
      c * weightedCutoffFrequency chi phi p := by
  unfold weightedCutoffFrequency
  rw [cutoffFreeFrequency_smul]
  ring

private lemma weightedCutoffL2_add (chi phi psi : SchwartzMap ℝ ℂ) (t : ℝ) :
    weightedCutoffL2 chi (phi + psi) t =
      weightedCutoffL2 chi phi t + weightedCutoffL2 chi psi t := by
  apply Lp.ext
  filter_upwards [coe_weightedCutoffL2 chi (phi + psi) t,
    coe_weightedCutoffL2 chi phi t, coe_weightedCutoffL2 chi psi t,
    Lp.coeFn_add (weightedCutoffL2 chi phi t)
      (weightedCutoffL2 chi psi t)] with xi hsum hphi hpsi hout
  rw [hsum, hout]
  simp only [Pi.add_apply]
  rw [hphi, hpsi, weightedCutoffFrequency_add]

private lemma weightedCutoffL2_smul (chi phi : SchwartzMap ℝ ℂ)
    (c : ℂ) (t : ℝ) :
    weightedCutoffL2 chi (c • phi) t = c • weightedCutoffL2 chi phi t := by
  apply Lp.ext
  filter_upwards [coe_weightedCutoffL2 chi (c • phi) t,
    coe_weightedCutoffL2 chi phi t,
    Lp.coeFn_smul c (weightedCutoffL2 chi phi t)] with xi hleft hphi hout
  rw [hleft, hout]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hphi, weightedCutoffFrequency_smul]

private lemma localizedFreeSchwartzHs_add
    (chi phi psi : SchwartzMap ℝ ℂ) (t : ℝ) :
    localizedFreeSchwartzHs chi (phi + psi) t =
      localizedFreeSchwartzHs chi phi t + localizedFreeSchwartzHs chi psi t := by
  unfold localizedFreeSchwartzHs HsHalfOfWeightedFourier
  rw [weightedCutoffL2_add, map_add]

private lemma localizedFreeSchwartzHs_smul
    (chi phi : SchwartzMap ℝ ℂ) (c : ℂ) (t : ℝ) :
    localizedFreeSchwartzHs chi (c • phi) t =
      c • localizedFreeSchwartzHs chi phi t := by
  unfold localizedFreeSchwartzHs HsHalfOfWeightedFourier
  rw [weightedCutoffL2_smul, map_smul]

private def localizedFreeSchwartzCurveLp (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (phi : SchwartzMap ℝ ℂ) :
    Lp (Hs (1 / 2 : ℝ)) 2 (volume.restrict (Icc a b)) :=
  (localizedFreeSchwartzHs_memLp_two_Icc chi phi a b).toLp
    (localizedFreeSchwartzHs chi phi)

private lemma localizedFreeSchwartzCurveLp_add
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (phi psi : SchwartzMap ℝ ℂ) :
    localizedFreeSchwartzCurveLp chi a b (phi + psi) =
      localizedFreeSchwartzCurveLp chi a b phi +
        localizedFreeSchwartzCurveLp chi a b psi := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (localizedFreeSchwartzHs_memLp_two_Icc chi (phi + psi) a b),
    MemLp.coeFn_toLp (localizedFreeSchwartzHs_memLp_two_Icc chi phi a b),
    MemLp.coeFn_toLp (localizedFreeSchwartzHs_memLp_two_Icc chi psi a b),
    Lp.coeFn_add (localizedFreeSchwartzCurveLp chi a b phi)
      (localizedFreeSchwartzCurveLp chi a b psi)] with t hsum hphi hpsi hout
  rw [show (localizedFreeSchwartzCurveLp chi a b (phi + psi) : ℝ →
      Hs (1 / 2 : ℝ)) t = localizedFreeSchwartzHs chi (phi + psi) t by
        exact hsum,
    show ((localizedFreeSchwartzCurveLp chi a b phi +
      localizedFreeSchwartzCurveLp chi a b psi :
        Lp (Hs (1 / 2 : ℝ)) 2 (volume.restrict (Icc a b))) :
          ℝ → Hs (1 / 2 : ℝ)) t =
      (localizedFreeSchwartzCurveLp chi a b phi : ℝ → Hs (1 / 2 : ℝ)) t +
      (localizedFreeSchwartzCurveLp chi a b psi : ℝ → Hs (1 / 2 : ℝ)) t by
        exact hout]
  rw [show (localizedFreeSchwartzCurveLp chi a b phi : ℝ →
      Hs (1 / 2 : ℝ)) t = localizedFreeSchwartzHs chi phi t by exact hphi,
    show (localizedFreeSchwartzCurveLp chi a b psi : ℝ →
      Hs (1 / 2 : ℝ)) t = localizedFreeSchwartzHs chi psi t by exact hpsi,
    localizedFreeSchwartzHs_add]

private lemma localizedFreeSchwartzCurveLp_smul
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (c : ℂ) (phi : SchwartzMap ℝ ℂ) :
    localizedFreeSchwartzCurveLp chi a b (c • phi) =
      c • localizedFreeSchwartzCurveLp chi a b phi := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (localizedFreeSchwartzHs_memLp_two_Icc chi (c • phi) a b),
    MemLp.coeFn_toLp (localizedFreeSchwartzHs_memLp_two_Icc chi phi a b),
    Lp.coeFn_smul c (localizedFreeSchwartzCurveLp chi a b phi)]
      with t hleft hphi hout
  rw [show (localizedFreeSchwartzCurveLp chi a b (c • phi) : ℝ →
      Hs (1 / 2 : ℝ)) t = localizedFreeSchwartzHs chi (c • phi) t by
        exact hleft,
    show ((c • localizedFreeSchwartzCurveLp chi a b phi :
      Lp (Hs (1 / 2 : ℝ)) 2 (volume.restrict (Icc a b))) :
        ℝ → Hs (1 / 2 : ℝ)) t =
      c • (localizedFreeSchwartzCurveLp chi a b phi :
        ℝ → Hs (1 / 2 : ℝ)) t by exact hout,
    show (localizedFreeSchwartzCurveLp chi a b phi : ℝ →
      Hs (1 / 2 : ℝ)) t = localizedFreeSchwartzHs chi phi t by exact hphi,
    localizedFreeSchwartzHs_smul]

private def localizedFreeSchwartzCurveLinear (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) : SchwartzMap ℝ ℂ →ₗ[ℂ]
      Lp (Hs (1 / 2 : ℝ)) 2 (volume.restrict (Icc a b)) where
  toFun := localizedFreeSchwartzCurveLp chi a b
  map_add' := localizedFreeSchwartzCurveLp_add chi a b
  map_smul' := localizedFreeSchwartzCurveLp_smul chi a b

private lemma eLpNorm_comp_snd_prod_Icc (M : ℝ → ℂ)
    (hM : AEStronglyMeasurable M volume) (a b : ℝ) :
    eLpNorm (fun p : ℝ × ℝ => M p.2) 2
        ((volume.restrict (Icc a b)).prod volume) =
      ((volume.restrict (Icc a b)) Set.univ) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm M 2 volume := by
  let mu : Measure ℝ := volume.restrict (Icc a b)
  have hMmap : AEStronglyMeasurable M
      (Measure.map Prod.snd (mu.prod volume)) := by
    rw [Measure.map_snd_prod]
    exact hM.smul_measure (mu Set.univ : ℝ≥0∞)
  calc
    eLpNorm (fun p : ℝ × ℝ => M p.2) 2 (mu.prod volume) =
        eLpNorm M 2 (Measure.map Prod.snd (mu.prod volume)) := by
      symm
      exact eLpNorm_map_measure hMmap measurable_snd.aemeasurable
    _ = eLpNorm M 2 ((mu Set.univ) • volume) := by
      rw [Measure.map_snd_prod]
    _ = (mu Set.univ) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm M 2 volume := by
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
      rfl

private lemma norm_toLp_prod_Icc_le_snd_majorant
    (f : ℝ × ℝ → ℂ) (hf : MemLp f 2
      ((volume.restrict (Icc a b)).prod volume))
    (M : ℝ → ℂ) (hM : MemLp M 2 volume)
    (hbound : ∀ p, ‖f p‖ ≤ ‖M p.2‖) :
    ‖hf.toLp f‖ ≤
      (((volume.restrict (Icc a b)) Set.univ) ^
        (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖hM.toLp M‖ := by
  have he : eLpNorm f 2 ((volume.restrict (Icc a b)).prod volume) ≤
      eLpNorm (fun p : ℝ × ℝ => M p.2) 2
        ((volume.restrict (Icc a b)).prod volume) := by
    apply eLpNorm_mono_enorm_ae
    filter_upwards with p
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hbound p)
  rw [eLpNorm_comp_snd_prod_Icc M hM.1 a b] at he
  have htop : ((volume.restrict (Icc a b)) Set.univ) ^
      (1 / (2 : ℝ≥0∞)).toReal * eLpNorm M 2 volume ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · positivity
      · rw [Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top
    · exact hM.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop he
  rw [ENNReal.toReal_mul,
    toReal_eLpNorm hf.1, toReal_eLpNorm hM.1] at hr
  rw [Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm hf.1, toReal_eLpNorm hM.1]
  exact hr

private lemma norm_fourierNormReal_toLp (phi : SchwartzMap ℝ ℂ) :
    ‖(fourierNormReal_memLp_two phi).toLp (fourierNormReal phi)‖ =
      ‖phi.toLp 2 volume‖ := by
  have hnorm : eLpNorm (fourierNormReal phi) 2 volume =
      eLpNorm (FourierTransform.fourier phi : ℝ → ℂ) 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with xi
    unfold fourierNormReal
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [Lp.norm_toLp, hnorm]
  calc
    (eLpNorm (FourierTransform.fourier phi : ℝ → ℂ) 2 volume).toReal =
        ‖(FourierTransform.fourier phi).toLp 2 volume‖ := by
      symm
      exact Lp.norm_toLp _ _
    _ = ‖fourierL2 (phi.toLp 2 volume)‖ := by
      exact congrArg norm (SchwartzMap.toLp_fourier_eq phi).symm
    _ = ‖phi.toLp 2 volume‖ := LinearIsometryEquiv.norm_map _ _

private lemma norm_fourierNormComplex_toLp (phi : SchwartzMap ℝ ℂ) :
    ‖((fourierNormReal_memLp_two phi).ofReal.toLp
      (fun y => ((fourierNormReal phi y : ℝ) : ℂ)))‖ =
      ‖phi.toLp 2 volume‖ := by
  rw [Lp.norm_toLp]
  have hnorm : eLpNorm (fun y => ((fourierNormReal phi y : ℝ) : ℂ)) 2 volume =
      eLpNorm (fourierNormReal phi) 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with xi
    unfold fourierNormReal
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  rw [hnorm]
  rw [← Lp.norm_toLp (fourierNormReal phi)
      (fourierNormReal_memLp_two phi)]
  exact norm_fourierNormReal_toLp phi

private def freeKernelAbs (chi : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ :=
  ((‖(FourierTransform.fourier chi) y‖ : ℝ) : ℂ)

private lemma freeKernelAbs_integrable (chi : SchwartzMap ℝ ℂ) :
    Integrable (freeKernelAbs chi) := by
  exact Complex.ofRealCLM.integrable_comp
    (FourierTransform.fourier chi).integrable.norm

private lemma norm_freeMajorant_toLp_le (chi phi : SchwartzMap ℝ ℂ) :
    ‖(freeMajorant_memLp_two chi phi).toLp (freeMajorant chi phi)‖ ≤
      ‖(memLp_one_iff_integrable.mpr (freeKernelAbs_integrable chi)).toLp
        (freeKernelAbs chi)‖ * ‖phi.toLp 2 volume‖ := by
  have hyoung := norm_convolution_mul_toLp_le
    (freeKernelAbs chi) (fun y => ((fourierNormReal phi y : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp
      (FourierTransform.fourier chi).continuous.norm).measurable
    (Complex.continuous_ofReal.comp (by
      unfold fourierNormReal
      fun_prop)).measurable
    (freeKernelAbs_integrable chi) (fourierNormReal_memLp_two phi).ofReal
  have hleft : (convolution_mul_memLp_two
      (freeKernelAbs chi) (fun y => ((fourierNormReal phi y : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp
        (FourierTransform.fourier chi).continuous.norm).measurable
      (Complex.continuous_ofReal.comp (by
        unfold fourierNormReal
        fun_prop)).measurable
      (freeKernelAbs_integrable chi) (fourierNormReal_memLp_two phi).ofReal).toLp
        ((freeKernelAbs chi) ⋆[complexMulCLM]
          fun y => ((fourierNormReal phi y : ℝ) : ℂ)) =
      (freeMajorant_memLp_two chi phi).toLp (freeMajorant chi phi) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (convolution_mul_memLp_two
        (freeKernelAbs chi) (fun y => ((fourierNormReal phi y : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp
          (FourierTransform.fourier chi).continuous.norm).measurable
        (Complex.continuous_ofReal.comp (by
          unfold fourierNormReal
          fun_prop)).measurable
        (freeKernelAbs_integrable chi) (fourierNormReal_memLp_two phi).ofReal),
      MemLp.coeFn_toLp (freeMajorant_memLp_two chi phi)] with xi h1 h2
    rw [h1, h2]
    rfl
  rw [hleft] at hyoung
  rw [norm_fourierNormComplex_toLp phi] at hyoung
  simpa [freeKernelAbs, freeMajorant, fourierNormReal] using hyoung

private def commutatorKernelComplex (chi : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ :=
  ((commutatorKernelReal chi y : ℝ) : ℂ)

private lemma commutatorKernelComplex_integrable (chi : SchwartzMap ℝ ℂ) :
    Integrable (commutatorKernelComplex chi) :=
  Complex.ofRealCLM.integrable_comp (commutatorKernelReal_integrable chi)

private lemma norm_commutatorMajorant_toLp_le
    (chi phi : SchwartzMap ℝ ℂ) :
    ‖(commutatorMajorant_memLp_two chi phi).toLp
        (commutatorMajorant chi phi)‖ ≤
      ‖(memLp_one_iff_integrable.mpr
        (commutatorKernelComplex_integrable chi)).toLp
          (commutatorKernelComplex chi)‖ * ‖phi.toLp 2 volume‖ := by
  have hyoung := norm_convolution_mul_toLp_le
    (commutatorKernelComplex chi)
    (fun y => ((fourierNormReal phi y : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (by
      unfold commutatorKernelReal
      exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs).mul
        (FourierTransform.fourier chi).continuous.norm)).measurable
    (Complex.continuous_ofReal.comp (by
      unfold fourierNormReal
      fun_prop)).measurable
    (commutatorKernelComplex_integrable chi)
    (fourierNormReal_memLp_two phi).ofReal
  have hleft : (convolution_mul_memLp_two
      (commutatorKernelComplex chi)
      (fun y => ((fourierNormReal phi y : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (by
        unfold commutatorKernelReal
        exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs).mul
          (FourierTransform.fourier chi).continuous.norm)).measurable
      (Complex.continuous_ofReal.comp (by
        unfold fourierNormReal
        fun_prop)).measurable
      (commutatorKernelComplex_integrable chi)
      (fourierNormReal_memLp_two phi).ofReal).toLp
        ((commutatorKernelComplex chi) ⋆[complexMulCLM]
          fun y => ((fourierNormReal phi y : ℝ) : ℂ)) =
      (commutatorMajorant_memLp_two chi phi).toLp
        (commutatorMajorant chi phi) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (convolution_mul_memLp_two
        (commutatorKernelComplex chi)
        (fun y => ((fourierNormReal phi y : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp (by
          unfold commutatorKernelReal
          exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs).mul
            (FourierTransform.fourier chi).continuous.norm)).measurable
        (Complex.continuous_ofReal.comp (by
          unfold fourierNormReal
          fun_prop)).measurable
        (commutatorKernelComplex_integrable chi)
        (fourierNormReal_memLp_two phi).ofReal),
      MemLp.coeFn_toLp (commutatorMajorant_memLp_two chi phi)] with xi h1 h2
    rw [h1, h2]
    rfl
  rw [hleft] at hyoung
  rw [norm_fourierNormComplex_toLp phi] at hyoung
  simpa [commutatorKernelComplex, commutatorMajorant] using hyoung

private def halfSmoothingCoefficient : ℝ :=
  abs ((-2 * Real.pi)⁻¹) *
    (Classical.choose point_smoothing).toReal ^ 2 / 4

private lemma halfSmoothingCoefficient_nonneg : 0 ≤ halfSmoothingCoefficient := by
  unfold halfSmoothingCoefficient
  positivity

private lemma cutoffHalfBoundConstant_eq (phi : SchwartzMap ℝ ℂ) :
    cutoffHalfBoundConstant phi =
      halfSmoothingCoefficient * ‖phi.toLp 2 volume‖ ^ 2 := by
  let C0 : ℝ≥0∞ := Classical.choose point_smoothing
  have hC0top : C0 ≠ ⊤ := (Classical.choose_spec point_smoothing).1.ne
  unfold cutoffHalfBoundConstant halfSmoothingCoefficient
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  ring

private lemma integral_cutoffHalfFrequency_eq_physical
    (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    (∫ xi : ℝ, ‖cutoffHalfFrequency chi phi t xi‖ ^ 2) =
      ∫ x : ℝ, cutoffHalfPhysicalSquare chi phi (x, t) := by
  have hleft : Integrable (fun xi : ℝ =>
      ‖cutoffHalfFrequency chi phi t xi‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (cutoffHalfFrequency_memLp_two chi phi t).1).mp
        (cutoffHalfFrequency_memLp_two chi phi t)
  have hright : Integrable (fun x : ℝ =>
      cutoffHalfPhysicalSquare chi phi (x, t)) := by
    have hprod := cutoffHalfPhysicalSquare_integrable chi phi
    have hsections := hprod.swap.prod_right_ae
    -- The explicit section estimate is available for every spatial point;
    -- for a fixed time, use the already proved Fourier-side `L²` slice.
    have hmem : MemLp (fun x =>
        chi x * canonicalHalfIntegral phi x (-2 * Real.pi * t)) 2 volume := by
      let q : L2 := (cutoffHalfFrequency_memLp_two chi phi t).toLp
        (cutoffHalfFrequency chi phi t)
      let qInv : L2 := fourierL2.symm q
      have hqInv : (qInv : ℝ → ℂ) =ᵐ[volume]
          fun x => chi x * canonicalHalfIntegral phi x (-2 * Real.pi * t) := by
        have hbridge := l1_l2_fourierInv_bridge
          (by simpa [cutoffHalfFrequency] using
            (memLp_one_iff_integrable.mpr
              (cutoffHalfFrequency_integrable chi phi t)))
          (cutoffHalfFrequency_memLp_two chi phi t)
        exact hbridge.trans (Filter.Eventually.of_forall
          (inverseIntegral_cutoffHalfFrequency chi phi t))
      exact (Lp.memLp qInv).congr_norm
        ((Lp.aestronglyMeasurable qInv).congr hqInv)
        (hqInv.mono fun x hx => by rw [hx])
    have hsquare := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
    exact hsquare.congr (Filter.Eventually.of_forall fun x => by
      unfold cutoffHalfPhysicalSquare
      rfl)
  have hleftOf := ofReal_integral_eq_lintegral_ofReal hleft
    (Filter.Eventually.of_forall fun xi => sq_nonneg _)
  have hrightOf := ofReal_integral_eq_lintegral_ofReal hright
    (Filter.Eventually.of_forall fun x => by
      unfold cutoffHalfPhysicalSquare
      positivity)
  have hlin := lintegral_cutoffHalfFrequency_eq_physical chi phi t
  rw [show (fun xi : ℝ => ENNReal.ofReal
      (‖cutoffHalfFrequency chi phi t xi‖ ^ 2)) =
      fun xi => ‖cutoffHalfFrequency chi phi t xi‖ₑ ^ (2 : ℝ) by
    funext xi
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    norm_num] at hleftOf
  rw [show (fun x : ℝ => ENNReal.ofReal
      (cutoffHalfPhysicalSquare chi phi (x, t))) =
      fun x => ‖chi x * canonicalHalfIntegral phi x
        (-2 * Real.pi * t)‖ₑ ^ (2 : ℝ) by
    funext x
    unfold cutoffHalfPhysicalSquare
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    norm_num] at hrightOf
  rw [hlin] at hleftOf
  rw [← hrightOf] at hleftOf
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun xi => sq_nonneg _)
    (integral_nonneg fun x => by
      unfold cutoffHalfPhysicalSquare
      positivity)).mp hleftOf

private lemma integral_cutoffHalfPhysicalSquare_prod_le
    (chi phi : SchwartzMap ℝ ℂ) :
    (∫ p : ℝ × ℝ, cutoffHalfPhysicalSquare chi phi p
      ∂(volume.prod volume)) ≤
      halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ ^ 2 *
        ‖phi.toLp 2 volume‖ ^ 2 := by
  rw [integral_prod _ (cutoffHalfPhysicalSquare_integrable chi phi)]
  have houter : Integrable (fun x : ℝ =>
      cutoffHalfBoundConstant phi * ‖chi x‖ ^ 2) := by
    exact ((memLp_two_iff_integrable_sq_norm
      chi.continuous.aestronglyMeasurable).mp
        (chi.memLp 2 volume)).const_mul _
  calc
    (∫ x : ℝ, ∫ t : ℝ, cutoffHalfPhysicalSquare chi phi (x, t)) ≤
        ∫ x : ℝ, cutoffHalfBoundConstant phi * ‖chi x‖ ^ 2 := by
      apply integral_mono_ae
      · exact (cutoffHalfPhysicalSquare_integrable chi phi).integral_prod_left
      · exact houter
      · filter_upwards with x
        exact integral_cutoffHalfPhysicalSquare_le chi phi x
    _ = cutoffHalfBoundConstant phi *
        ∫ x : ℝ, ‖chi x‖ ^ 2 := by rw [integral_const_mul]
    _ = cutoffHalfBoundConstant phi * ‖chi.toLp 2 volume‖ ^ 2 := by
      have hbundle : (chi.memLp 2 volume).toLp (chi : ℝ → ℂ) =
          chi.toLp 2 volume := by rfl
      rw [integral_norm_sq_toLp (chi.memLp 2 volume), hbundle]
    _ = halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ ^ 2 *
        ‖phi.toLp 2 volume‖ ^ 2 := by
      rw [cutoffHalfBoundConstant_eq]
      ring

private lemma integral_norm_sq_toLp_prod {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.prod volume)) :
    ∫ p, ‖f p‖ ^ 2 ∂(volume.prod volume) = ‖hf.toLp f‖ ^ 2 := by
  let g : Lp ℂ 2 (volume.prod volume) := hf.toLp f
  have hfg : (g : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume] f := hf.coeFn_toLp
  calc
    ∫ p, ‖f p‖ ^ 2 ∂(volume.prod volume) =
        ∫ p, ‖(g : ℝ × ℝ → ℂ) p‖ ^ 2 ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards [hfg] with p hp
      rw [hp]
    _ = ‖g‖ ^ 2 := by
      have h := lpNorm_eq_integral_norm_rpow_toReal
        (f := (g : ℝ × ℝ → ℂ)) (p := (2 : ENNReal))
          (by norm_num) (by norm_num) (Lp.aestronglyMeasurable g)
      have hlp : lpNorm (g : ℝ × ℝ → ℂ) 2 (volume.prod volume) = ‖g‖ := by
        rw [lpNorm, if_pos (Lp.aestronglyMeasurable g), Lp.norm_def]
      rw [hlp] at h
      norm_num at h
      rw [← Real.sqrt_eq_rpow] at h
      have hi : 0 ≤ ∫ p, ‖(g : ℝ × ℝ → ℂ) p‖ ^ 2
          ∂(volume.prod volume) := integral_nonneg fun _ => sq_nonneg _
      rw [h, Real.sq_sqrt hi]
    _ = ‖hf.toLp f‖ ^ 2 := rfl

private lemma norm_cutoffHalfProd_toLp_le (chi phi : SchwartzMap ℝ ℂ) :
    ‖(cutoffHalfFrequency_memLp_two_prod chi phi).toLp
      (fun p : ℝ × ℝ => cutoffHalfFrequency chi phi p.1 p.2)‖ ≤
      Real.sqrt halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ *
        ‖phi.toLp 2 volume‖ := by
  let q : Lp ℂ 2 (volume.prod volume) :=
    (cutoffHalfFrequency_memLp_two_prod chi phi).toLp
      (fun p : ℝ × ℝ => cutoffHalfFrequency chi phi p.1 p.2)
  have hfreqInt : Integrable (fun p : ℝ × ℝ =>
      ‖cutoffHalfFrequency chi phi p.1 p.2‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (cutoffHalfFrequency_memLp_two_prod chi phi).1).mp
        (cutoffHalfFrequency_memLp_two_prod chi phi)
  have heq : (∫ p : ℝ × ℝ,
      ‖cutoffHalfFrequency chi phi p.1 p.2‖ ^ 2
        ∂(volume.prod volume)) =
      ∫ p : ℝ × ℝ, cutoffHalfPhysicalSquare chi phi p
        ∂(volume.prod volume) := by
    rw [integral_prod _ hfreqInt,
      integral_prod_symm _ (cutoffHalfPhysicalSquare_integrable chi phi)]
    apply integral_congr_ae
    filter_upwards with t
    exact integral_cutoffHalfFrequency_eq_physical chi phi t
  have hsq : ‖q‖ ^ 2 ≤
      halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ ^ 2 *
        ‖phi.toLp 2 volume‖ ^ 2 := by
    rw [← integral_norm_sq_toLp_prod
      (cutoffHalfFrequency_memLp_two_prod chi phi)]
    rw [heq]
    exact integral_cutoffHalfPhysicalSquare_prod_le chi phi
  have hright0 : 0 ≤ Real.sqrt halfSmoothingCoefficient *
      ‖chi.toLp 2 volume‖ * ‖phi.toLp 2 volume‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg q) hright0).mp
  calc
    ‖q‖ ^ 2 ≤ halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ ^ 2 *
        ‖phi.toLp 2 volume‖ ^ 2 := hsq
    _ = (Real.sqrt halfSmoothingCoefficient) ^ 2 *
        ‖chi.toLp 2 volume‖ ^ 2 * ‖phi.toLp 2 volume‖ ^ 2 := by
      rw [Real.sq_sqrt halfSmoothingCoefficient_nonneg]
    _ = (Real.sqrt halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ *
        ‖phi.toLp 2 volume‖) ^ 2 := by ring

private lemma norm_toLp_le_three {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f f₁ f₂ f₃ : X → ℂ)
    (hf : MemLp f 2 mu) (h₁ : MemLp f₁ 2 mu)
    (h₂ : MemLp f₂ 2 mu) (h₃ : MemLp f₃ 2 mu)
    (hbound : ∀ x, ‖f x‖ ≤ ‖f₁ x‖ + ‖f₂ x‖ + ‖f₃ x‖) :
    ‖hf.toLp f‖ ≤ ‖h₁.toLp f₁‖ + ‖h₂.toLp f₂‖ + ‖h₃.toLp f₃‖ := by
  let M : X → ℝ := fun x => ‖f₁ x‖ + ‖f₂ x‖ + ‖f₃ x‖
  have hM : AEStronglyMeasurable M mu :=
    (h₁.1.norm.add h₂.1.norm).add h₃.1.norm
  have he₀ : eLpNorm f 2 mu ≤ eLpNorm M 2 mu := by
    apply eLpNorm_mono_enorm_ae
    filter_upwards with x
    rw [Real.enorm_eq_ofReal (by
      dsimp [M]
      positivity), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hbound x)
  have he₁ : eLpNorm M 2 mu ≤
      eLpNorm (fun x => ‖f₁ x‖ + ‖f₂ x‖) 2 mu +
        eLpNorm (fun x => ‖f₃ x‖) 2 mu := by
    exact eLpNorm_add_le (h₁.1.norm.add h₂.1.norm) h₃.1.norm (by norm_num)
  have he₂ : eLpNorm (fun x => ‖f₁ x‖ + ‖f₂ x‖) 2 mu ≤
      eLpNorm (fun x => ‖f₁ x‖) 2 mu +
        eLpNorm (fun x => ‖f₂ x‖) 2 mu :=
    eLpNorm_add_le h₁.1.norm h₂.1.norm (by norm_num)
  have henorm (g : X → ℂ) (hg : AEStronglyMeasurable g mu) :
      eLpNorm (fun x => ‖g x‖) 2 mu = eLpNorm g 2 mu := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    simp
  have he : eLpNorm f 2 mu ≤
      eLpNorm f₁ 2 mu + eLpNorm f₂ 2 mu + eLpNorm f₃ 2 mu := by
    calc
      eLpNorm f 2 mu ≤ eLpNorm M 2 mu := he₀
      _ ≤ eLpNorm (fun x => ‖f₁ x‖ + ‖f₂ x‖) 2 mu +
          eLpNorm (fun x => ‖f₃ x‖) 2 mu := he₁
      _ ≤ (eLpNorm (fun x => ‖f₁ x‖) 2 mu +
          eLpNorm (fun x => ‖f₂ x‖) 2 mu) +
          eLpNorm (fun x => ‖f₃ x‖) 2 mu := by
        exact add_le_add he₂ le_rfl
      _ = _ := by rw [henorm f₁ h₁.1, henorm f₂ h₂.1, henorm f₃ h₃.1]
  have htop : eLpNorm f₁ 2 mu + eLpNorm f₂ 2 mu + eLpNorm f₃ 2 mu ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨h₁.eLpNorm_ne_top, h₂.eLpNorm_ne_top⟩, h₃.eLpNorm_ne_top⟩
  have hr := ENNReal.toReal_mono htop he
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨h₁.eLpNorm_ne_top, h₂.eLpNorm_ne_top⟩)
      h₃.eLpNorm_ne_top,
    ENNReal.toReal_add h₁.eLpNorm_ne_top h₂.eLpNorm_ne_top,
    toReal_eLpNorm hf.1, toReal_eLpNorm h₁.1,
    toReal_eLpNorm h₂.1, toReal_eLpNorm h₃.1] at hr
  rw [Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm hf.1, toReal_eLpNorm h₁.1,
    toReal_eLpNorm h₂.1, toReal_eLpNorm h₃.1]
  exact hr

private lemma norm_toLp_mono_measure {X : Type*} [MeasurableSpace X]
    {mu nu : Measure X} (hmunu : mu ≤ nu) (f : X → ℂ)
    (hf : MemLp f 2 nu) :
    ‖(hf.mono_measure hmunu).toLp f‖ ≤ ‖hf.toLp f‖ := by
  have he := eLpNorm_mono_measure f hmunu (p := (2 : ℝ≥0∞))
  have hr := ENNReal.toReal_mono hf.eLpNorm_ne_top he
  rw [toReal_eLpNorm (hf.mono_measure hmunu).1,
    toReal_eLpNorm hf.1] at hr
  rw [Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm (hf.mono_measure hmunu).1,
    toReal_eLpNorm hf.1]
  exact hr

private def weightedProductLp (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp ℂ 2 (((volume : Measure ℝ).restrict (Icc a b)).prod
      (volume : Measure ℝ)) :=
  (weightedCutoffFrequency_memLp_two_prod_Icc chi phi a b).toLp
    (weightedCutoffFrequency chi phi)

private lemma norm_localizedFreeSchwartzCurveLp_eq_weightedProduct
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ‖localizedFreeSchwartzCurveLp chi a b phi‖ =
      ‖weightedProductLp chi phi a b‖ := by
  let mu : Measure ℝ := volume.restrict (Icc a b)
  have he : eLpNorm (localizedFreeSchwartzHs chi phi) 2 mu =
      eLpNorm (weightedCutoffFrequency chi phi) 2 (mu.prod volume) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
      eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    norm_num only [ENNReal.toReal_ofNat]
    congr 1
    rw [lintegral_prod _
      ((weightedCutoffFrequency_memLp_two_prod_Icc chi phi a b).1.enorm.pow_const 2)]
    apply lintegral_congr
    intro t
    rw [show ‖localizedFreeSchwartzHs chi phi t‖ₑ =
        ‖weightedCutoffL2 chi phi t‖ₑ by
      unfold localizedFreeSchwartzHs HsHalfOfWeightedFourier
      rw [LinearIsometryEquiv.enorm_map]]
    convert (lintegral_enorm_sq_toLp
      (weightedCutoffFrequency_memLp_two chi phi t)).symm using 1 <;>
        norm_num [weightedCutoffL2]
  rw [localizedFreeSchwartzCurveLp, weightedProductLp,
    Lp.norm_toLp, Lp.norm_toLp, he]

private def cutoffFreeProdLp (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp ℂ 2 (((volume : Measure ℝ).restrict (Icc a b)).prod
      (volume : Measure ℝ)) :=
  (cutoffFreeFrequency_memLp_two_prod_Icc chi phi a b).toLp
    (fun p => cutoffFreeFrequency chi phi p.1 p.2)

private def cutoffHalfRestrictedLp (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp ℂ 2 (((volume : Measure ℝ).restrict (Icc a b)).prod
      (volume : Measure ℝ)) :=
  ((cutoffHalfFrequency_memLp_two_prod chi phi).mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl)).toLp
      (fun p => cutoffHalfFrequency chi phi p.1 p.2)

private def cutoffCommutatorProdLp (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    Lp ℂ 2 (((volume : Measure ℝ).restrict (Icc a b)).prod
      (volume : Measure ℝ)) :=
  (cutoffCommutatorFrequency_memLp_two_prod_Icc chi phi a b).toLp
    (fun p => cutoffCommutatorFrequency chi phi p.1 p.2)

set_option maxHeartbeats 4000000 in
private lemma norm_weightedProduct_le_components
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ‖weightedProductLp chi phi a b‖ ≤
      ‖cutoffFreeProdLp chi phi a b‖ +
      ‖cutoffHalfRestrictedLp chi phi a b‖ +
      ‖cutoffCommutatorProdLp chi phi a b‖ := by
  let mu : Measure (ℝ × ℝ) :=
    ((volume : Measure ℝ).restrict (Icc a b)).prod (volume : Measure ℝ)
  have hraw := norm_toLp_le_three mu
    (weightedCutoffFrequency chi phi)
    (fun p : ℝ × ℝ => cutoffFreeFrequency chi phi p.1 p.2)
    (fun p : ℝ × ℝ => cutoffHalfFrequency chi phi p.1 p.2)
    (fun p : ℝ × ℝ => cutoffCommutatorFrequency chi phi p.1 p.2)
    (weightedCutoffFrequency_memLp_two_prod_Icc chi phi a b)
    (cutoffFreeFrequency_memLp_two_prod_Icc chi phi a b)
    ((cutoffHalfFrequency_memLp_two_prod chi phi).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl))
    (cutoffCommutatorFrequency_memLp_two_prod_Icc chi phi a b)
  simpa only [weightedProductLp, cutoffFreeProdLp, cutoffHalfRestrictedLp,
    cutoffCommutatorProdLp, mu] using hraw (by
  intro p
  unfold weightedCutoffFrequency
  rw [norm_mul]
  calc
    ‖positiveHalfWeight p.2‖ *
        ‖cutoffFreeFrequency chi phi p.1 p.2‖ ≤
      (1 + |p.2| ^ (1 / 2 : ℝ)) *
        ‖cutoffFreeFrequency chi phi p.1 p.2‖ := by
      gcongr
      exact norm_positiveHalfWeight_le p.2
    _ = ‖cutoffFreeFrequency chi phi p.1 p.2‖ +
        ‖homogeneousCutoffFrequency chi phi p.1 p.2‖ := by
      unfold homogeneousCutoffFrequency
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg p.2) _)]
      ring
    _ ≤ ‖cutoffFreeFrequency chi phi p.1 p.2‖ +
        ‖cutoffHalfFrequency chi phi p.1 p.2‖ +
        ‖cutoffCommutatorFrequency chi phi p.1 p.2‖ := by
      rw [homogeneousCutoffFrequency_eq]
      calc
        ‖cutoffFreeFrequency chi phi p.1 p.2‖ +
            ‖cutoffHalfFrequency chi phi p.1 p.2 +
              cutoffCommutatorFrequency chi phi p.1 p.2‖ ≤
          ‖cutoffFreeFrequency chi phi p.1 p.2‖ +
            (‖cutoffHalfFrequency chi phi p.1 p.2‖ +
              ‖cutoffCommutatorFrequency chi phi p.1 p.2‖) :=
            add_le_add le_rfl (norm_add_le _ _)
        _ = _ := by ring)

private def timeIccFactor (a b : ℝ) : ℝ :=
  (((volume : Measure ℝ).restrict (Icc a b) Set.univ) ^
    (1 / (2 : ℝ≥0∞)).toReal).toReal

private def freeYoungCoefficient (chi : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(memLp_one_iff_integrable.mpr (freeKernelAbs_integrable chi)).toLp
    (freeKernelAbs chi)‖

private def commutatorYoungCoefficient (chi : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(memLp_one_iff_integrable.mpr
    (commutatorKernelComplex_integrable chi)).toLp
      (commutatorKernelComplex chi)‖

private lemma norm_cutoffFreeProdLp_le (chi phi : SchwartzMap ℝ ℂ)
    (a b : ℝ) :
    ‖cutoffFreeProdLp chi phi a b‖ ≤
      timeIccFactor a b * freeYoungCoefficient chi *
        ‖phi.toLp 2 volume‖ := by
  have hmajor := norm_toLp_prod_Icc_le_snd_majorant
    (fun p : ℝ × ℝ => cutoffFreeFrequency chi phi p.1 p.2)
    (cutoffFreeFrequency_memLp_two_prod_Icc chi phi a b)
    (freeMajorant chi phi) (freeMajorant_memLp_two chi phi)
    (fun p => norm_cutoffFreeFrequency_le chi phi p.1 p.2)
  rw [show ‖(cutoffFreeFrequency_memLp_two_prod_Icc chi phi a b).toLp
      (fun p : ℝ × ℝ => cutoffFreeFrequency chi phi p.1 p.2)‖ =
      ‖cutoffFreeProdLp chi phi a b‖ by rfl] at hmajor
  calc
    ‖cutoffFreeProdLp chi phi a b‖ ≤
        timeIccFactor a b *
          ‖(freeMajorant_memLp_two chi phi).toLp
            (freeMajorant chi phi)‖ := by
      simpa only [timeIccFactor] using hmajor
    _ ≤ timeIccFactor a b *
        (freeYoungCoefficient chi * ‖phi.toLp 2 volume‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_freeMajorant_toLp_le chi phi) (by
          unfold timeIccFactor
          positivity)
    _ = _ := by ring

private lemma norm_cutoffCommutatorProdLp_le
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ‖cutoffCommutatorProdLp chi phi a b‖ ≤
      timeIccFactor a b * commutatorYoungCoefficient chi *
        ‖phi.toLp 2 volume‖ := by
  have hmajor := norm_toLp_prod_Icc_le_snd_majorant
    (fun p : ℝ × ℝ => cutoffCommutatorFrequency chi phi p.1 p.2)
    (cutoffCommutatorFrequency_memLp_two_prod_Icc chi phi a b)
    (commutatorMajorant chi phi) (commutatorMajorant_memLp_two chi phi)
    (fun p => norm_cutoffCommutatorFrequency_le chi phi p.1 p.2)
  rw [show ‖(cutoffCommutatorFrequency_memLp_two_prod_Icc chi phi a b).toLp
      (fun p : ℝ × ℝ => cutoffCommutatorFrequency chi phi p.1 p.2)‖ =
      ‖cutoffCommutatorProdLp chi phi a b‖ by rfl] at hmajor
  calc
    ‖cutoffCommutatorProdLp chi phi a b‖ ≤
        timeIccFactor a b *
          ‖(commutatorMajorant_memLp_two chi phi).toLp
            (commutatorMajorant chi phi)‖ := by
      simpa only [timeIccFactor] using hmajor
    _ ≤ timeIccFactor a b *
        (commutatorYoungCoefficient chi * ‖phi.toLp 2 volume‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_commutatorMajorant_toLp_le chi phi) (by
          unfold timeIccFactor
          positivity)
    _ = _ := by ring

private lemma norm_cutoffHalfRestrictedLp_le
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ‖cutoffHalfRestrictedLp chi phi a b‖ ≤
      Real.sqrt halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ *
        ‖phi.toLp 2 volume‖ := by
  have hmeasure :
      ((volume : Measure ℝ).restrict (Icc a b)).prod (volume : Measure ℝ) ≤
        (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hmono := norm_toLp_mono_measure hmeasure
    (fun p : ℝ × ℝ => cutoffHalfFrequency chi phi p.1 p.2)
    (cutoffHalfFrequency_memLp_two_prod chi phi)
  rw [show ‖((cutoffHalfFrequency_memLp_two_prod chi phi).mono_measure
      hmeasure).toLp
        (fun p : ℝ × ℝ => cutoffHalfFrequency chi phi p.1 p.2)‖ =
      ‖cutoffHalfRestrictedLp chi phi a b‖ by rfl] at hmono
  exact hmono.trans (norm_cutoffHalfProd_toLp_le chi phi)

def localizedFreeBound (chi : SchwartzMap ℝ ℂ) (a b : ℝ) : ℝ :=
  timeIccFactor a b * freeYoungCoefficient chi +
    Real.sqrt halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ +
    timeIccFactor a b * commutatorYoungCoefficient chi

lemma localizedFreeBound_nonneg (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    0 ≤ localizedFreeBound chi a b := by
  unfold localizedFreeBound timeIccFactor freeYoungCoefficient
    commutatorYoungCoefficient
  positivity

private lemma norm_localizedFreeSchwartzCurveLinear_le
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    ‖localizedFreeSchwartzCurveLinear chi a b phi‖ ≤
      localizedFreeBound chi a b * ‖phi.toLp 2 volume‖ := by
  rw [show localizedFreeSchwartzCurveLinear chi a b phi =
      localizedFreeSchwartzCurveLp chi a b phi by rfl,
    norm_localizedFreeSchwartzCurveLp_eq_weightedProduct]
  calc
    ‖weightedProductLp chi phi a b‖ ≤
        ‖cutoffFreeProdLp chi phi a b‖ +
          ‖cutoffHalfRestrictedLp chi phi a b‖ +
          ‖cutoffCommutatorProdLp chi phi a b‖ :=
      norm_weightedProduct_le_components chi phi a b
    _ ≤ (timeIccFactor a b * freeYoungCoefficient chi *
          ‖phi.toLp 2 volume‖) +
        (Real.sqrt halfSmoothingCoefficient * ‖chi.toLp 2 volume‖ *
          ‖phi.toLp 2 volume‖) +
        (timeIccFactor a b * commutatorYoungCoefficient chi *
          ‖phi.toLp 2 volume‖) := by
      gcongr
      · exact norm_cutoffFreeProdLp_le chi phi a b
      · exact norm_cutoffHalfRestrictedLp_le chi phi a b
      · exact norm_cutoffCommutatorProdLp_le chi phi a b
    _ = localizedFreeBound chi a b * ‖phi.toLp 2 volume‖ := by
      unfold localizedFreeBound
      ring

def localizedFreeCurveCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    L2 →L[ℝ] Lp (Hs (1 / 2 : ℝ)) 2 (volume.restrict (Icc a b)) :=
  LinearMap.extendOfNorm
    (LinearMap.restrictScalars ℝ (localizedFreeSchwartzCurveLinear chi a b))
    (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)).toLinearMap

lemma localizedFreeCurveCLM_schwartz
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    localizedFreeCurveCLM chi a b (phi.toLp 2 volume) =
      localizedFreeSchwartzCurveLp chi a b phi := by
  unfold localizedFreeCurveCLM
  have h := LinearMap.extendOfNorm_eq
    (f := LinearMap.restrictScalars ℝ
      (localizedFreeSchwartzCurveLinear chi a b))
    (e := (SchwartzMap.toLpCLM ℝ ℂ 2
      (volume : Measure ℝ)).toLinearMap)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure ℝ)) (by norm_num))
    ⟨localizedFreeBound chi a b, fun q => by
      change ‖localizedFreeSchwartzCurveLinear chi a b q‖ ≤
        localizedFreeBound chi a b * ‖q.toLp 2 volume‖
      exact norm_localizedFreeSchwartzCurveLinear_le chi q a b⟩ phi
  simpa [SchwartzMap.toLpCLM_apply, localizedFreeSchwartzCurveLinear] using h

lemma norm_localizedFreeCurveCLM_le
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (f : L2) :
    ‖localizedFreeCurveCLM chi a b f‖ ≤
      localizedFreeBound chi a b * ‖f‖ := by
  unfold localizedFreeCurveCLM
  exact LinearMap.norm_extendOfNorm_apply_le
    (f := LinearMap.restrictScalars ℝ
      (localizedFreeSchwartzCurveLinear chi a b))
    (e := (SchwartzMap.toLpCLM ℝ ℂ 2
      (volume : Measure ℝ)).toLinearMap)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure ℝ)) (by norm_num))
    (localizedFreeBound chi a b)
    (fun q => by
      change ‖localizedFreeSchwartzCurveLinear chi a b q‖ ≤
        localizedFreeBound chi a b * ‖q.toLp 2 volume‖
      exact norm_localizedFreeSchwartzCurveLinear_le chi q a b) f

/-! ### Physical realization of the extended curve -/

/-- A concrete uniform bound for a Schwartz cutoff. -/
def schwartzCutoffBound (chi : SchwartzMap ℝ ℂ) : ℝ :=
  (SchwartzMap.seminorm ℂ 0 0) chi

lemma norm_chi_le_schwartzCutoffBound (chi : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖chi x‖ ≤ schwartzCutoffBound chi := by
  have h := SchwartzMap.le_seminorm ℂ 0 0 chi x
  simpa [schwartzCutoffBound] using h

lemma schwartzCutoffBound_nonneg (chi : SchwartzMap ℝ ℂ) :
    0 ≤ schwartzCutoffBound chi :=
  (norm_nonneg (chi 0)).trans (norm_chi_le_schwartzCutoffBound chi 0)

private def cutoffSymbolLp (chi : SchwartzMap ℝ ℂ) :
    Lp ℂ ⊤ (volume : Measure ℝ) :=
  (memLp_top_of_bound chi.continuous.aestronglyMeasurable
    (schwartzCutoffBound chi)
    (Filter.Eventually.of_forall
      (norm_chi_le_schwartzCutoffBound chi))).toLp chi

private lemma coe_cutoffSymbolLp (chi : SchwartzMap ℝ ℂ) :
    (cutoffSymbolLp chi : ℝ → ℂ) =ᵐ[volume] chi := by
  exact MemLp.coeFn_toLp _

private lemma norm_cutoffSymbolLp_le (chi : SchwartzMap ℝ ℂ) :
    ‖cutoffSymbolLp chi‖ ≤ schwartzCutoffBound chi := by
  rw [Lp.norm_def]
  calc
    (eLpNorm (cutoffSymbolLp chi : ℝ → ℂ) ⊤ volume).toReal ≤
        (ENNReal.ofReal (schwartzCutoffBound chi)).toReal := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      rw [eLpNorm_congr_ae (coe_cutoffSymbolLp chi), eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound
        (Filter.Eventually.of_forall
          (norm_chi_le_schwartzCutoffBound chi))
    _ = schwartzCutoffBound chi :=
      ENNReal.toReal_ofReal (schwartzCutoffBound_nonneg chi)

private def cutoffL2Linear (chi : SchwartzMap ℝ ℂ) : L2 →ₗ[ℂ] L2 where
  toFun f := cutoffSymbolLp chi • f
  map_add' f g := Lp.add_smul (r := 2) _ _ _
  map_smul' c f := (Lp.smul_comm (r := 2) c (cutoffSymbolLp chi) f).symm

/-- Multiplication by a Schwartz cutoff on physical `L²`. -/
def cutoffL2CLM (chi : SchwartzMap ℝ ℂ) : L2 →L[ℂ] L2 :=
  (cutoffL2Linear chi).mkContinuous (schwartzCutoffBound chi) fun f => by
    exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_cutoffSymbolLp_le chi) (norm_nonneg f))

lemma coe_cutoffL2CLM (chi : SchwartzMap ℝ ℂ) (f : L2) :
    (cutoffL2CLM chi f : ℝ → ℂ) =ᵐ[volume]
      fun x => chi x * (f : ℝ → ℂ) x := by
  change ((cutoffSymbolLp chi • f : L2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (cutoffSymbolLp chi) f,
    coe_cutoffSymbolLp chi] with x hmul hchi
  rw [hmul]
  change (cutoffSymbolLp chi : ℝ → ℂ) x * (f : ℝ → ℂ) x = _
  rw [hchi]

lemma toTemperedDistribution_cutoffL2CLM
    (chi : SchwartzMap ℝ ℂ) (f : L2) :
    MeasureTheory.Lp.toTemperedDistribution (cutoffL2CLM chi f) =
      TemperedDistribution.smulLeftCLM ℂ (chi : ℝ → ℂ)
        (MeasureTheory.Lp.toTemperedDistribution f) := by
  change MeasureTheory.Lp.toTemperedDistribution
      (cutoffSymbolLp chi • f) = _
  unfold cutoffSymbolLp
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq
    chi.hasTemperateGrowth]

lemma norm_cutoffL2CLM_le (chi : SchwartzMap ℝ ℂ) (f : L2) :
    ‖cutoffL2CLM chi f‖ ≤ schwartzCutoffBound chi * ‖f‖ := by
  exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
    (norm_cutoffSymbolLp_le chi) (norm_nonneg f))

/-- The physical cutoff of the free evolution. -/
def localizedPhysicalFree (chi : SchwartzMap ℝ ℂ) (f : L2) (t : ℝ) : L2 :=
  cutoffL2CLM chi (freeProp t f)

lemma continuous_localizedPhysicalFree (chi : SchwartzMap ℝ ℂ) (f : L2) :
    Continuous (localizedPhysicalFree chi f) := by
  exact (cutoffL2CLM chi).continuous.comp
    (propagator_unitary.2.2.2.1 f)

lemma norm_localizedPhysicalFree_le
    (chi : SchwartzMap ℝ ℂ) (f : L2) (t : ℝ) :
    ‖localizedPhysicalFree chi f t‖ ≤
      schwartzCutoffBound chi * ‖f‖ := by
  exact (norm_cutoffL2CLM_le chi (freeProp t f)).trans_eq
    (congrArg (schwartzCutoffBound chi * ·) (norm_freeProp t f))

lemma localizedPhysicalFree_memLp_two_Icc
    (chi : SchwartzMap ℝ ℂ) (f : L2) (a b : ℝ) :
    MemLp (localizedPhysicalFree chi f) 2
      (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound
    (continuous_localizedPhysicalFree chi f).aestronglyMeasurable
    (schwartzCutoffBound chi * ‖f‖)
  exact Filter.Eventually.of_forall
    (norm_localizedPhysicalFree_le chi f)

/-- The physical cutoff free curve, bundled in `L²_t L²_x`. -/
def localizedPhysicalFreeCurveLp (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (f : L2) : Lp L2 2 (volume.restrict (Icc a b)) :=
  (localizedPhysicalFree_memLp_two_Icc chi f a b).toLp
    (localizedPhysicalFree chi f)

lemma norm_localizedPhysicalFreeCurveLp_le
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (f : L2) :
    ‖localizedPhysicalFreeCurveLp chi a b f‖ ≤
      ((measureUnivNNReal (volume.restrict (Icc a b)) ^
          (2 : ℝ≥0∞).toReal⁻¹ : NNReal) : ℝ) *
        (schwartzCutoffBound chi * ‖f‖) := by
  apply Lp.norm_le_of_ae_bound
    (mul_nonneg (schwartzCutoffBound_nonneg chi) (norm_nonneg f))
  filter_upwards [MemLp.coeFn_toLp
    (localizedPhysicalFree_memLp_two_Icc chi f a b)] with t ht
  rw [show (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t =
      localizedPhysicalFree chi f t by exact ht]
  exact norm_localizedPhysicalFree_le chi f t

private lemma localizedPhysicalFree_add (chi : SchwartzMap ℝ ℂ)
    (f g : L2) (t : ℝ) :
    localizedPhysicalFree chi (f + g) t =
      localizedPhysicalFree chi f t + localizedPhysicalFree chi g t := by
  unfold localizedPhysicalFree
  rw [freeProp_add_apply, map_add]

private lemma localizedPhysicalFree_smul (chi : SchwartzMap ℝ ℂ)
    (c : ℂ) (f : L2) (t : ℝ) :
    localizedPhysicalFree chi (c • f) t =
      c • localizedPhysicalFree chi f t := by
  unfold localizedPhysicalFree
  rw [freeProp_smul, map_smul]

private lemma localizedPhysicalFreeCurveLp_add (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (f g : L2) :
    localizedPhysicalFreeCurveLp chi a b (f + g) =
      localizedPhysicalFreeCurveLp chi a b f +
        localizedPhysicalFreeCurveLp chi a b g := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (localizedPhysicalFree_memLp_two_Icc chi (f + g) a b),
    MemLp.coeFn_toLp (localizedPhysicalFree_memLp_two_Icc chi f a b),
    MemLp.coeFn_toLp (localizedPhysicalFree_memLp_two_Icc chi g a b),
    Lp.coeFn_add (localizedPhysicalFreeCurveLp chi a b f)
      (localizedPhysicalFreeCurveLp chi a b g)] with t hsum hf hg hout
  rw [show (localizedPhysicalFreeCurveLp chi a b (f + g) : ℝ → L2) t =
      localizedPhysicalFree chi (f + g) t by exact hsum,
    show ((localizedPhysicalFreeCurveLp chi a b f +
        localizedPhysicalFreeCurveLp chi a b g :
          Lp L2 2 (volume.restrict (Icc a b))) : ℝ → L2) t =
      (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t +
        (localizedPhysicalFreeCurveLp chi a b g : ℝ → L2) t by exact hout,
    show (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t =
      localizedPhysicalFree chi f t by exact hf,
    show (localizedPhysicalFreeCurveLp chi a b g : ℝ → L2) t =
      localizedPhysicalFree chi g t by exact hg,
    localizedPhysicalFree_add]

private lemma localizedPhysicalFreeCurveLp_smul (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) (c : ℂ) (f : L2) :
    localizedPhysicalFreeCurveLp chi a b (c • f) =
      c • localizedPhysicalFreeCurveLp chi a b f := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (localizedPhysicalFree_memLp_two_Icc chi (c • f) a b),
    MemLp.coeFn_toLp (localizedPhysicalFree_memLp_two_Icc chi f a b),
    Lp.coeFn_smul c (localizedPhysicalFreeCurveLp chi a b f)]
      with t hleft hf hout
  rw [show (localizedPhysicalFreeCurveLp chi a b (c • f) : ℝ → L2) t =
      localizedPhysicalFree chi (c • f) t by exact hleft,
    show ((c • localizedPhysicalFreeCurveLp chi a b f :
      Lp L2 2 (volume.restrict (Icc a b))) : ℝ → L2) t =
      c • (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t by exact hout,
    show (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t =
      localizedPhysicalFree chi f t by exact hf,
    localizedPhysicalFree_smul]

private def localizedPhysicalFreeCurveLinear (chi : SchwartzMap ℝ ℂ)
    (a b : ℝ) : L2 →ₗ[ℂ] Lp L2 2 (volume.restrict (Icc a b)) where
  toFun := localizedPhysicalFreeCurveLp chi a b
  map_add' := localizedPhysicalFreeCurveLp_add chi a b
  map_smul' := localizedPhysicalFreeCurveLp_smul chi a b

/-- A norm bound for the physical cutoff curve. -/
def physicalFreeCurveBound (chi : SchwartzMap ℝ ℂ) (a b : ℝ) : ℝ :=
  ((measureUnivNNReal (volume.restrict (Icc a b)) ^
      (2 : ℝ≥0∞).toReal⁻¹ : NNReal) : ℝ) * schwartzCutoffBound chi

private lemma norm_localizedPhysicalFreeCurveLinear_le
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (f : L2) :
    ‖localizedPhysicalFreeCurveLinear chi a b f‖ ≤
      physicalFreeCurveBound chi a b * ‖f‖ := by
  rw [show localizedPhysicalFreeCurveLinear chi a b f =
      localizedPhysicalFreeCurveLp chi a b f by rfl]
  calc
    ‖localizedPhysicalFreeCurveLp chi a b f‖ ≤
        ((measureUnivNNReal (volume.restrict (Icc a b)) ^
            (2 : ℝ≥0∞).toReal⁻¹ : NNReal) : ℝ) *
          (schwartzCutoffBound chi * ‖f‖) :=
      norm_localizedPhysicalFreeCurveLp_le chi a b f
    _ = physicalFreeCurveBound chi a b * ‖f‖ := by
      unfold physicalFreeCurveBound
      ring

/-- The physical cutoff free curve as a complex continuous linear map. -/
def localizedPhysicalFreeCurveCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    L2 →L[ℂ] Lp L2 2 (volume.restrict (Icc a b)) :=
  (localizedPhysicalFreeCurveLinear chi a b).mkContinuous
    (physicalFreeCurveBound chi a b)
    (norm_localizedPhysicalFreeCurveLinear_le chi a b)

@[simp] lemma localizedPhysicalFreeCurveCLM_apply
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (f : L2) :
    localizedPhysicalFreeCurveCLM chi a b f =
      localizedPhysicalFreeCurveLp chi a b f := rfl

/-- Apply the physical `H^{1/2} → L²` realization at almost every time. -/
def realizedLocalizedFreeCurveCLM (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    L2 →L[ℝ] Lp L2 2 (volume.restrict (Icc a b)) :=
  ((hsHalfToL2CLM.restrictScalars ℝ).compLpL 2
      (volume.restrict (Icc a b))).comp
    (localizedFreeCurveCLM chi a b)

private lemma localizedPhysicalFree_schwartz_eq
    (chi phi : SchwartzMap ℝ ℂ) (t : ℝ) :
    localizedPhysicalFree chi (phi.toLp 2 volume) t =
      cutoffPhysicalL2 chi phi t := by
  apply Lp.ext
  filter_upwards [coe_cutoffL2CLM chi
      (freeProp t (phi.toLp 2 volume)),
    coe_cutoffPhysicalL2 chi phi t] with x hleft hright
  rw [show (localizedPhysicalFree chi (phi.toLp 2 volume) t : ℝ → ℂ) x =
      chi x * (freeProp t (phi.toLp 2 volume) : ℝ → ℂ) x by
        exact hleft,
    show (cutoffPhysicalL2 chi phi t : ℝ → ℂ) x =
      chi x * (freeProp t (phi.toLp 2 volume) : ℝ → ℂ) x by
        exact hright]

private lemma realizedLocalizedFreeCurveCLM_schwartz
    (chi phi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    realizedLocalizedFreeCurveCLM chi a b (phi.toLp 2 volume) =
      localizedPhysicalFreeCurveLp chi a b (phi.toLp 2 volume) := by
  unfold realizedLocalizedFreeCurveCLM
  rw [ContinuousLinearMap.comp_apply, localizedFreeCurveCLM_schwartz]
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (hsHalfToL2CLM.restrictScalars ℝ)
        (localizedFreeSchwartzCurveLp chi a b phi),
    MemLp.coeFn_toLp
      (localizedFreeSchwartzHs_memLp_two_Icc chi phi a b),
    MemLp.coeFn_toLp
      (localizedPhysicalFree_memLp_two_Icc chi
        (phi.toLp 2 volume) a b)] with t hreal hsch hphys
  rw [show (((hsHalfToL2CLM.restrictScalars ℝ).compLpL 2
        (volume.restrict (Icc a b)))
          (localizedFreeSchwartzCurveLp chi a b phi) : ℝ → L2) t =
      hsHalfToL2CLM
        (localizedFreeSchwartzCurveLp chi a b phi t) by exact hreal,
    show (localizedFreeSchwartzCurveLp chi a b phi :
        ℝ → Hs (1 / 2 : ℝ)) t =
      localizedFreeSchwartzHs chi phi t by exact hsch,
    hsHalfToL2CLM_apply,
    localizedFreeSchwartzHs_toL2,
    show (localizedPhysicalFreeCurveLp chi a b
        (phi.toLp 2 volume) : ℝ → L2) t =
      localizedPhysicalFree chi (phi.toLp 2 volume) t by exact hphys,
    localizedPhysicalFree_schwartz_eq]

theorem realizedLocalizedFreeCurveCLM_eq
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) :
    realizedLocalizedFreeCurveCLM chi a b =
      (localizedPhysicalFreeCurveCLM chi a b).restrictScalars ℝ := by
  have hfun :
      (realizedLocalizedFreeCurveCLM chi a b :
        L2 → Lp L2 2 (volume.restrict (Icc a b))) =
      ((localizedPhysicalFreeCurveCLM chi a b).restrictScalars ℝ :
        L2 → Lp L2 2 (volume.restrict (Icc a b))) := by
    apply (SchwartzMap.denseRange_toLpCLM
      (F := ℂ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℝ))
      (by norm_num)).equalizer
      (realizedLocalizedFreeCurveCLM chi a b).continuous
      ((localizedPhysicalFreeCurveCLM chi a b).restrictScalars ℝ).continuous
    funext phi
    change realizedLocalizedFreeCurveCLM chi a b (phi.toLp 2 volume) =
      localizedPhysicalFreeCurveCLM chi a b (phi.toLp 2 volume)
    rw [localizedPhysicalFreeCurveCLM_apply]
    exact realizedLocalizedFreeCurveCLM_schwartz chi phi a b
  exact DFunLike.coe_injective hfun

theorem realizedLocalizedFreeCurveCLM_apply
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (f : L2) :
    realizedLocalizedFreeCurveCLM chi a b f =
      localizedPhysicalFreeCurveLp chi a b f := by
  rw [realizedLocalizedFreeCurveCLM_eq]
  rfl

/-- The density extension is represented by the actual physical cutoff of the
free evolution. -/
theorem localizedFreeCurveCLM_represents
    (chi : SchwartzMap ℝ ℂ) (a b : ℝ) (f : L2) :
    IsLocalizedHsRepresentative chi (Icc a b)
      (fun t => freeProp t f)
      (localizedFreeCurveCLM chi a b f : ℝ → Hs (1 / 2 : ℝ)) := by
  let mu : Measure ℝ := volume.restrict (Icc a b)
  have hreal := ContinuousLinearMap.coeFn_compLpL
    (hsHalfToL2CLM.restrictScalars ℝ)
    (localizedFreeCurveCLM chi a b f)
  have hphys := MemLp.coeFn_toLp
    (localizedPhysicalFree_memLp_two_Icc chi f a b)
  have hcurve :
      (realizedLocalizedFreeCurveCLM chi a b f : ℝ → L2) =
        (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) :=
    congrArg (fun q : Lp L2 2 mu => (q : ℝ → L2))
      (realizedLocalizedFreeCurveCLM_apply chi a b f)
  filter_upwards [hreal, hphys] with t hreal_t hphys_t
  have hL2 :
      hsHalfToL2CLM
          ((localizedFreeCurveCLM chi a b f :
            ℝ → Hs (1 / 2 : ℝ)) t) =
        localizedPhysicalFree chi f t := by
    calc
      hsHalfToL2CLM
          ((localizedFreeCurveCLM chi a b f :
            ℝ → Hs (1 / 2 : ℝ)) t) =
          (realizedLocalizedFreeCurveCLM chi a b f : ℝ → L2) t :=
        hreal_t.symm
      _ = (localizedPhysicalFreeCurveLp chi a b f : ℝ → L2) t :=
        congrFun hcurve t
      _ = localizedPhysicalFree chi f t := hphys_t
  rw [Hs.toTempered_toL2 (s := (1 / 2 : ℝ)) (by norm_num)]
  rw [← hsHalfToL2CLM_apply, hL2]
  exact toTemperedDistribution_cutoffL2CLM chi (freeProp t f)

end CubicNLSPhaseRetrieval
