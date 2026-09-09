import Lean_Code.CriticalCurrentExtension
import Lean_Code.YoungConvolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Compact smooth approximation in the bounded critical algebra

We mollify a compactly supported representative by normalized nonnegative
bumps.  Positivity preserves the `L∞` bound, Young's inequality preserves
the `L²` norm, and commutation with translations preserves the homogeneous
half-order Gagliardo energy.
-/

open Filter MeasureTheory Set
open scoped Convolution ENNReal SchwartzMap Topology Pointwise

noncomputable section
namespace CubicNLSPhaseRetrieval

/-- A normalized bump whose outer radius is `1/(n+1)`. -/
def criticalBump (n : ℕ) : ContDiffBump (0 : ℝ) := by
  let r : ℝ := 1 / (n + 1 : ℝ)
  refine ⟨r / 2, r, ?_, ?_⟩
  · dsimp [r]
    positivity
  · exact half_lt_self (by dsimp [r]; positivity)

lemma criticalBump_rOut (n : ℕ) :
    (criticalBump n).rOut = 1 / (n + 1 : ℝ) := rfl

lemma criticalBump_rIn (n : ℕ) :
    (criticalBump n).rIn = (1 / (n + 1 : ℝ)) / 2 := rfl

lemma criticalBump_rOut_tendsto :
    Tendsto (fun n : ℕ => (criticalBump n).rOut) atTop (nhds 0) := by
  simpa [criticalBump_rOut] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma criticalBump_ratio : ∀ n : ℕ,
    (criticalBump n).rOut ≤ 2 * (criticalBump n).rIn := by
  intro n
  rw [criticalBump_rOut, criticalBump_rIn]
  ring_nf
  exact le_rfl

/-- The complex-valued normalized kernel. -/
def criticalKernel (n : ℕ) (x : ℝ) : ℂ :=
  ((criticalBump n).normed volume x : ℝ)

lemma criticalKernel_continuous (n : ℕ) :
    Continuous (criticalKernel n) := by
  exact Complex.continuous_ofReal.comp (criticalBump n).continuous_normed

lemma criticalKernel_measurable (n : ℕ) :
    Measurable (criticalKernel n) := (criticalKernel_continuous n).measurable

lemma criticalKernel_hasCompactSupport (n : ℕ) :
    HasCompactSupport (criticalKernel n) := by
  exact (criticalBump n).hasCompactSupport_normed.comp_left
    (g := fun x : ℝ => (x : ℂ)) rfl

lemma criticalKernel_integrable (n : ℕ) :
    Integrable (criticalKernel n) :=
  (criticalKernel_continuous n).integrable_of_hasCompactSupport
    (criticalKernel_hasCompactSupport n)

lemma criticalKernel_norm (n : ℕ) (x : ℝ) :
    ‖criticalKernel n x‖ = (criticalBump n).normed volume x := by
  rw [criticalKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((criticalBump n).nonneg_normed x)]

lemma criticalKernel_eLpNorm_one (n : ℕ) :
    eLpNorm (criticalKernel n) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hint := (criticalBump n).integral_normed (μ := volume)
  calc
    (∫⁻ x : ℝ, ‖criticalKernel n x‖ₑ) =
        ∫⁻ x : ℝ, ENNReal.ofReal ((criticalBump n).normed volume x) := by
      apply lintegral_congr
      intro x
      rw [← ofReal_norm, criticalKernel_norm]
    _ = ENNReal.ofReal (∫ x : ℝ, (criticalBump n).normed volume x) := by
      exact (ofReal_integral_eq_lintegral_ofReal
        (criticalBump n).integrable_normed
        (Filter.Eventually.of_forall (criticalBump n).nonneg_normed)).symm
    _ = 1 := by rw [hint]; norm_num
  /-
  rw [show (∫⁻ x : ℝ, ENNReal.ofReal ((criticalBump n).normed volume x)) =
      ENNReal.ofReal (∫ x : ℝ, (criticalBump n).normed volume x) by
    exact (ofReal_integral_eq_lintegral_ofReal
      (criticalBump n).integrable_normed
      (Filter.Eventually.of_forall (criticalBump n).nonneg_normed)).symm]
  rw [hint]
  norm_num
  -/

/-- Physical mollification by the normalized bump. -/
def criticalMollify (n : ℕ) (A : ℝ → ℂ) : ℝ → ℂ :=
  criticalKernel n ⋆[complexMulCLM, volume] A

private def criticalMollifyReal (n : ℕ) (A : ℝ → ℂ) : ℝ → ℂ :=
  (criticalBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A

lemma criticalMollify_eq_real (n : ℕ) (A : ℝ → ℂ) :
    criticalMollify n A = criticalMollifyReal n A := by
  funext x
  unfold criticalMollify criticalMollifyReal
  apply integral_congr_ae
  filter_upwards with y
  simp only [criticalKernel, complexMulCLM, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rfl

lemma criticalMollify_contDiff (n : ℕ) (A : ℝ → ℂ)
    (hA : LocallyIntegrable A volume) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (criticalMollify n A) := by
  rw [criticalMollify_eq_real]
  exact (criticalBump n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (criticalBump n).contDiff_normed hA

lemma criticalMollify_hasCompactSupport (n : ℕ) (A : ℝ → ℂ)
    (hA : HasCompactSupport A) :
    HasCompactSupport (criticalMollify n A) :=
  (criticalKernel_hasCompactSupport n).convolution complexMulCLM hA

def criticalMollify_toSchwartz (n : ℕ) (A : ℝ → ℂ)
    (hA : LocallyIntegrable A volume) (hAc : HasCompactSupport A) :
    SchwartzMap ℝ ℂ :=
  (criticalMollify_hasCompactSupport n A hAc).toSchwartzMap
    (criticalMollify_contDiff n A hA)

@[simp] lemma criticalMollify_toSchwartz_apply (n : ℕ) (A : ℝ → ℂ)
    (hA : LocallyIntegrable A volume) (hAc : HasCompactSupport A) (x : ℝ) :
    criticalMollify_toSchwartz n A hA hAc x = criticalMollify n A x := by
  rfl

lemma criticalMollify_tendsto_ae (A : ℝ → ℂ)
    (hA : LocallyIntegrable A volume) :
    ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => criticalMollify n A x) atTop (nhds (A x)) := by
  have hreal := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) criticalBump_rOut_tendsto
    (Filter.Eventually.of_forall criticalBump_ratio) hA
  filter_upwards [hreal] with x hx
  apply hx.congr'
  filter_upwards with n
  rw [criticalMollify_eq_real]
  rfl

/-- The mollification bundled in the canonical physical `L²` space. -/
def criticalMollifyL2 (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) : FourierL2 :=
  (convolution_mul_memLp_two (criticalKernel n) A
    (criticalKernel_measurable n) hAm (criticalKernel_integrable n) hA2).toLp
      (criticalMollify n A)

lemma criticalMollifyL2_coe (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) :
    (criticalMollifyL2 n A hAm hA2 : ℝ → ℂ) =ᵐ[volume]
      criticalMollify n A :=
  MemLp.coeFn_toLp _

lemma criticalMollifyL2_norm_le (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) :
    ‖criticalMollifyL2 n A hAm hA2‖ ≤ ‖hA2.toLp A‖ := by
  have h := norm_convolution_mul_toLp_le (criticalKernel n) A
    (criticalKernel_measurable n) hAm (criticalKernel_integrable n) hA2
  have hkNorm : ‖(memLp_one_iff_integrable.mpr (criticalKernel_integrable n)).toLp
      (criticalKernel n)‖ = 1 := by
    rw [Lp.norm_toLp, criticalKernel_eLpNorm_one]
    norm_num
  simpa [criticalMollifyL2, criticalMollify, hkNorm] using h

private lemma criticalMollify_translate_sub (n : ℕ) (A : ℝ → ℂ)
    (hA : LocallyIntegrable A volume) (h x : ℝ) :
    criticalMollify n A (x + h) - criticalMollify n A x =
      criticalMollify n (fun z => A (z + h) - A z) x := by
  have hex := (criticalKernel_hasCompactSupport n).convolutionExists_left
    complexMulCLM (criticalKernel_continuous n) hA
  unfold criticalMollify convolution
  rw [← integral_sub (hex (x + h)) (hex x)]
  apply integral_congr_ae
  filter_upwards with y
  convert (map_sub (complexMulCLM (criticalKernel n y))
    (A (x + h - y)) (A (x - y))).symm using 1 <;> ring

private lemma measurable_translate_sub (A : ℝ → ℂ) (h : ℝ)
    (hA : Measurable A) : Measurable (fun x => A (x + h) - A x) :=
  (hA.comp (measurable_id.add measurable_const)).sub hA

private lemma memLp_translate_sub (A : ℝ → ℂ) (h : ℝ)
    (hA : MemLp A 2 volume) : MemLp (fun x => A (x + h) - A x) 2 volume := by
  exact (hA.comp_measurePreserving
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h)).sub hA

lemma criticalMollifyL2_translate_sub (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) (h : ℝ) :
    translateL2 h (criticalMollifyL2 n A hAm hA2) -
        criticalMollifyL2 n A hAm hA2 =
      criticalMollifyL2 n (fun x => A (x + h) - A x)
        (measurable_translate_sub A h hAm) (memLp_translate_sub A h hA2) := by
  apply Lp.ext
  filter_upwards [coe_translateL2 h (criticalMollifyL2 n A hAm hA2),
    criticalMollifyL2_coe n A hAm hA2,
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae
      (criticalMollifyL2_coe n A hAm hA2),
    Lp.coeFn_sub (translateL2 h (criticalMollifyL2 n A hAm hA2))
      (criticalMollifyL2 n A hAm hA2),
    criticalMollifyL2_coe n (fun x => A (x + h) - A x)
      (measurable_translate_sub A h hAm) (memLp_translate_sub A h hA2)]
      with x htrans hmoll hmollShift hsub hout
  rw [hsub, Pi.sub_apply, htrans, hmollShift, hmoll, hout]
  exact criticalMollify_translate_sub n A (hA2.locallyIntegrable (by norm_num)) h x

/-- Mollification does not increase any physical translation difference. -/
lemma norm_criticalMollifyL2_translate_sub_le (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) (h : ℝ) :
    ‖translateL2 h (criticalMollifyL2 n A hAm hA2) -
        criticalMollifyL2 n A hAm hA2‖ ≤
      ‖(memLp_translate_sub A h hA2).toLp (fun x => A (x + h) - A x)‖ := by
  rw [criticalMollifyL2_translate_sub]
  exact criticalMollifyL2_norm_le n (fun x => A (x + h) - A x)
    (measurable_translate_sub A h hAm) (memLp_translate_sub A h hA2)

private lemma memLp_translate_sub_toLp_eq (A : ℝ → ℂ) (h : ℝ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) :
    (memLp_translate_sub A h hA2).toLp (fun x => A (x + h) - A x) =
      translateL2 h (hA2.toLp A) - hA2.toLp A := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_translate_sub A h hA2),
    coe_translateL2 h (hA2.toLp A), MemLp.coeFn_toLp hA2,
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae
      (MemLp.coeFn_toLp hA2),
    Lp.coeFn_sub (translateL2 h (hA2.toLp A)) (hA2.toLp A)]
      with x hout htrans hA hAshift hsub
  rw [hout, hsub, Pi.sub_apply, htrans, hAshift, hA]

lemma enorm_criticalMollifyL2_translate_sub_le (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) (h : ℝ) :
    ‖translateL2 h (criticalMollifyL2 n A hAm hA2) -
        criticalMollifyL2 n A hAm hA2‖ₑ ≤
      ‖translateL2 h (hA2.toLp A) - hA2.toLp A‖ₑ := by
  have hnorm := norm_criticalMollifyL2_translate_sub_le n A hAm hA2 h
  rw [memLp_translate_sub_toLp_eq A h hAm hA2] at hnorm
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm

/-- The normalized mollifier is a contraction for the homogeneous
`H^{1/2}` translation energy. -/
theorem translationEnergy_criticalMollifyL2_le (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) :
    translationEnergy (criticalMollifyL2 n A hAm hA2) ≤
      translationEnergy (hA2.toLp A) := by
  unfold translationEnergy
  apply lintegral_mono
  intro h
  exact ENNReal.div_le_div_right
    (pow_le_pow_left'
      (enorm_criticalMollifyL2_translate_sub_le n A hAm hA2 h) 2) _

lemma homogeneousFourierEnergy_criticalMollifyL2_le (n : ℕ) (A : ℝ → ℂ)
    (hAm : Measurable A) (hA2 : MemLp A 2 volume) :
    homogeneousFourierEnergy (1 / 2 : ℝ)
        (criticalMollifyL2 n A hAm hA2) ≤
      homogeneousFourierEnergy (1 / 2 : ℝ) (hA2.toLp A) := by
  rw [← ENNReal.mul_le_mul_iff_right halfKernelConstant_pos.ne'
    halfKernelConstant_lt_top.ne]
  simpa only [translationEnergy_eq_fourier] using
    translationEnergy_criticalMollifyL2_le n A hAm hA2

private lemma representative_toLp_eq (f : Hs (1 / 2 : ℝ)) (A : ℝ → ℂ)
    (hA2 : MemLp A 2 volume)
    (hrep : A =ᵐ[volume] (Hs.toL2 (by norm_num) f : ℝ → ℂ)) :
    hA2.toLp A = Hs.toL2 (by norm_num) f := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp hA2, hrep] with x hA hx
  rw [hA, hx]

/-- A compactly represented critical function has mollifications in
`H^{1/2}` with one uniform quantitative bound. -/
theorem criticalMollifyHs_exists (f : Hs (1 / 2 : ℝ)) (A : ℝ → ℂ)
    (hAm : Measurable A)
    (hrep : A =ᵐ[volume] (Hs.toL2 (by norm_num) f : ℝ → ℂ)) :
    ∀ n : ℕ, ∃ p : Hs (1 / 2 : ℝ),
      Hs.toL2 (by norm_num) p =
        criticalMollifyL2 n A hAm
          ((memLp_congr_ae hrep).2 (Lp.memLp (Hs.toL2 (by norm_num) f))) ∧
      ‖p‖ₑ ^ (2 : ℕ) ≤
        ‖Hs.toL2 (by norm_num) f‖ₑ ^ (2 : ℕ) +
          homogeneousFourierEnergy (1 / 2 : ℝ)
            (Hs.toL2 (by norm_num) f) := by
  intro n
  let hA2 : MemLp A 2 volume :=
    (memLp_congr_ae hrep).2 (Lp.memLp (Hs.toL2 (by norm_num) f))
  have hto : hA2.toLp A = Hs.toL2 (by norm_num) f :=
    representative_toLp_eq f A hA2 hrep
  have hhomLe : homogeneousFourierEnergy (1 / 2 : ℝ)
      (criticalMollifyL2 n A hAm hA2) ≤
        homogeneousFourierEnergy (1 / 2 : ℝ)
          (Hs.toL2 (by norm_num) f) := by
    rw [← hto]
    exact homogeneousFourierEnergy_criticalMollifyL2_le n A hAm hA2
  have hhomTop : homogeneousFourierEnergy (1 / 2 : ℝ)
      (criticalMollifyL2 n A hAm hA2) < ⊤ :=
    hhomLe.trans_lt (homogeneousFourierEnergy_Hs_toL2_lt_top f)
  obtain ⟨p, hp⟩ := exists_Hs_half_of_homogeneousFourierEnergy_lt_top
    (criticalMollifyL2 n A hAm hA2) hhomTop
  refine ⟨p, hp, ?_⟩
  have hmassNorm := criticalMollifyL2_norm_le n A hAm hA2
  rw [hto] at hmassNorm
  have hmass : ‖criticalMollifyL2 n A hAm hA2‖ₑ ≤
      ‖Hs.toL2 (by norm_num) f‖ₑ := by
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hmassNorm
  exact (enorm_Hs_half_sq_le_mass_add_homogeneous p).trans <| by
    rw [hp]
    exact add_le_add (pow_le_pow_left' hmass 2) hhomLe

lemma integral_norm_criticalKernel (n : ℕ) :
    (∫ x : ℝ, ‖criticalKernel n x‖) = 1 := by
  simp_rw [criticalKernel_norm]
  exact (criticalBump n).integral_normed

lemma norm_criticalMollify_le (n : ℕ) (A : ℝ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ x, ‖A x‖ ≤ M) (x : ℝ) :
    ‖criticalMollify n A x‖ ≤ M := by
  unfold criticalMollify convolution
  have hg : Integrable (fun y : ℝ => M * ‖criticalKernel n y‖) volume :=
    (criticalKernel_integrable n).norm.const_mul M
  calc
    ‖∫ y : ℝ, complexMulCLM (criticalKernel n y) (A (x - y))‖ ≤
        ∫ y : ℝ, M * ‖criticalKernel n y‖ := by
      apply norm_integral_le_of_norm_le hg
      filter_upwards with y
      rw [show ‖complexMulCLM (criticalKernel n y) (A (x - y))‖ =
          ‖criticalKernel n y‖ * ‖A (x - y)‖ by simp [complexMulCLM]]
      calc
        ‖criticalKernel n y‖ * ‖A (x - y)‖ ≤
            ‖criticalKernel n y‖ * M :=
          mul_le_mul_of_nonneg_left (hbound (x - y)) (norm_nonneg _)
        _ = M * ‖criticalKernel n y‖ := mul_comm _ _
    _ = M := by
      rw [integral_const_mul, integral_norm_criticalKernel, mul_one]

lemma criticalKernel_support_subset_closedBall (n : ℕ) :
    Function.support (criticalKernel n) ⊆ Metric.closedBall (0 : ℝ) 1 := by
  intro x hx
  have hxreal : (criticalBump n).normed volume x ≠ 0 := by
    intro hz
    apply hx
    simp [criticalKernel, hz]
  have hxball : x ∈ Metric.ball (0 : ℝ) (criticalBump n).rOut := by
    rw [← (criticalBump n).support_normed_eq (μ := volume)]
    exact hxreal
  have hr : (criticalBump n).rOut ≤ 1 := by
    rw [criticalBump_rOut]
    exact (div_le_one (by positivity : 0 < (n + 1 : ℝ))).2 (by norm_num)
  exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr) hxball

lemma criticalMollify_support_subset (n : ℕ) (A : ℝ → ℂ) :
    Function.support (criticalMollify n A) ⊆
      Metric.closedBall (0 : ℝ) 1 + tsupport A := by
  exact (support_convolution_subset complexMulCLM).trans
    (add_subset_add (criticalKernel_support_subset_closedBall n) (subset_tsupport A))

private lemma self_mem_kernel_add_tsupport {A : ℝ → ℂ} {x : ℝ}
    (hx : A x ≠ 0) : x ∈ Metric.closedBall (0 : ℝ) 1 + tsupport A := by
  rw [Set.mem_add]
  exact ⟨0, by simp, x, subset_tsupport A hx, zero_add x⟩

/-- For a compact, pointwise bounded representative, the normalized
mollifications converge strongly in physical `L²`. -/
theorem criticalMollifyL2_tendsto (f : Hs (1 / 2 : ℝ)) (A : ℝ → ℂ)
    (hAm : Measurable A) (hAc : HasCompactSupport A)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, ‖A x‖ ≤ M)
    (hrep : A =ᵐ[volume] (Hs.toL2 (by norm_num) f : ℝ → ℂ)) :
    Tendsto (fun n => criticalMollifyL2 n A hAm
        ((memLp_congr_ae hrep).2 (Lp.memLp (Hs.toL2 (by norm_num) f))))
      atTop (nhds (Hs.toL2 (by norm_num) f)) := by
  let K : Set ℝ := Metric.closedBall (0 : ℝ) 1 + tsupport A
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) 1).add hAc.isCompact
  have hKmeas : MeasurableSet K := hK.measurableSet
  let hA2 : MemLp A 2 volume :=
    (memLp_congr_ae hrep).2 (Lp.memLp (Hs.toL2 (by norm_num) f))
  have hto : hA2.toLp A = Hs.toL2 (by norm_num) f :=
    representative_toLp_eq f A hA2 hrep
  let F : ℕ → ℝ → ℝ := fun n x => ‖criticalMollify n A x - A x‖ ^ 2
  let B : ℝ → ℝ := K.indicator (fun _ => (2 * M) ^ 2)
  have hBint : Integrable B volume := by
    change Integrable (K.indicator (fun _ : ℝ => (2 * M) ^ 2)) volume
    rw [integrable_indicator_iff hKmeas]
    exact integrableOn_const hK.measure_lt_top.ne
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    exact (((criticalMollify_contDiff n A
      (hA2.locallyIntegrable (by norm_num))).continuous.measurable.sub hAm).norm.pow_const 2)
      |>.aestronglyMeasurable
  have hFB (n : ℕ) : ∀ᵐ x : ℝ ∂volume, ‖F n x‖ ≤ B x := by
    filter_upwards with x
    by_cases hxK : x ∈ K
    · change ‖F n x‖ ≤ K.indicator (fun _ : ℝ => (2 * M) ^ 2) x
      rw [Set.indicator_of_mem hxK, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _)]
      have hmoll := norm_criticalMollify_le n A M hM hbound x
      have hdiff : ‖criticalMollify n A x - A x‖ ≤ 2 * M := by
        calc
          _ ≤ ‖criticalMollify n A x‖ + ‖A x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add hmoll (hbound x)
          _ = 2 * M := by ring
      nlinarith [norm_nonneg (criticalMollify n A x - A x),
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM]
    · have hAzero : A x = 0 := by
        by_contra hx
        exact hxK (self_mem_kernel_add_tsupport hx)
      have hmollzero : criticalMollify n A x = 0 := by
        by_contra hx
        exact hxK (criticalMollify_support_subset n A hx)
      change ‖F n x‖ ≤ K.indicator (fun _ : ℝ => (2 * M) ^ 2) x
      simp [hxK, F, hAzero, hmollzero]
  have hFlim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => F n x) atTop (nhds 0) := by
    filter_upwards [criticalMollify_tendsto_ae A
      (hA2.locallyIntegrable (by norm_num))] with x hx
    have hs := hx.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A x) atTop (nhds (A x)))
    have hn := hs.norm
    have hp := hn.pow 2
    simpa [F] using hp
  have hint : Tendsto (fun n => ∫ x, F n x) atTop (nhds 0) := by
    simpa using tendsto_integral_of_dominated_convergence B hFmeas hBint hFB hFlim
  have hFint (n : ℕ) : Integrable (F n) volume :=
    hBint.mono' (hFmeas n) (hFB n)
  have heLp : Tendsto (fun n => eLpNorm
      (fun x => criticalMollify n A x - A x) 2 volume) atTop (nhds 0) := by
    have hrewrite (n : ℕ) : eLpNorm
        (fun x => criticalMollify n A x - A x) 2 volume =
        ENNReal.ofReal (∫ x, F n x) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      norm_num only [ENNReal.toReal_ofNat]
      congr 1
      rw [ofReal_integral_eq_lintegral_ofReal]
      · apply lintegral_congr
        intro x
        change ‖criticalMollify n A x - A x‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal (‖criticalMollify n A x - A x‖ ^ 2)
        rw [ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm]
        norm_num [ENNReal.rpow_two]
      · exact hFint n
      · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
    simp_rw [hrewrite]
    have hof := ENNReal.tendsto_ofReal hint
    have hrp := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hof
    simpa [Function.comp_def] using hrp
  have ht : Tendsto (fun n => criticalMollifyL2 n A hAm hA2)
      atTop (nhds (hA2.toLp A)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm
      (fun n => criticalMollifyL2 n A hAm hA2) A hA2).2
    apply heLp.congr'
    filter_upwards with n
    apply eLpNorm_congr_ae
    exact ((criticalMollifyL2_coe n A hAm hA2).sub
      (Filter.Eventually.of_forall fun _ => rfl)).symm
  simpa only [hto] using ht

end CubicNLSPhaseRetrieval
