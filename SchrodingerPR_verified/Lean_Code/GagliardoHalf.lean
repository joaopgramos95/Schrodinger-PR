import Lean_Code.FourierSobolev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

def translationEnergy (f : FourierL2) : ℝ≥0∞ :=
  ∫⁻ h : ℝ, ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
    ENNReal.ofReal (|h| ^ (2 : ℕ))

lemma enorm_translate_sub_sq (h : ℝ) (f : FourierL2) :
    ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) =
      ∫⁻ ξ : ℝ, ‖translationPhase h ξ - 1‖ₑ ^ (2 : ℝ) *
        ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
  rw [← LinearIsometryEquiv.enorm_map sobolevFourier]
  rw [map_sub]
  have hcoe :
      ((sobolevFourier (translateL2 h f) - sobolevFourier f : FourierL2) :
          ℝ → ℂ) =ᵐ[volume]
        fun ξ => (translationPhase h ξ - 1) *
          (sobolevFourier f : ℝ → ℂ) ξ := by
    filter_upwards [coe_fourier_translateL2 h f,
      Lp.coeFn_sub (sobolevFourier (translateL2 h f)) (sobolevFourier f)]
      with ξ htrans hsub
    rw [hsub, Pi.sub_apply, htrans]
    ring
  rw [Lp.enorm_def, eLpNorm_congr_ae hcoe]
  rw [← ENNReal.rpow_natCast]
  calc
    eLpNorm (fun ξ => (translationPhase h ξ - 1) *
        (sobolevFourier f : ℝ → ℂ) ξ) 2 volume ^ (2 : ℝ) =
        ∫⁻ ξ, ‖(translationPhase h ξ - 1) *
          (sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral
        (f := fun ξ => (translationPhase h ξ - 1) *
          (sobolevFourier f : ℝ → ℂ) ξ) (μ := volume)
        (p := (2 : NNReal)) (by norm_num))
    _ = _ := by
      apply lintegral_congr
      intro ξ
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

def halfTranslationKernel (h ξ : ℝ) : ℝ≥0∞ :=
  ‖translationPhase h ξ - 1‖ₑ ^ (2 : ℝ) /
    ENNReal.ofReal (|h| ^ (2 : ℕ))

lemma translationEnergy_eq_iter (f : FourierL2) :
    translationEnergy f =
      ∫⁻ h : ℝ, ∫⁻ ξ : ℝ, halfTranslationKernel h ξ *
        ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
  unfold translationEnergy
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with h hh
  rw [enorm_translate_sub_sq]
  unfold halfTranslationKernel
  rw [ENNReal.div_eq_inv_mul]
  rw [← lintegral_const_mul' _ _ (by
    simp only [ne_eq, ENNReal.inv_eq_top]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (sq_pos_of_ne_zero (abs_ne_zero.mpr hh))))]
  apply lintegral_congr
  intro ξ
  rw [ENNReal.div_eq_inv_mul]
  ac_rfl

lemma halfTranslationKernel_measurable :
    Measurable (fun p : ℝ × ℝ => halfTranslationKernel p.1 p.2) := by
  unfold halfTranslationKernel translationPhase
  fun_prop

lemma translationEnergy_eq_swapped (f : FourierL2) :
    translationEnergy f =
      ∫⁻ ξ : ℝ, (∫⁻ h : ℝ, halfTranslationKernel h ξ) *
        ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
  rw [translationEnergy_eq_iter]
  let K : ℝ × ℝ → ℝ≥0∞ := fun p => halfTranslationKernel p.1 p.2 *
    ‖(sobolevFourier f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
  have hK : AEMeasurable K (volume.prod volume) :=
    halfTranslationKernel_measurable.aemeasurable.mul
      (((Lp.aestronglyMeasurable (sobolevFourier f)).enorm.pow_const (2 : ℝ)).comp_snd)
  rw [← lintegral_prod K hK]
  rw [lintegral_prod_symm K hK]
  apply lintegral_congr
  intro ξ
  exact lintegral_mul_const' _ _
    (ENNReal.rpow_ne_top_of_nonneg (x :=
      ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ) (y := (2 : ℝ))
      (by norm_num) enorm_ne_top)

lemma translationPhase_mul (h ξ : ℝ) :
    translationPhase h ξ = translationPhase (ξ * h) 1 := by
  unfold translationPhase
  congr 3
  push_cast
  ring

lemma halfTranslationKernel_scale (h ξ : ℝ) :
    halfTranslationKernel h ξ =
      ENNReal.ofReal (|ξ| ^ (2 : ℕ)) * halfTranslationKernel (ξ * h) 1 := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [halfTranslationKernel, translationPhase]
  by_cases hh : h = 0
  · subst h
    simp [halfTranslationKernel, translationPhase]
  rw [halfTranslationKernel, halfTranslationKernel, translationPhase_mul]
  have hξpos : 0 < |ξ| ^ (2 : ℕ) := sq_pos_of_ne_zero (abs_ne_zero.mpr hξ)
  have hhpos : 0 < |h| ^ (2 : ℕ) := sq_pos_of_ne_zero (abs_ne_zero.mpr hh)
  have hmul : |ξ * h| ^ (2 : ℕ) = |ξ| ^ (2 : ℕ) * |h| ^ (2 : ℕ) := by
    rw [abs_mul, mul_pow]
  rw [hmul, ENNReal.ofReal_mul hξpos.le]
  have hX0 : ENNReal.ofReal (|ξ| ^ (2 : ℕ)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hξpos)
  have hXtop : ENNReal.ofReal (|ξ| ^ (2 : ℕ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
  conv_rhs =>
    rw [show ENNReal.ofReal (|ξ| ^ (2 : ℕ)) *
        ((ENNReal.ofReal (|ξ| ^ (2 : ℕ)))⁻¹ *
          (ENNReal.ofReal (|h| ^ (2 : ℕ)))⁻¹ *
          ‖translationPhase (ξ * h) 1 - 1‖ₑ ^ (2 : ℝ)) =
        (ENNReal.ofReal (|ξ| ^ (2 : ℕ)) *
          (ENNReal.ofReal (|ξ| ^ (2 : ℕ)))⁻¹) *
          ((ENNReal.ofReal (|h| ^ (2 : ℕ)))⁻¹ *
            ‖translationPhase (ξ * h) 1 - 1‖ₑ ^ (2 : ℝ)) by ac_rfl]
  rw [ENNReal.mul_inv_cancel hX0 hXtop]
  simp
  all_goals aesop

def halfKernelConstant : ℝ≥0∞ :=
  ∫⁻ h : ℝ, halfTranslationKernel h 1

lemma integral_halfTranslationKernel (ξ : ℝ) :
    (∫⁻ h : ℝ, halfTranslationKernel h ξ) =
      ENNReal.ofReal |ξ| * halfKernelConstant := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [halfTranslationKernel, translationPhase]
  have hbase : Measurable (fun h : ℝ => halfTranslationKernel h 1) := by
    have hp : Measurable (fun h : ℝ => (h, (1 : ℝ))) :=
      measurable_id.prodMk measurable_const
    simpa [Function.comp_def] using halfTranslationKernel_measurable.comp hp
  have hchange := lintegral_map'
    (μ := volume) (f := fun h : ℝ => halfTranslationKernel h 1)
    (g := fun h : ℝ => ξ * h)
    (by
      rw [Real.map_volume_mul_left hξ]
      exact hbase.aemeasurable.smul_measure (ENNReal.ofReal |ξ⁻¹|))
    (by fun_prop : AEMeasurable (fun h : ℝ => ξ * h) volume)
  rw [Real.map_volume_mul_left hξ, lintegral_smul_measure] at hchange
  calc
    (∫⁻ h : ℝ, halfTranslationKernel h ξ) =
        ∫⁻ h : ℝ, ENNReal.ofReal (|ξ| ^ (2 : ℕ)) *
          halfTranslationKernel (ξ * h) 1 := by
      apply lintegral_congr
      intro h
      exact halfTranslationKernel_scale h ξ
    _ = ENNReal.ofReal (|ξ| ^ (2 : ℕ)) *
        ∫⁻ h : ℝ, halfTranslationKernel (ξ * h) 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (|ξ| ^ (2 : ℕ)) *
        (ENNReal.ofReal |ξ⁻¹| * halfKernelConstant) := by
      rw [← hchange]
      rfl
    _ = ENNReal.ofReal |ξ| * halfKernelConstant := by
      rw [← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_mul (sq_nonneg |ξ|)]
      congr 1
      rw [abs_inv]
      field_simp

theorem translationEnergy_eq_fourier (f : FourierL2) :
    translationEnergy f =
      halfKernelConstant * homogeneousFourierEnergy (1 / 2 : ℝ) f := by
  rw [translationEnergy_eq_swapped]
  simp_rw [integral_halfTranslationKernel]
  rw [homogeneousFourierEnergy]
  have hmeas : AEMeasurable (fun ξ : ℝ =>
      ENNReal.ofReal |ξ| * ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) volume :=
    (by fun_prop : Measurable fun ξ : ℝ => ENNReal.ofReal |ξ|).aemeasurable.mul
      ((Lp.aestronglyMeasurable (sobolevFourier f)).enorm.pow_const (2 : ℝ))
  calc
    (∫⁻ ξ : ℝ, (ENNReal.ofReal |ξ| * halfKernelConstant) *
        ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) =
        ∫⁻ ξ : ℝ, halfKernelConstant *
          (ENNReal.ofReal |ξ| *
            ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) := by
      apply lintegral_congr
      intro ξ
      ac_rfl
    _ = halfKernelConstant * ∫⁻ ξ : ℝ,
          ENNReal.ofReal |ξ| *
            ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) :=
      lintegral_const_mul'' halfKernelConstant hmeas
    _ = halfKernelConstant * ∫⁻ ξ : ℝ,
          ENNReal.ofReal (|ξ| ^ (2 * (1 / 2 : ℝ))) *
            ‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ ^ (2 : ℕ) := by
      congr 1
      apply lintegral_congr
      intro ξ
      norm_num [enorm_eq_nnnorm, ENNReal.rpow_two]

private lemma halfTranslationKernel_eq_ofReal (h : ℝ) :
    halfTranslationKernel h 1 =
      ENNReal.ofReal (‖translationPhase h 1 - 1‖ ^ 2 / |h| ^ 2) := by
  by_cases hh : h = 0
  · subst h
    simp [halfTranslationKernel, translationPhase]
  rw [halfTranslationKernel, ENNReal.rpow_two, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_div_of_pos]
  exact sq_pos_of_ne_zero (abs_ne_zero.mpr hh)

private lemma halfTranslationKernel_le_integrable_majorant (h : ℝ) :
    halfTranslationKernel h 1 ≤
      ENNReal.ofReal (8 * Real.pi ^ 2 * (1 + h ^ 2)⁻¹) := by
  rw [halfTranslationKernel_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hpi : 1 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hpi0 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  by_cases hh : h = 0
  · subst h
    simp [translationPhase, hpi0]
  have hh2 : 0 < |h| ^ 2 := sq_pos_of_ne_zero (abs_ne_zero.mpr hh)
  by_cases hsmall : |h| ≤ 1
  · have hosc := Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := h * (2 * Real.pi * 1))
    have hphase : translationPhase h 1 =
        Complex.exp (Complex.I * ((h * (2 * Real.pi * 1) : ℝ) : ℂ)) := rfl
    rw [← hphase] at hosc
    have hosc2 : ‖translationPhase h 1 - 1‖ ^ 2 ≤
        (2 * Real.pi * |h|) ^ 2 := by
      have hb : ‖translationPhase h 1 - 1‖ ≤ 2 * Real.pi * |h| := by
        simpa [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
          mul_assoc, mul_comm, mul_left_comm] using hosc
      nlinarith [norm_nonneg (translationPhase h 1 - 1),
        mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (abs_nonneg h)]
    rw [div_le_iff₀ hh2]
    have habs2 : |h| ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (abs_nonneg h) zero_le_one).2 hsmall
    have hone : 1 + h ^ 2 ≤ 2 := by
      rw [← sq_abs]
      linarith
    have hdenpos : 0 < 1 + h ^ 2 := by positivity
    have hrewrite :
        8 * Real.pi ^ 2 * (1 + h ^ 2)⁻¹ * |h| ^ 2 =
          (8 * Real.pi ^ 2 * |h| ^ 2) / (1 + h ^ 2) := by
      field_simp
    rw [hrewrite, le_div_iff₀ hdenpos]
    calc
      ‖translationPhase h 1 - 1‖ ^ 2 * (1 + h ^ 2) ≤
          (2 * Real.pi * |h|) ^ 2 * (1 + h ^ 2) := by gcongr
      _ ≤ (2 * Real.pi * |h|) ^ 2 * 2 := by gcongr
      _ = 8 * Real.pi ^ 2 * |h| ^ 2 := by ring
  · have hlarge : 1 ≤ |h| := le_of_not_ge hsmall
    have hsquare : 1 ≤ h ^ 2 := by
      rw [← sq_abs]
      simpa using (sq_le_sq₀ zero_le_one (abs_nonneg h)).2 hlarge
    have hosc : ‖translationPhase h 1 - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖translationPhase h 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_translationPhase]; norm_num
    have hosc2 : ‖translationPhase h 1 - 1‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (translationPhase h 1 - 1)]
    rw [div_le_iff₀ hh2]
    have hdenpos : 0 < 1 + h ^ 2 := by positivity
    have hrewrite :
        8 * Real.pi ^ 2 * (1 + h ^ 2)⁻¹ * |h| ^ 2 =
          (8 * Real.pi ^ 2 * |h| ^ 2) / (1 + h ^ 2) := by
      field_simp
    rw [hrewrite, le_div_iff₀ hdenpos]
    calc
      ‖translationPhase h 1 - 1‖ ^ 2 * (1 + h ^ 2) ≤
          4 * (1 + h ^ 2) := by gcongr
      _ ≤ 8 * Real.pi ^ 2 * |h| ^ 2 := by
        rw [sq_abs]
        nlinarith [sq_nonneg h]

lemma halfKernelConstant_lt_top : halfKernelConstant < ⊤ := by
  have hmajInt : Integrable
      (fun h : ℝ => 8 * Real.pi ^ 2 * (1 + h ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul (8 * Real.pi ^ 2)
  have hmajFin :
      (∫⁻ h : ℝ, ENNReal.ofReal
        (8 * Real.pi ^ 2 * (1 + h ^ 2)⁻¹) ∂volume) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmajInt]
    · exact ENNReal.ofReal_lt_top
    · filter_upwards with h
      positivity
  exact lt_of_le_of_lt
    (lintegral_mono halfTranslationKernel_le_integrable_majorant) hmajFin

private lemma halfTranslationKernel_ne_zero_of_Ioo (h : ℝ)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) : halfTranslationKernel h 1 ≠ 0 := by
  have hxpos : 0 < 2 * Real.pi * h := mul_pos Real.two_pi_pos hh.1
  have hxlt : 2 * Real.pi * h < 2 * Real.pi := by
    simpa using mul_lt_mul_of_pos_left hh.2 Real.two_pi_pos
  have hcos : Real.cos (2 * Real.pi * h) ≠ 1 := by
    rw [ne_eq, Real.cos_eq_one_iff_of_lt_of_lt]
    · nlinarith
    · nlinarith [Real.two_pi_pos]
    · exact hxlt
  have hexp : translationPhase h 1 ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [translationPhase] at hre
    have harg :
        Complex.I * (((h * (2 * Real.pi * 1) : ℝ) : ℂ)) =
          (((2 * Real.pi * h : ℝ) : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re] at hre
    norm_num at hre
    exact hcos hre
  rw [halfTranslationKernel_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
  exact div_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hexp)))
    (sq_pos_of_ne_zero (abs_ne_zero.mpr hh.1.ne'))

lemma halfKernelConstant_pos : 0 < halfKernelConstant := by
  have hmeas : Measurable (fun h : ℝ => halfTranslationKernel h 1) := by
    simpa [Function.comp_def] using halfTranslationKernel_measurable.comp
      (measurable_id.prodMk measurable_const)
  rw [halfKernelConstant, lintegral_pos_iff_support hmeas]
  calc
    0 < volume (Set.Ioo (0 : ℝ) 1) := by
      rw [Real.volume_Ioo]
      norm_num
    _ ≤ volume (Function.support fun h : ℝ => halfTranslationKernel h 1) := by
      apply measure_mono
      intro h hh
      exact halfTranslationKernel_ne_zero_of_Ioo h hh
