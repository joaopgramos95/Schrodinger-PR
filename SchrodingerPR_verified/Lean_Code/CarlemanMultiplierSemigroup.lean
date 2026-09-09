import Lean_Code.CarlemanVectorODE
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Contractive multiplication semigroups on the pair-coordinate `L²` space. -/

open Filter Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

private lemma l2FrequencyProduct_memLp
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    MemLp (fun ξ => m ξ * (f : ℝ × ℝ → ℂ) ξ) 2
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun ξ => m ξ * (f : ℝ × ℝ → ℂ) ξ) (volume.prod volume) :=
    hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  apply MemLp.of_le_mul (Lp.memLp f) hmeas
  filter_upwards with ξ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

def l2FrequencyMultiplier
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) : SpatialL2Two :=
  MemLp.toLp (fun ξ => m ξ * (f : ℝ × ℝ → ℂ) ξ)
    (l2FrequencyProduct_memLp m hm C hC f)

theorem coe_l2FrequencyMultiplier
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    (l2FrequencyMultiplier m hm C hC f : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun ξ => m ξ * (f : ℝ × ℝ → ℂ) ξ :=
  MemLp.coeFn_toLp _

private lemma l2FrequencyMultiplier_add
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f g : SpatialL2Two) :
    l2FrequencyMultiplier m hm C hC (f + g) =
      l2FrequencyMultiplier m hm C hC f + l2FrequencyMultiplier m hm C hC g := by
  apply Lp.ext
  filter_upwards [coe_l2FrequencyMultiplier m hm C hC (f + g),
    coe_l2FrequencyMultiplier m hm C hC f,
    coe_l2FrequencyMultiplier m hm C hC g, Lp.coeFn_add f g,
    Lp.coeFn_add (l2FrequencyMultiplier m hm C hC f)
      (l2FrequencyMultiplier m hm C hC g)] with ξ hfg hf hg hadd hout
  rw [hfg, hadd, hout]
  simp only [Pi.add_apply]
  rw [hf, hg]
  ring

private lemma l2FrequencyMultiplier_smul
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (c : ℂ) (f : SpatialL2Two) :
    l2FrequencyMultiplier m hm C hC (c • f) =
      c • l2FrequencyMultiplier m hm C hC f := by
  apply Lp.ext
  filter_upwards [coe_l2FrequencyMultiplier m hm C hC (c • f),
    coe_l2FrequencyMultiplier m hm C hC f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (l2FrequencyMultiplier m hm C hC f)]
      with ξ hcf hf hsmul hout
  rw [hcf, hsmul, hout]
  simp only [Pi.smul_apply]
  rw [hf]
  ring

theorem norm_l2FrequencyMultiplier_le
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    ‖l2FrequencyMultiplier m hm C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_l2FrequencyMultiplier m hm C hC f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

def l2FrequencyMultiplierCLM
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    SpatialL2Two →L[ℂ] SpatialL2Two :=
  let L : SpatialL2Two →ₗ[ℂ] SpatialL2Two :=
    { toFun := l2FrequencyMultiplier m hm C hC
      map_add' := l2FrequencyMultiplier_add m hm C hC
      map_smul' := l2FrequencyMultiplier_smul m hm C hC }
  L.mkContinuous C (norm_l2FrequencyMultiplier_le m hm C hC0 hC)

@[simp] theorem l2FrequencyMultiplierCLM_apply
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    l2FrequencyMultiplierCLM m hm C hC0 hC f =
      l2FrequencyMultiplier m hm C hC f := rfl

private lemma expMultiplier_bound
    (m : ℝ × ℝ → ℂ) (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ) (ξ : ℝ × ℝ) :
    ‖Complex.exp (m ξ * (τ : ℂ))‖ ≤ Real.exp (C * |τ|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (m ξ * (τ : ℂ)).re ≤ ‖m ξ * (τ : ℂ)‖ := Complex.re_le_norm _
    _ = ‖m ξ‖ * |τ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C * |τ| := mul_le_mul_of_nonneg_right (hC ξ) (abs_nonneg τ)

def l2ExpMultiplier
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ) :
    SpatialL2Two →L[ℂ] SpatialL2Two :=
  l2FrequencyMultiplierCLM (fun ξ => Complex.exp (m ξ * (τ : ℂ)))
    (by fun_prop) (Real.exp (C * |τ|)) (Real.exp_pos _).le
    (expMultiplier_bound m C hC τ)

theorem coe_l2ExpMultiplier
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ) (f : SpatialL2Two) :
    (l2ExpMultiplier m hm C hC0 hC τ f : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun ξ => Complex.exp (m ξ * (τ : ℂ)) * (f : ℝ × ℝ → ℂ) ξ :=
  coe_l2FrequencyMultiplier
    (fun ξ => Complex.exp (m ξ * (τ : ℂ))) (by fun_prop)
    (Real.exp (C * |τ|)) (expMultiplier_bound m C hC τ) f

theorem l2ExpMultiplier_zero
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    l2ExpMultiplier m hm C hC0 hC 0 = ContinuousLinearMap.id ℂ SpatialL2Two := by
  ext f
  filter_upwards [coe_l2ExpMultiplier m hm C hC0 hC 0 f] with ξ hξ
  rw [hξ]
  simp

theorem l2ExpMultiplier_norm_le_one
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ)
    (hdamp : ∀ ξ, (m ξ).re * τ ≤ 0) (f : SpatialL2Two) :
    ‖l2ExpMultiplier m hm C hC0 hC τ f‖ ≤ ‖f‖ := by
  calc
    ‖l2ExpMultiplier m hm C hC0 hC τ f‖ ≤ 1 * ‖f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [coe_l2ExpMultiplier m hm C hC0 hC τ f] with ξ hξ
      rw [hξ, norm_mul, Complex.norm_exp]
      have hre : (m ξ * (τ : ℂ)).re = (m ξ).re * τ := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (hdamp ξ)) (norm_nonneg _)
    _ = ‖f‖ := one_mul _

private theorem l2ExpMultiplier_remainder_bound
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (r τ : ℝ)
    (hsmall : C * |r - τ| ≤ 1) :
    ‖l2ExpMultiplier m hm C hC0 hC r -
        l2ExpMultiplier m hm C hC0 hC τ -
        (r - τ) • ((l2FrequencyMultiplierCLM m hm C hC0 hC).comp
          (l2ExpMultiplier m hm C hC0 hC τ))‖ ≤
      (Real.exp (C * |τ|) * C ^ 2 * |r - τ| ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖l2ExpMultiplier m hm C hC0 hC r f -
      l2ExpMultiplier m hm C hC0 hC τ f -
      (r - τ) • l2FrequencyMultiplierCLM m hm C hC0 hC
        (l2ExpMultiplier m hm C hC0 hC τ f)‖ ≤ _
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
      Lp.coeFn_sub
        (l2ExpMultiplier m hm C hC0 hC r f -
          l2ExpMultiplier m hm C hC0 hC τ f)
        ((r - τ) • l2FrequencyMultiplierCLM m hm C hC0 hC
          (l2ExpMultiplier m hm C hC0 hC τ f)),
      Lp.coeFn_sub (l2ExpMultiplier m hm C hC0 hC r f)
        (l2ExpMultiplier m hm C hC0 hC τ f),
      Lp.coeFn_smul (r - τ)
        (l2FrequencyMultiplierCLM m hm C hC0 hC
          (l2ExpMultiplier m hm C hC0 hC τ f)),
      coe_l2ExpMultiplier m hm C hC0 hC r f,
      coe_l2ExpMultiplier m hm C hC0 hC τ f,
      coe_l2FrequencyMultiplier m hm C hC
        (l2ExpMultiplier m hm C hC0 hC τ f)]
      with ξ hout hsub hsmul hr hτ hA
  rw [hout]
  simp only [Pi.sub_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, l2FrequencyMultiplierCLM_apply]
  rw [hr, hτ, hA, hτ]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_eq_mul]
  have hexp :
      Complex.exp (m ξ * (r : ℂ)) =
        Complex.exp (m ξ * (τ : ℂ)) *
          Complex.exp (m ξ * ((r - τ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfactor :
      Complex.exp (m ξ * (r : ℂ)) * (f : ℝ × ℝ → ℂ) ξ -
          Complex.exp (m ξ * (τ : ℂ)) * (f : ℝ × ℝ → ℂ) ξ -
          ((r - τ : ℝ) : ℂ) *
            (m ξ * (Complex.exp (m ξ * (τ : ℂ)) *
              (f : ℝ × ℝ → ℂ) ξ)) =
        Complex.exp (m ξ * (τ : ℂ)) *
          (Complex.exp (m ξ * ((r - τ : ℝ) : ℂ)) - 1 -
            m ξ * ((r - τ : ℝ) : ℂ)) *
          (f : ℝ × ℝ → ℂ) ξ := by
    rw [hexp]
    ring
  change ‖Complex.exp (m ξ * (r : ℂ)) * (f : ℝ × ℝ → ℂ) ξ -
      Complex.exp (m ξ * (τ : ℂ)) * (f : ℝ × ℝ → ℂ) ξ -
      ((r - τ : ℝ) : ℂ) *
        (m ξ * (Complex.exp (m ξ * (τ : ℂ)) *
          (f : ℝ × ℝ → ℂ) ξ))‖ ≤ _
  rw [hfactor]
  have hz : ‖m ξ * ((r - τ : ℝ) : ℂ)‖ ≤ C * |r - τ| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC ξ) (abs_nonneg _)
  have hrem :
      ‖Complex.exp (m ξ * ((r - τ : ℝ) : ℂ)) - 1 -
          m ξ * ((r - τ : ℝ) : ℂ)‖ ≤ (C * |r - τ|) ^ 2 := by
    exact (Complex.norm_exp_sub_one_sub_id_le (hz.trans hsmall)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hz 2)
  calc
    ‖Complex.exp (m ξ * (τ : ℂ)) *
        (Complex.exp (m ξ * ((r - τ : ℝ) : ℂ)) - 1 -
          m ξ * ((r - τ : ℝ) : ℂ)) *
        (f : ℝ × ℝ → ℂ) ξ‖ ≤
        (Real.exp (C * |τ|) * (C * |r - τ|) ^ 2) *
          ‖(f : ℝ × ℝ → ℂ) ξ‖ := by
      simp only [norm_mul]
      gcongr
      exact expMultiplier_bound m C hC τ ξ
    _ = (Real.exp (C * |τ|) * C ^ 2 * |r - τ| ^ 2) *
          ‖(f : ℝ × ℝ → ℂ) ξ‖ := by ring

/-- The bounded multiplication semigroup solves the operator ODE generated by
the corresponding multiplication operator. -/
theorem l2ExpMultiplier_hasDerivAt
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ) :
    HasDerivAt (fun r : ℝ => l2ExpMultiplier m hm C hC0 hC r)
      ((l2FrequencyMultiplierCLM m hm C hC0 hC).comp
        (l2ExpMultiplier m hm C hC0 hC τ)) τ := by
  rw [hasDerivAt_iff_tendsto]
  apply squeeze_zero'
    (by
      filter_upwards with r
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · filter_upwards [eventually_abs_sub_lt τ (show 0 < (C + 1)⁻¹ by positivity)] with r hr
    have hsmall : C * |r - τ| ≤ 1 := by
      have hC1 : C < C + 1 := lt_add_one C
      have hpos : 0 < C + 1 := lt_of_le_of_lt hC0 hC1
      have habs : |r - τ| < (C + 1)⁻¹ := hr
      exact le_of_lt <| calc
        C * |r - τ| ≤ (C + 1) * |r - τ| := by
          gcongr
        _ < (C + 1) * (C + 1)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    have hbound := l2ExpMultiplier_remainder_bound m hm C hC0 hC r τ hsmall
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  · have hconst :
        Tendsto (fun r : ℝ => Real.exp (C * |τ|) * C ^ 2 * |r - τ|)
          (𝓝 τ) (𝓝 0) := by
      have habs : Tendsto (fun r : ℝ => |r - τ|) (𝓝 τ) (𝓝 0) := by
        have hc : ContinuousAt (fun r : ℝ => |r - τ|) τ := by fun_prop
        simpa only [ContinuousAt, sub_self, abs_zero] using hc
      convert tendsto_const_nhds.mul habs using 1 <;> simp
    convert hconst using 1
    funext r
    by_cases hr : r = τ
    · simp [hr]
    · rw [Real.norm_eq_abs]
      have habs : |r - τ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hr)
      field_simp [habs]
      <;> ring

theorem l2ExpMultiplierReal_hasDerivAt
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        (l2ExpMultiplier m hm C hC0 hC r).restrictScalars ℝ)
      (((l2FrequencyMultiplierCLM m hm C hC0 hC).restrictScalars ℝ).comp
        ((l2ExpMultiplier m hm C hC0 hC τ).restrictScalars ℝ)) τ := by
  let R := ContinuousLinearMap.restrictScalarsL ℂ SpatialL2Two SpatialL2Two ℝ ℝ
  have h := R.hasFDerivAt.comp_hasDerivAt τ
    (l2ExpMultiplier_hasDerivAt m hm C hC0 hC τ)
  apply h.congr_deriv
  ext f
  rfl

theorem l2ExpMultiplier_commutes
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (τ : ℝ) :
    ((l2ExpMultiplier m hm C hC0 hC τ).restrictScalars ℝ).comp
        ((l2FrequencyMultiplierCLM m hm C hC0 hC).restrictScalars ℝ) =
      ((l2FrequencyMultiplierCLM m hm C hC0 hC).restrictScalars ℝ).comp
        ((l2ExpMultiplier m hm C hC0 hC τ).restrictScalars ℝ) := by
  ext f
  filter_upwards [
      coe_l2ExpMultiplier m hm C hC0 hC τ
        (l2FrequencyMultiplierCLM m hm C hC0 hC f),
      coe_l2FrequencyMultiplier m hm C hC f,
      coe_l2FrequencyMultiplier m hm C hC
        (l2ExpMultiplier m hm C hC0 hC τ f),
      coe_l2ExpMultiplier m hm C hC0 hC τ f]
      with ξ hSA hA hAS hS
  change
    (l2ExpMultiplier m hm C hC0 hC τ
      (l2FrequencyMultiplierCLM m hm C hC0 hC f) : ℝ × ℝ → ℂ) ξ =
    (l2FrequencyMultiplierCLM m hm C hC0 hC
      (l2ExpMultiplier m hm C hC0 hC τ f) : ℝ × ℝ → ℂ) ξ
  rw [hSA]
  simp only [l2FrequencyMultiplierCLM_apply]
  rw [hA, hAS, hS]
  ring

end CubicNLSPhaseRetrieval
