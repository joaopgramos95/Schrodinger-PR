import Lean_Code.CriticalZeroSafe
import Lean_Code.L1L2FourierBridge
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# `H¹` coefficients acting on bounded critical functions

The current at a bounded `H^{1/2}` slice is a continuous functional of an
`H¹` spatial coefficient.  This gives a separable coefficient space for the
common-null-set argument.
-/

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

def negativeOneWeight (ξ : ℝ) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

lemma continuous_negativeOneWeight : Continuous negativeOneWeight := by
  unfold negativeOneWeight
  have hb : Continuous (fun ξ : ℝ => 1 + ‖ξ‖ ^ 2) := by fun_prop
  exact Complex.continuous_ofReal.comp
    (hb.rpow_const (fun ξ => Or.inl (by positivity)))

lemma hasTemperateGrowth_negativeOneWeight :
    negativeOneWeight.HasTemperateGrowth := by
  unfold negativeOneWeight
  fun_prop

lemma norm_negativeOneWeight_le (ξ : ℝ) : ‖negativeOneWeight ξ‖ ≤ 1 := by
  unfold negativeOneWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by nlinarith [sq_nonneg ‖ξ‖]) (by norm_num)

lemma fourier_Hs_one_toL2 (f : Hs (1 : ℝ)) :
    sobolevFourier (Hs.toL2 (by norm_num) f) =
      boundedMulCLM negativeOneWeight continuous_negativeOneWeight 1
        (by norm_num) norm_negativeOneWeight_le (sobolevFourier f) := by
  have hinj : Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2 :
        FourierL2 →L[ℂ] TemperedDistribution ℝ ℂ) :=
    LinearMap.ker_eq_bot.mp (by
      simpa using
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := ℂ) (E := ℝ) (μ := volume) (p := (2 : ℝ≥0∞))))
  apply hinj
  change MeasureTheory.Lp.toTemperedDistribution
      (sobolevFourier (Hs.toL2 (by norm_num) f)) = _
  rw [sobolevFourier_eq_fourier]
  calc
    _ = 𝓕 (MeasureTheory.Lp.toTemperedDistribution
          (Hs.toL2 (by norm_num) f)) := by
      simpa [sobolevFourier] using
        (MeasureTheory.Lp.fourier_toTemperedDistribution_eq
          (Hs.toL2 (by norm_num) f)).symm
    _ = 𝓕 (Hs.toTempered (1 : ℝ) f) := by
      rw [Hs.toTempered_toL2 (s := (1 : ℝ)) (by norm_num) f]
    _ = TemperedDistribution.smulLeftCLM ℂ negativeOneWeight
          (MeasureTheory.Lp.toTemperedDistribution (sobolevFourier f)) := by
      rw [fourier_Hs_toTempered]
      congr 2
    _ = MeasureTheory.Lp.toTemperedDistribution
          (boundedMulCLM negativeOneWeight continuous_negativeOneWeight 1
            (by norm_num) norm_negativeOneWeight_le (sobolevFourier f)) :=
      (toTemperedDistribution_boundedMulCLM negativeOneWeight
        continuous_negativeOneWeight hasTemperateGrowth_negativeOneWeight 1
        (by norm_num) norm_negativeOneWeight_le (sobolevFourier f)).symm

/-- Continuous physical `L²` realization of `H¹`. -/
def hsOneToL2CLM : Hs (1 : ℝ) →L[ℂ] FourierL2 :=
  sobolevFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM negativeOneWeight continuous_negativeOneWeight 1
      (by norm_num) norm_negativeOneWeight_le).comp
        sobolevFourier.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] lemma hsOneToL2CLM_apply (f : Hs (1 : ℝ)) :
    hsOneToL2CLM f = Hs.toL2 (by norm_num) f := by
  apply sobolevFourier.injective
  rw [fourier_Hs_one_toL2]
  simp [hsOneToL2CLM]

lemma negativeOneWeight_memLp_two : MemLp negativeOneWeight 2 volume := by
  have hm : AEStronglyMeasurable negativeOneWeight volume :=
    continuous_negativeOneWeight.aestronglyMeasurable
  apply (memLp_norm_iff hm).mp
  apply (memLp_two_iff_integrable_sq
    continuous_negativeOneWeight.norm.aestronglyMeasurable).2
  have hi : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  exact hi.congr (Filter.Eventually.of_forall fun x => by
    change (1 + x ^ 2)⁻¹ = ‖negativeOneWeight x‖ ^ 2
    rw [negativeOneWeight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [show ‖x‖ ^ 2 = x ^ 2 by simp [Real.norm_eq_abs, sq_abs]]
    have hp : 0 < 1 + x ^ 2 := by positivity
    rw [← Real.rpow_natCast ((1 + x ^ 2) ^ (-(1 : ℝ) / 2)) 2,
      ← Real.rpow_mul hp.le]
    norm_num [Real.rpow_neg_one])

lemma negativeOneWeight_mul_memLp_one (f : Hs (1 : ℝ)) :
    MemLp (fun ξ => negativeOneWeight ξ *
      (sobolevFourier f : ℝ → ℂ) ξ) 1 volume := by
  let wf : Lp ℂ 2 volume := negativeOneWeight_memLp_two.toLp negativeOneWeight
  have hwf : (wf : ℝ → ℂ) =ᵐ[volume] negativeOneWeight :=
    negativeOneWeight_memLp_two.coeFn_toLp
  have hp : MemLp (fun ξ => (wf : ℝ → ℂ) ξ *
      (sobolevFourier f : ℝ → ℂ) ξ) 1 volume :=
    (Lp.memLp (sobolevFourier f)).mul' (Lp.memLp wf)
  exact (memLp_congr_ae (hwf.mono fun ξ hξ => by rw [hξ])).mpr hp

lemma negativeOneWeight_mul_memLp_two (f : Hs (1 : ℝ)) :
    MemLp (fun ξ => negativeOneWeight ξ *
      (sobolevFourier f : ℝ → ℂ) ξ) 2 volume := by
  let w : Lp ℂ ⊤ volume :=
    (memLp_top_of_bound continuous_negativeOneWeight.aestronglyMeasurable 1
      (Filter.Eventually.of_forall norm_negativeOneWeight_le)).toLp
      negativeOneWeight
  have hw : (w : ℝ → ℂ) =ᵐ[volume] negativeOneWeight := MemLp.coeFn_toLp _
  have hp : MemLp (fun ξ => (w : ℝ → ℂ) ξ *
      (sobolevFourier f : ℝ → ℂ) ξ) 2 volume :=
    (Lp.memLp (sobolevFourier f)).mul' (Lp.memLp w)
  exact (memLp_congr_ae (hw.mono fun ξ hξ => by rw [hξ])).mpr hp

/-- Every `H¹` function has an essentially bounded physical representative. -/
theorem Hs_one_eLpNorm_top_lt_top (f : Hs (1 : ℝ)) :
    eLpNorm (Hs.toL2 (by norm_num) f : ℝ → ℂ) ⊤ volume < ⊤ := by
  let b : ℝ → ℂ := fun ξ => negativeOneWeight ξ *
    (sobolevFourier f : ℝ → ℂ) ξ
  have hb1 : MemLp b 1 volume := negativeOneWeight_mul_memLp_one f
  have hb2 : MemLp b 2 volume := negativeOneWeight_mul_memLp_two f
  have hfreq : sobolevFourier (Hs.toL2 (by norm_num) f) = hb2.toLp b := by
    rw [fourier_Hs_one_toL2]
    apply Lp.ext
    filter_upwards [coe_boundedMulCLM negativeOneWeight
      continuous_negativeOneWeight 1 (by norm_num)
      norm_negativeOneWeight_le (sobolevFourier f), hb2.coeFn_toLp]
      with ξ hl hr
    rw [hl, hr]
  have hinv : Hs.toL2 (by norm_num) f = 𝓕⁻ (hb2.toLp b) := by
    apply sobolevFourier.injective
    rw [hfreq]
    exact (sobolevFourier.apply_symm_apply (hb2.toLp b)).symm
  have hbridge := l1_l2_fourierInv_bridge hb1 hb2
  rw [hinv, eLpNorm_congr_ae hbridge, eLpNorm_exponent_top]
  obtain ⟨C, hC⟩ := inverseIntegral_bounded
    (memLp_one_iff_integrable.mp hb1)
  exact eLpNormEssSup_lt_top_of_ae_bound
    (Filter.Eventually.of_forall hC)

/-- The same physical function, with its Sobolev order lowered from `1` to
`1/2`. -/
def hsOneToHalfCLM : Hs (1 : ℝ) →L[ℂ] Hs (1 / 2 : ℝ) :=
  hsHalfToL2CLM

lemma hsOneToHalf_physical (f : Hs (1 : ℝ)) :
    Hs.toL2 (by norm_num) (hsOneToHalfCLM f) =
      Hs.toL2 (by norm_num) f := by
  have hmid : sobolevFourier (hsOneToHalfCLM f) =
      boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
        (by norm_num) norm_negativeHalfWeight_le (sobolevFourier f) := by
    change sobolevFourier (hsHalfToL2CLM f) = _
    rw [hsHalfToL2CLM_apply, fourier_Hs_toL2]
  have hmidcoe := congrArg (fun q : FourierL2 => (q : ℝ → ℂ)) hmid
  have hmidpoint : ∀ᵐ ξ : ℝ ∂volume,
      (sobolevFourier (hsOneToHalfCLM f) : ℝ → ℂ) ξ =
        negativeHalfWeight ξ * (sobolevFourier f : ℝ → ℂ) ξ := by
    rw [hmidcoe]
    exact coe_boundedMulCLM _ _ _ _ _ _
  apply sobolevFourier.injective
  rw [fourier_Hs_toL2, fourier_Hs_one_toL2]
  apply Lp.ext
  filter_upwards [coe_boundedMulCLM negativeHalfWeight
      continuous_negativeHalfWeight 1 (by norm_num)
      norm_negativeHalfWeight_le (sobolevFourier (hsOneToHalfCLM f)),
    coe_boundedMulCLM negativeOneWeight continuous_negativeOneWeight 1
      (by norm_num) norm_negativeOneWeight_le (sobolevFourier f), hmidpoint]
      with ξ hl hr hm
  rw [hl, hr, hm]
  unfold negativeHalfWeight negativeOneWeight
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  push_cast
  rw [← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.rpow_add hpos]
  norm_num

/-- An `H¹` coefficient as a bounded critical element. -/
def hsOneBoundedCritical (f : Hs (1 : ℝ)) : BoundedCritical where
  val := hsOneToHalfCLM f
  bounded := by
    rw [hsOneToHalf_physical]
    exact Hs_one_eLpNorm_top_lt_top f

lemma hsOneBoundedCritical_toL2 (f : Hs (1 : ℝ)) :
    (hsOneBoundedCritical f).toL2 = Hs.toL2 (by norm_num) f :=
  hsOneToHalf_physical f

/-- Multiplication of an `H¹` coefficient by a fixed bounded critical
function. -/
def hsOneMul (f : BoundedCritical) (a : Hs (1 : ℝ)) : Hs (1 / 2 : ℝ) :=
  ((hsOneBoundedCritical a).mul f).val

lemma hsOneMul_toL2_ae (f : BoundedCritical) (a : Hs (1 : ℝ)) :
    (Hs.toL2 (by norm_num) (hsOneMul f a) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Hs.toL2 (by norm_num) a : ℝ → ℂ) x *
        (f.toL2 : ℝ → ℂ) x := by
  change (((hsOneBoundedCritical a).mul f).toL2 : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [BoundedCritical.mul_toL2_ae (hsOneBoundedCritical a) f]
      with x hx
  rw [hx]
  have ha := congrFun (congrArg (fun q : FourierL2 => (q : ℝ → ℂ))
    (hsOneBoundedCritical_toL2 a)) x
  rw [ha]

lemma hsOneMul_add (f : BoundedCritical) (a b : Hs (1 : ℝ)) :
    hsOneMul f (a + b) = hsOneMul f a + hsOneMul f b := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  have hab : Hs.toL2 (by norm_num) (a + b) =
      Hs.toL2 (by norm_num) a + Hs.toL2 (by norm_num) b := by
    calc
      _ = hsOneToL2CLM (a + b) := (hsOneToL2CLM_apply _).symm
      _ = hsOneToL2CLM a + hsOneToL2CLM b := map_add _ _ _
      _ = _ := by rw [hsOneToL2CLM_apply, hsOneToL2CLM_apply]
  have hprod : Hs.toL2 (by norm_num) (hsOneMul f a + hsOneMul f b) =
      Hs.toL2 (by norm_num) (hsOneMul f a) +
        Hs.toL2 (by norm_num) (hsOneMul f b) := by
    calc
      _ = hsHalfToL2CLM (hsOneMul f a + hsOneMul f b) :=
        (hsHalfToL2CLM_apply _).symm
      _ = hsHalfToL2CLM (hsOneMul f a) +
          hsHalfToL2CLM (hsOneMul f b) := map_add _ _ _
      _ = _ := by rw [hsHalfToL2CLM_apply, hsHalfToL2CLM_apply]
  have hprodx : ∀ x : ℝ,
      (Hs.toL2 (by norm_num) (hsOneMul f a + hsOneMul f b) : ℝ → ℂ) x =
        ((Hs.toL2 (by norm_num) (hsOneMul f a) +
          Hs.toL2 (by norm_num) (hsOneMul f b) : FourierL2) : ℝ → ℂ) x :=
    fun x => congrFun
      (congrArg (fun q : FourierL2 => (q : ℝ → ℂ)) hprod) x
  filter_upwards [hsOneMul_toL2_ae f (a + b), hsOneMul_toL2_ae f a,
    hsOneMul_toL2_ae f b, Lp.coeFn_add (Hs.toL2 (by norm_num) a)
      (Hs.toL2 (by norm_num) b),
    Lp.coeFn_add (Hs.toL2 (by norm_num) (hsOneMul f a))
      (Hs.toL2 (by norm_num) (hsOneMul f b))] with x hout ha hb hcoef hsum
  rw [hout, hprodx, hsum]
  have habx := congrFun
    (congrArg (fun q : FourierL2 => (q : ℝ → ℂ)) hab) x
  rw [habx, hcoef]
  simp only [Pi.add_apply]
  rw [ha, hb]
  ring

lemma hsOneMul_smul (f : BoundedCritical) (c : ℂ) (a : Hs (1 : ℝ)) :
    hsOneMul f (c • a) = c • hsOneMul f a := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  have hca : Hs.toL2 (by norm_num) (c • a) =
      c • Hs.toL2 (by norm_num) a := by
    calc
      _ = hsOneToL2CLM (c • a) := (hsOneToL2CLM_apply _).symm
      _ = c • hsOneToL2CLM a := map_smul _ _ _
      _ = _ := by rw [hsOneToL2CLM_apply]
  have hprod : Hs.toL2 (by norm_num) (c • hsOneMul f a) =
      c • Hs.toL2 (by norm_num) (hsOneMul f a) := by
    calc
      _ = hsHalfToL2CLM (c • hsOneMul f a) :=
        (hsHalfToL2CLM_apply _).symm
      _ = c • hsHalfToL2CLM (hsOneMul f a) := map_smul _ _ _
      _ = _ := by rw [hsHalfToL2CLM_apply]
  have hprodx : ∀ x : ℝ,
      (Hs.toL2 (by norm_num) (c • hsOneMul f a) : ℝ → ℂ) x =
        (c • Hs.toL2 (by norm_num) (hsOneMul f a) : FourierL2) x :=
    fun x => congrFun
      (congrArg (fun q : FourierL2 => (q : ℝ → ℂ)) hprod) x
  filter_upwards [hsOneMul_toL2_ae f (c • a), hsOneMul_toL2_ae f a,
    Lp.coeFn_smul c (Hs.toL2 (by norm_num) a),
    Lp.coeFn_smul c (Hs.toL2 (by norm_num) (hsOneMul f a))]
      with x hout ha hcoef hsmul
  rw [hout, hprodx, hsmul]
  have hcax := congrFun
    (congrArg (fun q : FourierL2 => (q : ℝ → ℂ)) hca) x
  rw [hcax, hcoef]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ha]
  ring

def hsOneMulLinear (f : BoundedCritical) :
    Hs (1 : ℝ) →ₗ[ℂ] Hs (1 / 2 : ℝ) where
  toFun := hsOneMul f
  map_add' := hsOneMul_add f
  map_smul' := hsOneMul_smul f

private lemma boundedCritical_toL2_lt_top (f : BoundedCritical) :
    eLpNorm (f.toL2 : ℝ → ℂ) ⊤ volume < ⊤ := f.bounded

private def boundedProductRightLinear (f : BoundedCritical) :
    FourierL2 →ₗ[ℂ] FourierL2 where
  toFun := fun a => boundedProductL2 a f.toL2
    (boundedCritical_toL2_lt_top f)
  map_add' := by
    intro a b
    apply Lp.ext
    filter_upwards [coe_boundedProductL2 (a + b) f.toL2
        (boundedCritical_toL2_lt_top f),
      coe_boundedProductL2 a f.toL2 (boundedCritical_toL2_lt_top f),
      coe_boundedProductL2 b f.toL2 (boundedCritical_toL2_lt_top f),
      Lp.coeFn_add a b,
      Lp.coeFn_add
        (boundedProductL2 a f.toL2 (boundedCritical_toL2_lt_top f))
        (boundedProductL2 b f.toL2 (boundedCritical_toL2_lt_top f))]
        with x hout ha hb hab hsum
    rw [hout, hsum, hab]
    simp only [Pi.add_apply]
    rw [ha, hb]
    ring
  map_smul' := by
    intro c a
    change boundedProductL2 (c • a) f.toL2
      (boundedCritical_toL2_lt_top f) =
        c • boundedProductL2 a f.toL2 (boundedCritical_toL2_lt_top f)
    apply Lp.ext
    filter_upwards [coe_boundedProductL2 (c • a) f.toL2
        (boundedCritical_toL2_lt_top f),
      coe_boundedProductL2 a f.toL2 (boundedCritical_toL2_lt_top f),
      Lp.coeFn_smul c a,
      Lp.coeFn_smul c
        (boundedProductL2 a f.toL2 (boundedCritical_toL2_lt_top f))]
        with x hout ha hca hsmul
    rw [hout, hsmul, hca]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha]
    ring

private lemma norm_boundedProductRight_le (f : BoundedCritical)
    (a : FourierL2) :
    ‖boundedProductL2 a f.toL2 (boundedCritical_toL2_lt_top f)‖ ≤
      (eLpNorm (f.toL2 : ℝ → ℂ) ⊤ volume).toReal * ‖a‖ := by
  have h := norm_boundedProductL2_le a f.toL2
    (boundedCritical_toL2_lt_top f)
  have ht := (ENNReal.toReal_le_toReal enorm_ne_top
    (ENNReal.mul_ne_top enorm_ne_top
      (ne_of_lt (boundedCritical_toL2_lt_top f)))).2 h
  rw [ENNReal.toReal_mul] at ht
  simpa only [Lp.norm_def, Lp.enorm_def, mul_comm] using ht

private def boundedProductRightCLM (f : BoundedCritical) :
    FourierL2 →L[ℂ] FourierL2 :=
  (boundedProductRightLinear f).mkContinuous
    (eLpNorm (f.toL2 : ℝ → ℂ) ⊤ volume).toReal
    (norm_boundedProductRight_le f)

private lemma hsOneMul_toL2_eq (f : BoundedCritical) (a : Hs (1 : ℝ)) :
    Hs.toL2 (by norm_num) (hsOneMul f a) =
      boundedProductRightCLM f (Hs.toL2 (by norm_num) a) := by
  apply Lp.ext
  filter_upwards [hsOneMul_toL2_ae f a,
    coe_boundedProductL2 (Hs.toL2 (by norm_num) a) f.toL2
      (boundedCritical_toL2_lt_top f)]
      with x hl hr
  change (Hs.toL2 (by norm_num) (hsOneMul f a) : ℝ → ℂ) x =
    (boundedProductL2 (Hs.toL2 (by norm_num) a) f.toL2 f.bounded :
      ℝ → ℂ) x
  rw [hl, hr]

/-- Multiplication by a fixed bounded critical function is continuous from
`H¹` to `H^{1/2}`. -/
def hsOneMulCLM (f : BoundedCritical) :
    Hs (1 : ℝ) →L[ℂ] Hs (1 / 2 : ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph (g := hsOneMulLinear f) (by
    intro u x y hux huy
    apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
    have hxL2 : Tendsto (fun n => Hs.toL2 (by norm_num) (u n)) atTop
        (𝓝 (Hs.toL2 (by norm_num) x)) := by
      have h := hsOneToL2CLM.continuous.continuousAt.tendsto.comp hux
      change Tendsto (fun n => hsOneToL2CLM (u n)) atTop
        (𝓝 (hsOneToL2CLM x)) at h
      simpa only [hsOneToL2CLM_apply] using h
    have hmul := (boundedProductRightCLM f).continuous.continuousAt.tendsto.comp hxL2
    have hyL2 : Tendsto (fun n => Hs.toL2 (by norm_num)
        ((hsOneMulLinear f) (u n))) atTop
        (𝓝 (Hs.toL2 (by norm_num) y)) := by
      have h := hsHalfToL2CLM.continuous.continuousAt.tendsto.comp huy
      change Tendsto (fun n => hsHalfToL2CLM ((hsOneMulLinear f) (u n)))
        atTop (𝓝 (hsHalfToL2CLM y)) at h
      simpa only [hsHalfToL2CLM_apply] using h
    have heq : (fun n => Hs.toL2 (by norm_num)
        ((hsOneMulLinear f) (u n))) =
        fun n => boundedProductRightCLM f (Hs.toL2 (by norm_num) (u n)) := by
      funext n
      exact hsOneMul_toL2_eq f (u n)
    rw [heq] at hyL2
    have huniq := tendsto_nhds_unique hyL2 hmul
    change Hs.toL2 (by norm_num) y =
      Hs.toL2 (by norm_num) (hsOneMul f x)
    rw [hsOneMul_toL2_eq]
    exact huniq)

@[simp] lemma hsOneMulCLM_apply (f : BoundedCritical) (a : Hs (1 : ℝ)) :
    hsOneMulCLM f a = hsOneMul f a := rfl

def positiveOneWeight (ξ : ℝ) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

lemma positiveOneWeight_hasTemperateGrowth :
    positiveOneWeight.HasTemperateGrowth := by
  unfold positiveOneWeight
  fun_prop

def schwartzHsOneFourier (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ positiveOneWeight
    (FourierTransform.fourier φ)

lemma schwartzHsOneFourier_apply (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    schwartzHsOneFourier φ ξ = positiveOneWeight ξ *
      FourierTransform.fourier φ ξ := by
  simpa only [schwartzHsOneFourier, smul_eq_mul] using congrFun
    (SchwartzMap.smulLeftCLM_apply positiveOneWeight_hasTemperateGrowth
      (FourierTransform.fourier φ)) ξ

/-- The canonical `H¹` realization of a Schwartz function. -/
def schwartzHsOne (φ : SchwartzMap ℝ ℂ) : Hs (1 : ℝ) :=
  sobolevFourier.symm ((schwartzHsOneFourier φ).toLp 2 volume)

lemma schwartzHsOne_toL2 (φ : SchwartzMap ℝ ℂ) :
    Hs.toL2 (by norm_num) (schwartzHsOne φ) = φ.toLp 2 volume := by
  apply sobolevFourier.injective
  rw [fourier_Hs_one_toL2]
  have hrhs : sobolevFourier (φ.toLp 2 volume) =
      (FourierTransform.fourier φ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq φ
  rw [hrhs]
  apply Lp.ext
  filter_upwards [coe_boundedMulCLM negativeOneWeight
      continuous_negativeOneWeight 1 (by norm_num)
      norm_negativeOneWeight_le (sobolevFourier (schwartzHsOne φ)),
    (schwartzHsOneFourier φ).coeFn_toLp 2 volume,
    (FourierTransform.fourier φ).coeFn_toLp 2 volume] with ξ hl hq hr
  rw [hl, hr]
  have hcoord : sobolevFourier (schwartzHsOne φ) =
      (schwartzHsOneFourier φ).toLp 2 volume := by
    exact sobolevFourier.apply_symm_apply _
  rw [hcoord]
  rw [hq, schwartzHsOneFourier_apply]
  unfold negativeOneWeight positiveOneWeight
  have hp : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  push_cast
  rw [← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
  norm_num

lemma schwartzHsOne_toL2_ae (φ : SchwartzMap ℝ ℂ) :
    (Hs.toL2 (by norm_num) (schwartzHsOne φ) : ℝ → ℂ) =ᵐ[volume] φ := by
  rw [schwartzHsOne_toL2]
  exact φ.coeFn_toLp 2 volume

/-- The quadratic current of a bounded critical slice, as a continuous
functional on the separable coefficient space `H¹`. -/
def boundedQuadraticCurrentHsOneCLM (f : BoundedCritical) :
    Hs (1 : ℝ) →L[ℂ] ℂ :=
  (criticalPairingCLM (criticalDerivative f.val)).comp (hsOneMulCLM f.conj)

lemma boundedQuadraticCurrentHsOneCLM_apply
    (f : BoundedCritical) (a : Hs (1 : ℝ)) :
    boundedQuadraticCurrentHsOneCLM f a =
      boundedQuadraticCurrentAgainst f (hsOneBoundedCritical a) := by
  rfl

lemma hsOneMul_conj_schwartz (f : BoundedCritical)
    (φ : SchwartzMap ℝ ℂ) :
    hsOneMul f.conj (schwartzHsOne φ) =
      schwartzHsMultiplier φ (criticalConj f.val) := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  filter_upwards [hsOneMul_toL2_ae f.conj (schwartzHsOne φ),
    schwartzHsOne_toL2_ae φ, BoundedCritical.conj_toL2_ae f,
    schwartzHsMultiplier_toL2_ae φ (criticalConj f.val),
    criticalConj_toL2_ae f.val] with x hl hφ hfc hr hc
  rw [hl, hr, hφ, hfc, hc]
  change φ x * (starRingEnd ℂ)
      ((Hs.toL2 (by norm_num) f.val : ℝ → ℂ) x) =
    (starRingEnd ℂ) ((Hs.toL2 (by norm_num) f.val : ℝ → ℂ) x) * φ x
  ring

lemma criticalQuadraticCurrent_eq_hsOne
    (f : BoundedCritical) (φ : SchwartzMap ℝ ℂ) :
    criticalQuadraticCurrent f.val φ =
      boundedQuadraticCurrentHsOneCLM f (schwartzHsOne φ) := by
  unfold criticalQuadraticCurrent boundedQuadraticCurrentHsOneCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [hsOneMulCLM_apply, hsOneMul_conj_schwartz]

end CubicNLSPhaseRetrieval
