import Mathlib

/-!
# Fourier analysis and the H^s calculus

Blueprint chapter: `chap:fourier` (module 1).
Imports: Mathlib only.
-/

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The L² coordinate model used to bundle every `H^s(ℝ)` as a Hilbert space. -/
abbrev FourierL2 : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- Mathlib's L² Fourier transform; all constants in later modules use its `2π` convention. -/
def sobolevFourier : FourierL2 ≃ₗᵢ[ℂ] FourierL2 :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-- The inhomogeneous Bessel multiplier `⟨D⟩^s` on tempered distributions. -/
def besselMultiplier (s : ℝ) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.besselPotential ℝ ℂ s

/-- The homogeneous multiplier `|D|^s` on tempered distributions. -/
def homogeneousMultiplier (s : ℝ) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ
    (fun ξ : ℝ => ((|ξ| ^ s : ℝ) : ℂ))

/--
The bundled Sobolev Hilbert space. An element is the L² coordinate `g = ⟨D⟩^s f`;
`Hs.toTempered` below recovers the physical tempered distribution `f`.
-/
abbrev Hs (_s : ℝ) : Type := FourierL2

namespace Hs

/-- Recover the physical distribution from its weighted L² coordinate. -/
def toTempered (s : ℝ) (f : Hs s) : 𝓢'(ℝ, ℂ) :=
  besselMultiplier (-s) (MeasureTheory.Lp.toTemperedDistribution f)

theorem memSobolev (s : ℝ) (f : Hs s) :
    TemperedDistribution.MemSobolev s 2 (toTempered s f) := by
  rw [toTempered, besselMultiplier,
    TemperedDistribution.memSobolev_besselPotential_iff]
  simpa using (TemperedDistribution.memSobolev_zero_iff.mpr
    ⟨f, rfl⟩ : TemperedDistribution.MemSobolev 0 2
      (MeasureTheory.Lp.toTemperedDistribution f))

/-- The physical L² representative of an `H^s` element when `s ≥ 0`. -/
noncomputable def toL2 {s : ℝ} (hs : 0 ≤ s) (f : Hs s) : FourierL2 :=
  Classical.choose (TemperedDistribution.memSobolev_zero_iff.mp
    ((memSobolev s f).mono hs))

theorem toTempered_toL2 {s : ℝ} (hs : 0 ≤ s) (f : Hs s) :
    toTempered s f = MeasureTheory.Lp.toTemperedDistribution (toL2 hs f) :=
  Classical.choose_spec (TemperedDistribution.memSobolev_zero_iff.mp
    ((memSobolev s f).mono hs))

/-- The weighted-coordinate realization of an `H^s` element as a tempered
distribution is faithful. -/
theorem toTempered_injective (s : ℝ) : Function.Injective (toTempered s) := by
  intro f g hfg
  have hcoord : MeasureTheory.Lp.toTemperedDistribution f =
      MeasureTheory.Lp.toTemperedDistribution g := by
    have h := congrArg
      (TemperedDistribution.besselPotential ℝ ℂ s) hfg
    simpa [toTempered, besselMultiplier] using h
  have hinj : Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2 :
        FourierL2 →L[ℂ] TemperedDistribution ℝ ℂ) :=
    LinearMap.ker_eq_bot.mp (by
      simpa using
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := ℂ) (E := ℝ) (μ := volume) (p := (2 : ℝ≥0∞))))
  exact hinj hcoord

/-- For nonnegative order, the physical `L²` realization is faithful. -/
theorem toL2_injective {s : ℝ} (hs : 0 ≤ s) :
    Function.Injective (toL2 hs : Hs s → FourierL2) := by
  intro f g hfg
  apply toTempered_injective s
  rw [toTempered_toL2 hs, toTempered_toL2 hs, hfg]

end Hs

/-- The complex-bilinear `H^{-1/2}`–`H^{1/2}` pairing in L² coordinates. -/
def hsNegPairing (T : Hs (-(1 / 2 : ℝ))) (φ : Hs (1 / 2 : ℝ)) : ℂ :=
  ∫ ξ : ℝ, (T : ℝ → ℂ) ξ * (φ : ℝ → ℂ) ξ

/-- Local Sobolev membership, expressed by compactly supported Schwartz cutoffs. -/
def MemHsLoc (s : ℝ) (T : 𝓢'(ℝ, ℂ)) : Prop :=
  ∀ χ : 𝓢(ℝ, ℂ), HasCompactSupport (χ : ℝ → ℂ) →
    TemperedDistribution.MemSobolev s 2
      (TemperedDistribution.smulLeftCLM ℂ (χ : ℝ → ℂ) T)

/-- The exact Gagliardo constant for the Mathlib Fourier normalization. -/
def gagliardoConstant (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : ℝ,
    ‖Complex.exp (Complex.I * ((2 * Real.pi * h : ℝ) : ℂ)) - 1‖₊ ^ (2 : ℕ) /
      ENNReal.ofReal (|h| ^ (1 + 2 * s))

/-- The squared homogeneous Gagliardo seminorm of an L² representative. -/
def gagliardoEnergy (s : ℝ) (f : FourierL2) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ,
    ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖₊ ^ (2 : ℕ) /
      ENNReal.ofReal (|p.1 - p.2| ^ (1 + 2 * s))

/-- The squared homogeneous Fourier `Ḣ^s` energy. -/
def homogeneousFourierEnergy (s : ℝ) (f : FourierL2) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ,
    ENNReal.ofReal (|ξ| ^ (2 * s)) *
      ‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ ^ (2 : ℕ)

/-- The squared inhomogeneous Fourier `H^s` energy of a physical L² function. -/
def inhomogeneousFourierEnergy (s : ℝ) (f : FourierL2) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ,
    ENNReal.ofReal ((1 + ξ ^ 2) ^ s) *
      ‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ ^ (2 : ℕ)

/-- Uniform cutoff error appearing in the Gagliardo localization argument. -/
def cutoffGagliardoError (s : ℝ) (χ : 𝓢(ℝ, ℝ)) (R y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ,
    ENNReal.ofReal (|χ (x / R) - χ (y / R)| ^ 2) /
      ENNReal.ofReal (|x - y| ^ (1 + 2 * s))

/-- Essential-supremum-free notation for the actual sup norm of a Schwartz function. -/
def schwartzSupNorm (χ : 𝓢(ℝ, ℂ)) : ℝ≥0∞ := ⨆ x : ℝ, ‖χ x‖₊

/-- Sup norm of the classical derivative of a Schwartz function. -/
def schwartzDerivSupNorm (χ : 𝓢(ℝ, ℂ)) : ℝ≥0∞ :=
  ⨆ x : ℝ, ‖deriv (χ : ℝ → ℂ) x‖₊

/-- Translation on L², represented by `x ↦ f (x+h)`. -/
def translateL2 (h : ℝ) (f : FourierL2) : FourierL2 :=
  MemLp.toLp (fun x : ℝ => (f : ℝ → ℂ) (x + h)) (by
    simpa [Function.comp_def] using
      (Lp.memLp f).comp_measurePreserving
        (MeasureTheory.measurePreserving_add_right volume h))

/-- `def:Hs-neg-pairing`: Cauchy–Schwarz bound for the complex-bilinear pairing. -/
theorem hsNegPairing_bound (T : Hs (-(1 / 2 : ℝ))) (φ : Hs (1 / 2 : ℝ)) :
    ‖hsNegPairing T φ‖ ≤ ‖T‖ * ‖φ‖ := by
  rw [hsNegPairing]
  calc
    ‖∫ ξ : ℝ, (T : ℝ → ℂ) ξ * (φ : ℝ → ℂ) ξ‖ ≤
        ∫ ξ : ℝ, ‖(T : ℝ → ℂ) ξ * (φ : ℝ → ℂ) ξ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖(T : ℝ → ℂ) ξ‖ * ‖(φ : ℝ → ℂ) ξ‖ := by
      congr 1
      funext ξ
      exact norm_mul _ _
    _ ≤ (∫ ξ : ℝ, ‖(T : ℝ → ℂ) ξ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ ξ : ℝ, ‖(φ : ℝ → ℂ) ξ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using Lp.memLp T) (by simpa using Lp.memLp φ)
    _ = ‖T‖ * ‖φ‖ := by
      have hnorm (f : FourierL2) :
          (∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖f‖ := by
        have hfint : Integrable (fun x : ℝ => ‖(f : ℝ → ℂ) x‖ ^ 2) volume :=
          (Lp.memLp f).norm.integrable_sq
        have hfnonneg : 0 ≤ ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 :=
          integral_nonneg (fun _ => sq_nonneg _)
        rw [Lp.norm_def,
          eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
        norm_num
        rw [← ENNReal.toReal_rpow]
        congr 1
        rw [← ENNReal.toReal_ofReal hfnonneg]
        congr 1
        rw [ofReal_integral_eq_lintegral_ofReal hfint
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        congr 1
        funext x
        simp [ofReal_norm]
      rw [hnorm T, hnorm φ]

private def boundedSymbolLp (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C) : Lp ℂ ⊤ (volume : Measure ℝ) :=
  (memLp_top_of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)).toLp m

private lemma coe_boundedSymbolLp (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    (boundedSymbolLp m hm C hC : ℝ → ℂ) =ᵐ[volume] m := by
  exact MemLp.coeFn_toLp _

private lemma norm_boundedSymbolLp_le (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    ‖boundedSymbolLp m hm C hC‖ ≤ C := by
  rw [Lp.norm_def]
  calc
    (eLpNorm (boundedSymbolLp m hm C hC : ℝ → ℂ) ⊤ volume).toReal ≤
        (ENNReal.ofReal C).toReal := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      rw [eLpNorm_congr_ae (coe_boundedSymbolLp m hm C hC), eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hC)
    _ = C := ENNReal.toReal_ofReal hC0

private def boundedMulLinear (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C) : FourierL2 →ₗ[ℂ] FourierL2 where
  toFun f := boundedSymbolLp m hm C hC • f
  map_add' f g := Lp.add_smul (r := 2) _ _ _
  map_smul' c f := (Lp.smul_comm (r := 2) c (boundedSymbolLp m hm C hC) f).symm

def boundedMulCLM (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) : FourierL2 →L[ℂ] FourierL2 :=
  (boundedMulLinear m hm C hC).mkContinuous C fun f => by
    exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_boundedSymbolLp_le m hm C hC0 hC) (norm_nonneg f))

lemma norm_boundedMulCLM_le (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    ‖boundedMulCLM m hm C hC0 hC‖ ≤ C := by
  exact LinearMap.mkContinuous_norm_le _ hC0 _

lemma coe_boundedMulCLM (m : ℝ → ℂ) (hm : Continuous m)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : FourierL2) :
    (boundedMulCLM m hm C hC0 hC f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => m ξ * (f : ℝ → ℂ) ξ := by
  change ((boundedSymbolLp m hm C hC • f : FourierL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (boundedSymbolLp m hm C hC) f,
    coe_boundedSymbolLp m hm C hC] with ξ hmul hs
  rw [hmul]
  change (boundedSymbolLp m hm C hC : ℝ → ℂ) ξ * (f : ℝ → ℂ) ξ = _
  rw [hs]

lemma toTemperedDistribution_boundedMulCLM (m : ℝ → ℂ) (hm : Continuous m)
    (hmt : m.HasTemperateGrowth) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C)
    (f : FourierL2) :
    MeasureTheory.Lp.toTemperedDistribution (boundedMulCLM m hm C hC0 hC f) =
      TemperedDistribution.smulLeftCLM ℂ m
        (MeasureTheory.Lp.toTemperedDistribution f) := by
  change MeasureTheory.Lp.toTemperedDistribution (boundedSymbolLp m hm C hC • f) = _
  unfold boundedSymbolLp
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq hmt]

lemma fourier_Hs_toTempered (s : ℝ) (f : Hs s) :
    𝓕 (Hs.toTempered s f) =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : ℝ => (((1 + ‖ξ‖ ^ 2) ^ ((-s) / 2) : ℝ) : ℂ))
        (MeasureTheory.Lp.toTemperedDistribution (sobolevFourier f)) := by
  rw [Hs.toTempered, besselMultiplier,
    TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  rfl

lemma sobolevFourier_eq_fourier (f : FourierL2) :
    sobolevFourier f = 𝓕 f := rfl

def translationPhase (h ξ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((h * (2 * Real.pi * ξ) : ℝ) : ℂ))

private def normalizedFrequency (ξ : ℝ) : ℝ :=
  ξ / Real.sqrt (1 + ξ ^ 2)

private def derivativeCoordinateSymbol (ξ : ℝ) : ℂ :=
  ((2 * Real.pi * normalizedFrequency ξ : ℝ) : ℂ) * Complex.I

private def quotientCoordinateSymbol (h ξ : ℝ) : ℂ :=
  ((h : ℂ)⁻¹) * (translationPhase h ξ - 1) /
    ((Real.sqrt (1 + ξ ^ 2) : ℝ) : ℂ)

private lemma sqrt_one_add_sq_pos (ξ : ℝ) : 0 < Real.sqrt (1 + ξ ^ 2) := by
  positivity

private lemma abs_normalizedFrequency_le_one (ξ : ℝ) : |normalizedFrequency ξ| ≤ 1 := by
  rw [normalizedFrequency, abs_div, abs_of_pos (sqrt_one_add_sq_pos ξ), div_le_one]
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg ξ])
  · exact sqrt_one_add_sq_pos ξ

private lemma continuous_translationPhase (h : ℝ) : Continuous (translationPhase h) := by
  unfold translationPhase
  fun_prop

private lemma continuous_normalizedFrequency : Continuous normalizedFrequency := by
  unfold normalizedFrequency
  exact continuous_id.div (by fun_prop) (fun ξ => (sqrt_one_add_sq_pos ξ).ne')

private lemma continuous_derivativeCoordinateSymbol : Continuous derivativeCoordinateSymbol := by
  unfold derivativeCoordinateSymbol
  exact (Complex.ofRealCLM.continuous.comp
    (continuous_const.mul continuous_normalizedFrequency)).mul continuous_const

private lemma continuous_quotientCoordinateSymbol (h : ℝ) :
    Continuous (quotientCoordinateSymbol h) := by
  unfold quotientCoordinateSymbol translationPhase
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro ξ
    exact Complex.ofReal_ne_zero.mpr (sqrt_one_add_sq_pos ξ).ne'

private lemma norm_derivativeCoordinateSymbol_le (ξ : ℝ) :
    ‖derivativeCoordinateSymbol ξ‖ ≤ 2 * Real.pi := by
  rw [derivativeCoordinateSymbol, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith [abs_normalizedFrequency_le_one ξ, Real.pi_pos]

private lemma norm_quotientCoordinateSymbol_le (h ξ : ℝ) :
    ‖quotientCoordinateSymbol h ξ‖ ≤ 2 * Real.pi := by
  by_cases hh : h = 0
  · subst h
    simp [quotientCoordinateSymbol, translationPhase]
    positivity
  have hosc : translationPhase h ξ =
      Complex.exp (Complex.I * ((h * (2 * Real.pi * ξ) : ℝ) : ℂ)) := rfl
  have htrig := Real.norm_exp_I_mul_ofReal_sub_one_le (x := h * (2 * Real.pi * ξ))
  rw [quotientCoordinateSymbol, hosc, norm_div, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sqrt_one_add_sq_pos ξ)]
  calc
    |h|⁻¹ * ‖Complex.exp (Complex.I * ((h * (2 * Real.pi * ξ) : ℝ) : ℂ)) - 1‖ /
          Real.sqrt (1 + ξ ^ 2) ≤
        |h|⁻¹ * ‖h * (2 * Real.pi * ξ)‖ / Real.sqrt (1 + ξ ^ 2) := by
      gcongr
    _ = 2 * Real.pi * |normalizedFrequency ξ| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        normalizedFrequency, abs_div,
        abs_of_pos (sqrt_one_add_sq_pos ξ)]
      rw [abs_of_pos Real.pi_pos]
      norm_num
      field_simp [abs_ne_zero.mpr hh]
    _ ≤ 2 * Real.pi := by
      nlinarith [abs_normalizedFrequency_le_one ξ, Real.pi_pos]

def negativeHalfWeight (ξ : ℝ) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)

lemma continuous_negativeHalfWeight : Continuous negativeHalfWeight := by
  unfold negativeHalfWeight
  have hb : Continuous (fun ξ : ℝ => 1 + ‖ξ‖ ^ 2) := by fun_prop
  exact Complex.continuous_ofReal.comp
    (hb.rpow_const (fun ξ => Or.inl (by positivity)))

lemma hasTemperateGrowth_negativeHalfWeight :
    negativeHalfWeight.HasTemperateGrowth := by
  unfold negativeHalfWeight
  fun_prop

lemma norm_negativeHalfWeight_le (ξ : ℝ) : ‖negativeHalfWeight ξ‖ ≤ 1 := by
  unfold negativeHalfWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖]) (by norm_num)

private lemma negativeHalfWeight_sq_mul_sqrt (ξ : ℝ) :
    (negativeHalfWeight ξ) ^ (2 : ℕ) *
      ((Real.sqrt (1 + ξ ^ 2) : ℝ) : ℂ) = 1 := by
  have hr : ((1 + ξ ^ 2) ^ (-(1 : ℝ) / 4)) ^ (2 : ℕ) *
      Real.sqrt (1 + ξ ^ 2) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + ξ ^ 2),
      Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < 1 + ξ ^ 2)]
    norm_num
  simpa [negativeHalfWeight, Real.norm_eq_abs, sq_abs] using congrArg Complex.ofReal hr

private lemma derivativeCoordinateSymbol_factor (ξ : ℝ) :
    derivativeCoordinateSymbol ξ =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        (negativeHalfWeight ξ * (((ξ : ℝ) : ℂ) * negativeHalfWeight ξ)) := by
  simp only [derivativeCoordinateSymbol, normalizedFrequency]
  have hs := negativeHalfWeight_sq_mul_sqrt ξ
  have hs' : negativeHalfWeight ξ ^ (2 : ℕ) =
      (((Real.sqrt (1 + ξ ^ 2) : ℝ) : ℂ))⁻¹ := by
    field_simp [ne_of_gt (sqrt_one_add_sq_pos ξ)]
    exact hs
  ring_nf at hs' ⊢
  rw [hs']
  push_cast
  ring

private lemma hasTemperateGrowth_derivativeCoordinateSymbol :
    derivativeCoordinateSymbol.HasTemperateGrowth := by
  rw [funext derivativeCoordinateSymbol_factor]
  have hc : (fun _ : ℝ => (((2 * Real.pi : ℝ) : ℂ) * Complex.I)).HasTemperateGrowth := by
    fun_prop
  have hx : (fun x : ℝ => ((x : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  exact hc.mul (hasTemperateGrowth_negativeHalfWeight.mul
    (hx.mul hasTemperateGrowth_negativeHalfWeight))

lemma fourier_Hs_toL2 (f : Hs (1 / 2 : ℝ)) :
    sobolevFourier (Hs.toL2 (by norm_num) f) =
      boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
        norm_negativeHalfWeight_le (sobolevFourier f) := by
  have hinj : Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2 :
        FourierL2 →L[ℂ] 𝓢'(ℝ, ℂ)) :=
    LinearMap.ker_eq_bot.mp (by
      simpa using
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := ℂ) (E := ℝ) (μ := volume) (p := (2 : ℝ≥0∞))))
  apply hinj
  change MeasureTheory.Lp.toTemperedDistribution
      (sobolevFourier (Hs.toL2 (by norm_num) f)) = _
  rw [sobolevFourier_eq_fourier]
  calc
    _ = 𝓕 (MeasureTheory.Lp.toTemperedDistribution (Hs.toL2 (by norm_num) f)) := by
      simpa [sobolevFourier] using
        (MeasureTheory.Lp.fourier_toTemperedDistribution_eq
          (Hs.toL2 (by norm_num) f)).symm
    _ = 𝓕 (Hs.toTempered (1 / 2 : ℝ) f) := by
      rw [Hs.toTempered_toL2 (s := (1 / 2 : ℝ)) (by norm_num) f]
    _ = TemperedDistribution.smulLeftCLM ℂ negativeHalfWeight
          (MeasureTheory.Lp.toTemperedDistribution (sobolevFourier f)) := by
      rw [fourier_Hs_toTempered]
      congr 2
      funext ξ
      norm_num [negativeHalfWeight]
    _ = MeasureTheory.Lp.toTemperedDistribution
          (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
            norm_negativeHalfWeight_le (sobolevFourier f)) :=
      (toTemperedDistribution_boundedMulCLM negativeHalfWeight
        continuous_negativeHalfWeight hasTemperateGrowth_negativeHalfWeight 1
        (by norm_num) norm_negativeHalfWeight_le (sobolevFourier f)).symm

/-- The physical `L²` realization of an `H^{1/2}` element is contractive. -/
theorem norm_Hs_toL2_le (f : Hs (1 / 2 : ℝ)) :
    ‖Hs.toL2 (by norm_num) f‖ ≤ ‖f‖ := by
  rw [← LinearIsometryEquiv.norm_map sobolevFourier
    (Hs.toL2 (by norm_num) f), fourier_Hs_toL2]
  calc
    ‖boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
        norm_negativeHalfWeight_le (sobolevFourier f)‖ ≤
        ‖boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
          norm_negativeHalfWeight_le‖ * ‖sobolevFourier f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖sobolevFourier f‖ := by
      gcongr
      exact norm_boundedMulCLM_le _ _ _ _ _
    _ = ‖f‖ := by simp

/-- Continuous linear physical realization of `H^{1/2}` in `L²`, constructed
in Fourier coordinates. -/
def hsHalfToL2CLM : Hs (1 / 2 : ℝ) →L[ℂ] FourierL2 :=
  sobolevFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
      norm_negativeHalfWeight_le).comp
        sobolevFourier.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem hsHalfToL2CLM_apply (f : Hs (1 / 2 : ℝ)) :
    hsHalfToL2CLM f = Hs.toL2 (by norm_num) f := by
  apply sobolevFourier.injective
  rw [fourier_Hs_toL2]
  simp [hsHalfToL2CLM]

/-- The homogeneous half-derivative energy of the physical realization is
bounded by the squared bundled Sobolev norm. -/
theorem homogeneousFourierEnergy_Hs_toL2_le_enorm_sq
    (f : Hs (1 / 2 : ℝ)) :
    homogeneousFourierEnergy (1 / 2 : ℝ) (Hs.toL2 (by norm_num) f) ≤
      ‖f‖ₑ ^ (2 : ℕ) := by
  rw [homogeneousFourierEnergy]
  have hfourier := congrArg
    (fun q : FourierL2 => (q : ℝ → ℂ)) (fourier_Hs_toL2 f)
  have hcoe := coe_boundedMulCLM negativeHalfWeight
    continuous_negativeHalfWeight 1 (by norm_num)
    norm_negativeHalfWeight_le (sobolevFourier f)
  have heq : (sobolevFourier (Hs.toL2 (by norm_num) f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => negativeHalfWeight ξ * (sobolevFourier f : ℝ → ℂ) ξ := by
    filter_upwards [hcoe] with ξ hξ
    rw [hfourier, hξ]
  have hpoint : ∀ᵐ ξ : ℝ ∂volume,
      ENNReal.ofReal (|ξ| ^ (2 * (1 / 2 : ℝ))) *
          ‖(sobolevFourier (Hs.toL2 (by norm_num) f) : ℝ → ℂ) ξ‖₊ ^ (2 : ℕ) ≤
        (↑‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
    filter_upwards [heq] with ξ hξ
    rw [hξ, nnnorm_mul, ENNReal.coe_mul, mul_pow]
    norm_num
    have hweight : ENNReal.ofReal |ξ| *
        (↑‖negativeHalfWeight ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ) ≤ 1 := by
      have hn : ‖negativeHalfWeight ξ‖ =
          (1 + |ξ| ^ 2) ^ (-(1 : ℝ) / 4) := by
        rw [negativeHalfWeight, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity), Real.norm_eq_abs]
      rw [show (↑‖negativeHalfWeight ξ‖₊ : ℝ≥0∞) =
          ENNReal.ofReal ((1 + |ξ| ^ 2) ^ (-(1 : ℝ) / 4)) by
        calc
          (↑‖negativeHalfWeight ξ‖₊ : ℝ≥0∞) =
              ‖negativeHalfWeight ξ‖ₑ := (enorm_eq_nnnorm _).symm
          _ = ENNReal.ofReal ‖negativeHalfWeight ξ‖ := (ofReal_norm _).symm
          _ = _ := congrArg ENNReal.ofReal hn]
      rw [← ENNReal.ofReal_pow (by positivity) 2]
      rw [← ENNReal.ofReal_mul (abs_nonneg ξ)]
      apply ENNReal.ofReal_le_one.mpr
      have hden : 0 < Real.sqrt (1 + ξ ^ 2) := by positivity
      have hp : ((1 + |ξ| ^ 2) ^ (-(1 : ℝ) / 4)) ^ (2 : ℕ) =
          (Real.sqrt (1 + ξ ^ 2))⁻¹ := by
        calc
          ((1 + |ξ| ^ 2) ^ (-(1 : ℝ) / 4)) ^ (2 : ℕ) =
              (1 + |ξ| ^ 2) ^ (-(1 : ℝ) / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
          _ = ((1 + |ξ| ^ 2) ^ ((1 : ℝ) / 2))⁻¹ := by
            convert Real.rpow_neg (by positivity : 0 ≤ 1 + |ξ| ^ 2)
              ((1 : ℝ) / 2) using 1 <;> ring
          _ = (Real.sqrt (1 + ξ ^ 2))⁻¹ := by
            rw [sq_abs, Real.sqrt_eq_rpow]
      rw [hp]
      rw [mul_inv_le_iff₀ hden]
      simp only [one_mul]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ξ])
    calc
      ENNReal.ofReal |ξ| *
          ((↑‖negativeHalfWeight ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ) *
            (↑‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) =
          (ENNReal.ofReal |ξ| *
            (↑‖negativeHalfWeight ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) *
              (↑‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
        ac_rfl
      _ ≤ 1 * (↑‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
        gcongr
      _ = _ := one_mul _
  calc
    (∫⁻ ξ : ℝ, ENNReal.ofReal (|ξ| ^ (2 * (1 / 2 : ℝ))) *
        ‖(sobolevFourier (Hs.toL2 (by norm_num) f) : ℝ → ℂ) ξ‖₊ ^ (2 : ℕ)) ≤
        ∫⁻ ξ : ℝ, (↑‖(sobolevFourier f : ℝ → ℂ) ξ‖₊ : ℝ≥0∞) ^ (2 : ℕ) :=
      lintegral_mono_ae hpoint
    _ = ‖sobolevFourier f‖ₑ ^ (2 : ℕ) := by
      have hsq : ‖sobolevFourier f‖ₑ ^ (2 : ℕ) =
          ∫⁻ ξ : ℝ, ‖(sobolevFourier f : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
        rw [Lp.enorm_def, ← ENNReal.rpow_natCast]
        simpa using (eLpNorm_nnreal_pow_eq_lintegral
          (f := (sobolevFourier f : ℝ → ℂ)) (μ := volume)
          (p := (2 : NNReal)) (by norm_num))
      rw [hsq]
      apply lintegral_congr
      intro ξ
      simp [enorm_eq_nnnorm, ENNReal.rpow_two]
    _ = ‖f‖ₑ ^ (2 : ℕ) := by
      rw [LinearIsometryEquiv.enorm_map]

/-- The physical realization of a bundled `H^{1/2}` function has finite
homogeneous half-derivative Fourier energy. -/
theorem homogeneousFourierEnergy_Hs_toL2_lt_top
    (f : Hs (1 / 2 : ℝ)) :
    homogeneousFourierEnergy (1 / 2 : ℝ) (Hs.toL2 (by norm_num) f) < ⊤ :=
  (homogeneousFourierEnergy_Hs_toL2_le_enorm_sq f).trans_lt
    (ENNReal.pow_lt_top enorm_lt_top)

/-- The Fourier multiplier `(1 + ξ²)^(1/4)` used as the concrete
`H^{1/2}` coordinate weight. -/
def positiveHalfWeight (xi : ℝ) : ℂ :=
  (((1 + xi ^ 2) ^ ((1 : ℝ) / 4) : ℝ) : ℂ)

lemma continuous_positiveHalfWeight : Continuous positiveHalfWeight := by
  unfold positiveHalfWeight
  exact Complex.continuous_ofReal.comp
    ((continuous_const.add (continuous_id.pow 2)).rpow_const
      (fun _ => Or.inr (by norm_num)))

lemma negativeHalfWeight_mul_positiveHalfWeight (xi : ℝ) :
    negativeHalfWeight xi * positiveHalfWeight xi = 1 := by
  unfold negativeHalfWeight positiveHalfWeight
  rw [Real.norm_eq_abs, sq_abs]
  push_cast
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add (by positivity : 0 < 1 + xi ^ 2)]
  norm_num

/-- Bundle an already weighted Fourier coordinate as an `H^{1/2}` element. -/
noncomputable def HsHalfOfWeightedFourier (q : FourierL2) : Hs (1 / 2 : ℝ) :=
  sobolevFourier.symm q

@[simp] theorem sobolevFourier_HsHalfOfWeightedFourier (q : FourierL2) :
    sobolevFourier (HsHalfOfWeightedFourier q) = q := by
  exact sobolevFourier.apply_symm_apply q

/-- If `q` is the Bessel-weighted Fourier transform of `w`, the explicit
coordinate constructor has physical realization `w`. -/
theorem Hs_toL2_HsHalfOfWeightedFourier_eq (w q : FourierL2)
    (hq : (q : ℝ → ℂ) =ᵐ[volume] fun xi =>
      positiveHalfWeight xi * (sobolevFourier w : ℝ → ℂ) xi) :
    Hs.toL2 (by norm_num) (HsHalfOfWeightedFourier q) = w := by
  apply sobolevFourier.injective
  rw [fourier_Hs_toL2, sobolevFourier_HsHalfOfWeightedFourier]
  apply Lp.ext
  filter_upwards [coe_boundedMulCLM negativeHalfWeight
      continuous_negativeHalfWeight 1 (by norm_num)
      norm_negativeHalfWeight_le q, hq] with xi hout hqin
  rw [hout, hqin, ← mul_assoc,
    negativeHalfWeight_mul_positiveHalfWeight, one_mul]

/-- The bundled `H^{1/2}` norm is controlled by the physical mass and
homogeneous half-derivative energy.  This quantitative form is what allows
critical compositions to be passed to zero strongly. -/
theorem enorm_Hs_half_sq_le_mass_add_homogeneous (f : Hs (1 / 2 : ℝ)) :
    ‖f‖ₑ ^ (2 : ℕ) ≤
      ‖Hs.toL2 (by norm_num) f‖ₑ ^ (2 : ℕ) +
        homogeneousFourierEnergy (1 / 2 : ℝ)
          (Hs.toL2 (by norm_num) f) := by
  let w : FourierL2 := Hs.toL2 (by norm_num) f
  have hfourier := congrArg (fun q : FourierL2 => (q : ℝ → ℂ))
    (fourier_Hs_toL2 f)
  have hcoe := coe_boundedMulCLM negativeHalfWeight
    continuous_negativeHalfWeight 1 (by norm_num)
    norm_negativeHalfWeight_le (sobolevFourier f)
  have hneg : (sobolevFourier w : ℝ → ℂ) =ᵐ[volume]
      fun xi => negativeHalfWeight xi * (sobolevFourier f : ℝ → ℂ) xi := by
    filter_upwards [hcoe] with xi hxi
    rw [hfourier, hxi]
  have hpos : (sobolevFourier f : ℝ → ℂ) =ᵐ[volume]
      fun xi => positiveHalfWeight xi * (sobolevFourier w : ℝ → ℂ) xi := by
    filter_upwards [hneg] with xi hxi
    rw [hxi, ← mul_assoc, mul_comm (positiveHalfWeight xi),
      negativeHalfWeight_mul_positiveHalfWeight]
    simp
  have hsqrt (xi : ℝ) : Real.sqrt (1 + xi ^ 2) ≤ 1 + |xi| := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg xi, abs_nonneg xi, sq_abs xi]
  have hpoint : ∀ᵐ xi : ℝ ∂volume,
      ‖(sobolevFourier f : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) ≤
        ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) +
          ENNReal.ofReal |xi| *
            ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hpos] with xi hxi
    rw [hxi, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hposnorm : ‖positiveHalfWeight xi‖ =
        (1 + xi ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [positiveHalfWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hpossq : ‖positiveHalfWeight xi‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (1 + xi ^ 2)) := by
      rw [← ofReal_norm, hposnorm,
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.rpow_mul]
      norm_num
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        Real.sqrt_eq_rpow]
    rw [hpossq]
    calc
      ENNReal.ofReal (Real.sqrt (1 + xi ^ 2)) *
          ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (1 + |xi|) *
          ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
          gcongr
          exact hsqrt xi
      _ = _ := by
        rw [ENNReal.ofReal_add (by norm_num) (abs_nonneg xi)]
        norm_num
        ring
  have hleft : ‖f‖ₑ ^ (2 : ℕ) =
      ∫⁻ xi : ℝ, ‖(sobolevFourier f : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
    rw [← LinearIsometryEquiv.enorm_map sobolevFourier, Lp.enorm_def,
      ← ENNReal.rpow_natCast]
    simpa using (eLpNorm_nnreal_pow_eq_lintegral
      (f := (sobolevFourier f : ℝ → ℂ)) (μ := volume)
      (p := (2 : NNReal)) (by norm_num))
  have hmass : ‖w‖ₑ ^ (2 : ℕ) =
      ∫⁻ xi : ℝ, ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
    rw [← LinearIsometryEquiv.enorm_map sobolevFourier, Lp.enorm_def,
      ← ENNReal.rpow_natCast]
    simpa using (eLpNorm_nnreal_pow_eq_lintegral
      (f := (sobolevFourier w : ℝ → ℂ)) (μ := volume)
      (p := (2 : NNReal)) (by norm_num))
  rw [hleft, hmass, homogeneousFourierEnergy]
  rw [← lintegral_add_left']
  · exact lintegral_mono_ae (by
      filter_upwards [hpoint] with xi hxi
      simpa [enorm_eq_nnnorm, ENNReal.rpow_two, pow_two] using hxi)
  · exact (Lp.aestronglyMeasurable (sobolevFourier w)).enorm.pow_const 2

/-- Any physical `L²` function with finite homogeneous half-derivative energy
is the physical realization of a bundled `H^{1/2}` element. -/
theorem exists_Hs_half_of_homogeneousFourierEnergy_lt_top
    (w : FourierL2)
    (hw : homogeneousFourierEnergy (1 / 2 : ℝ) w < ⊤) :
    ∃ f : Hs (1 / 2 : ℝ), Hs.toL2 (by norm_num) f = w := by
  let q : ℝ → ℂ := fun xi =>
    positiveHalfWeight xi * (sobolevFourier w : ℝ → ℂ) xi
  have hqmeas : AEStronglyMeasurable q volume :=
    continuous_positiveHalfWeight.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (sobolevFourier w))
  have hsqrt (xi : ℝ) : Real.sqrt (1 + xi ^ 2) ≤ 1 + |xi| := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg xi, abs_nonneg xi, sq_abs xi]
  have hpoint : ∀ᵐ xi : ℝ ∂volume,
      ‖q xi‖ₑ ^ (2 : ℝ) ≤
        ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) +
        ENNReal.ofReal |xi| *
          ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
    filter_upwards with xi
    have hposnorm : ‖positiveHalfWeight xi‖ =
        (1 + xi ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [positiveHalfWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hpossq : ‖positiveHalfWeight xi‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (1 + xi ^ 2)) := by
      rw [← ofReal_norm, hposnorm,
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.rpow_mul]
      norm_num
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        Real.sqrt_eq_rpow]
    dsimp only [q]
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hpossq]
    calc
      ENNReal.ofReal (Real.sqrt (1 + xi ^ 2)) *
          ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (1 + |xi|) *
          ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
        gcongr
        exact hsqrt xi
      _ = _ := by
        rw [ENNReal.ofReal_add (by norm_num) (abs_nonneg xi)]
        norm_num
        ring
  have hmass :
      (∫⁻ xi : ℝ, ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Lp.memLp (sobolevFourier w)).2
  have hhom :
      (∫⁻ xi : ℝ, ENNReal.ofReal |xi| *
        ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa [homogeneousFourierEnergy, enorm_eq_nnnorm,
      ENNReal.rpow_two, pow_two] using hw
  have hsum :
      (∫⁻ xi : ℝ,
        ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) +
        ENNReal.ofReal |xi| *
          ‖(sobolevFourier w : ℝ → ℂ) xi‖ₑ ^ (2 : ℝ)) < ⊤ := by
    rw [lintegral_add_left']
    · exact ENNReal.add_lt_top.mpr ⟨hmass, hhom⟩
    · exact (Lp.aestronglyMeasurable (sobolevFourier w)).enorm.pow_const 2
  have hqint : (∫⁻ xi : ℝ, ‖q xi‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono_ae hpoint).trans_lt hsum
  have hqmem : MemLp q 2 volume := by
    refine ⟨hqmeas, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hqint.ne
  let qLp : FourierL2 := hqmem.toLp q
  let f : Hs (1 / 2 : ℝ) := sobolevFourier.symm qLp
  refine ⟨f, ?_⟩
  apply sobolevFourier.injective
  rw [fourier_Hs_toL2]
  change boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
      (by norm_num) norm_negativeHalfWeight_le (sobolevFourier f) =
    sobolevFourier w
  rw [show sobolevFourier f = qLp by
    dsimp [f]
    rw [LinearIsometryEquiv.apply_symm_apply]]
  apply Lp.ext
  filter_upwards [coe_boundedMulCLM negativeHalfWeight
      continuous_negativeHalfWeight 1 (by norm_num)
      norm_negativeHalfWeight_le qLp,
    hqmem.coeFn_toLp] with xi hout hqcoe
  rw [hout, hqcoe]
  dsimp [q]
  rw [← mul_assoc, negativeHalfWeight_mul_positiveHalfWeight, one_mul]

lemma tempered_eq_of_fourier_eq {S T : 𝓢'(ℝ, ℂ)} (h : 𝓕 S = 𝓕 T) : S = T := by
  calc
    S = 𝓕⁻ (𝓕 S) := (FourierTransform.fourierInv_fourier_eq S).symm
    _ = 𝓕⁻ (𝓕 T) := congrArg (fun U : 𝓢'(ℝ, ℂ) => 𝓕⁻ U) h
    _ = T := FourierTransform.fourierInv_fourier_eq T

lemma fourier_besselNegativeHalf_toTemperedDistribution (u : FourierL2) :
    𝓕 (TemperedDistribution.besselPotential ℝ ℂ (-(1 / 2 : ℝ))
      (MeasureTheory.Lp.toTemperedDistribution u)) =
      MeasureTheory.Lp.toTemperedDistribution
        (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
          norm_negativeHalfWeight_le (sobolevFourier u)) := by
  rw [TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  have hw : (fun x : ℝ =>
      (((1 + ‖x‖ ^ 2) ^ ((-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) =
      negativeHalfWeight := by
    funext ξ
    norm_num [negativeHalfWeight]
  rw [hw]
  rw [← toTemperedDistribution_boundedMulCLM negativeHalfWeight
    continuous_negativeHalfWeight hasTemperateGrowth_negativeHalfWeight]
  rw [sobolevFourier_eq_fourier]

private def derivativeCoordinate : Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)) :=
  sobolevFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM derivativeCoordinateSymbol continuous_derivativeCoordinateSymbol
      (2 * Real.pi) (by positivity) norm_derivativeCoordinateSymbol_le).comp
        sobolevFourier.toContinuousLinearEquiv.toContinuousLinearMap)

private lemma fourier_derivativeCoordinate (f : Hs (1 / 2 : ℝ)) :
    sobolevFourier (derivativeCoordinate f) =
      boundedMulCLM derivativeCoordinateSymbol continuous_derivativeCoordinateSymbol
        (2 * Real.pi) (by positivity) norm_derivativeCoordinateSymbol_le
        (sobolevFourier f) := by
  simp [derivativeCoordinate]

private def quotientCoordinate (h : ℝ) :
    Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)) :=
  sobolevFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
      (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h)).comp
        sobolevFourier.toContinuousLinearEquiv.toContinuousLinearMap)

private lemma norm_quotientCoordinate_le (h : ℝ) (f : Hs (1 / 2 : ℝ)) :
    ‖quotientCoordinate h f‖ ≤ 2 * Real.pi * ‖f‖ := by
  change ‖sobolevFourier.symm
      (boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
        (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h)
        (sobolevFourier f))‖ ≤ 2 * Real.pi * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  calc
    ‖boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
        (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h)
        (sobolevFourier f)‖ ≤
        ‖boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
          (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h)‖ *
          ‖sobolevFourier f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * Real.pi) * ‖sobolevFourier f‖ := by
      gcongr
      exact norm_boundedMulCLM_le _ _ _ _ _
    _ = 2 * Real.pi * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_translationPhase_zero (ξ : ℝ) :
    HasDerivAt (fun h => translationPhase h ξ)
      ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) 0 := by
  unfold translationPhase
  have hr : HasDerivAt (fun h : ℝ => h * (2 * Real.pi * ξ)) (2 * Real.pi * ξ) 0 :=
    hasDerivAt_mul_const (x := (0 : ℝ)) (2 * Real.pi * ξ)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hr
  have hlin : HasDerivAt (fun h : ℝ => Complex.I * ((h * (2 * Real.pi * ξ) : ℝ) : ℂ))
      (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) 0 := by
    simpa [Function.comp_def] using hc.const_mul Complex.I
  simpa [mul_comm] using hlin.cexp

private lemma tendsto_quotientCoordinateSymbol (ξ : ℝ) :
    Tendsto (fun h => quotientCoordinateSymbol h ξ) (nhdsWithin 0 {0}ᶜ)
      (𝓝 (derivativeCoordinateSymbol ξ)) := by
  have hs := (hasDerivAt_translationPhase_zero ξ).tendsto_slope_zero
  have hdiv := hs.div_const ((((Real.sqrt (1 + ξ ^ 2) : ℝ) : ℂ)))
  convert hdiv using 1 <;>
    simp [quotientCoordinateSymbol, derivativeCoordinateSymbol, normalizedFrequency,
      translationPhase, smul_eq_mul] <;>
    push_cast <;> ring

private lemma tendsto_quotientCoordinate (f : Hs (1 / 2 : ℝ)) :
    Tendsto (fun h => quotientCoordinate h f) (nhdsWithin 0 {0}ᶜ)
      (𝓝 (derivativeCoordinate f)) := by
  let g : FourierL2 := sobolevFourier f
  have hinner : Tendsto (fun h =>
      boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
        (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h) g)
      (nhdsWithin 0 {0}ᶜ)
      (𝓝 (boundedMulCLM derivativeCoordinateSymbol continuous_derivativeCoordinateSymbol
        (2 * Real.pi) (by positivity) norm_derivativeCoordinateSymbol_le g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    let r : ℝ → ℝ → ℂ := fun h ξ =>
      (quotientCoordinateSymbol h ξ - derivativeCoordinateSymbol ξ) * (g : ℝ → ℂ) ξ
    have hraw (h : ℝ) :
        eLpNorm
          ((boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
              (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h) g : ℝ → ℂ) -
            (boundedMulCLM derivativeCoordinateSymbol continuous_derivativeCoordinateSymbol
              (2 * Real.pi) (by positivity) norm_derivativeCoordinateSymbol_le g : ℝ → ℂ))
            2 volume = eLpNorm (r h) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [coe_boundedMulCLM (quotientCoordinateSymbol h)
        (continuous_quotientCoordinateSymbol h) (2 * Real.pi) (by positivity)
        (norm_quotientCoordinateSymbol_le h) g,
        coe_boundedMulCLM derivativeCoordinateSymbol continuous_derivativeCoordinateSymbol
          (2 * Real.pi) (by positivity) norm_derivativeCoordinateSymbol_le g]
        with ξ hq hd
      simp only [Pi.sub_apply, hq, hd]
      dsimp [r]
      ring
    simp_rw [hraw]
    have hmeas : ∀ h : ℝ, AEMeasurable (fun ξ => ‖r h ξ‖ₑ ^ (2 : ℝ)) volume := by
      intro h
      apply AEMeasurable.pow_const
      apply AEStronglyMeasurable.enorm
      exact ((continuous_quotientCoordinateSymbol h).aestronglyMeasurable.sub
        continuous_derivativeCoordinateSymbol.aestronglyMeasurable).mul
          (Lp.aestronglyMeasurable g)
    have hbound : ∀ h : ℝ, ∀ᵐ ξ : ℝ ∂volume,
        ‖r h ξ‖ₑ ^ (2 : ℝ) ≤
          ENNReal.ofReal ((4 * Real.pi) ^ 2) * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
      intro h
      filter_upwards with ξ
      have hdiff : ‖quotientCoordinateSymbol h ξ - derivativeCoordinateSymbol ξ‖ ≤
          4 * Real.pi := by
        calc
          _ ≤ ‖quotientCoordinateSymbol h ξ‖ + ‖derivativeCoordinateSymbol ξ‖ :=
            norm_sub_le _ _
          _ ≤ 2 * Real.pi + 2 * Real.pi := by
            gcongr
            · exact norm_quotientCoordinateSymbol_le h ξ
            · exact norm_derivativeCoordinateSymbol_le ξ
          _ = 4 * Real.pi := by ring
      have hdiffe : ‖quotientCoordinateSymbol h ξ - derivativeCoordinateSymbol ξ‖ₑ ≤
          ENNReal.ofReal (4 * Real.pi) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hdiff
      dsimp [r]
      rw [enorm_mul]
      calc
        (‖quotientCoordinateSymbol h ξ - derivativeCoordinateSymbol ξ‖ₑ *
            ‖(g : ℝ → ℂ) ξ‖ₑ) ^ (2 : ℝ) =
            ‖quotientCoordinateSymbol h ξ - derivativeCoordinateSymbol ξ‖ₑ ^ (2 : ℝ) *
              ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ ≤ (ENNReal.ofReal (4 * Real.pi)) ^ (2 : ℝ) *
              ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by gcongr
        _ = ENNReal.ofReal ((4 * Real.pi) ^ 2) *
              ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
          congr 1
          rw [ENNReal.rpow_two]
          exact (ENNReal.ofReal_pow (by positivity : 0 ≤ 4 * Real.pi) 2).symm
    have hfin : (∫⁻ ξ : ℝ, ENNReal.ofReal ((4 * Real.pi) ^ 2) *
        ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂volume) ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp g).2).ne
    have hpoint : ∀ ξ : ℝ, Tendsto (fun h => ‖r h ξ‖ₑ ^ (2 : ℝ))
        (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
      intro ξ
      have hr : Tendsto (fun h => r h ξ) (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
        have hs : Tendsto
            (fun h => quotientCoordinateSymbol h ξ - derivativeCoordinateSymbol ξ)
            (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
          simpa using (tendsto_quotientCoordinateSymbol ξ).sub
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => derivativeCoordinateSymbol ξ)
              (nhdsWithin 0 {0}ᶜ) (𝓝 (derivativeCoordinateSymbol ξ)))
        simpa [r] using hs.mul_const ((g : ℝ → ℂ) ξ)
      convert
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hr.enorm using 1 <;>
        simp [Function.comp_def]
    have hint := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := volume) (l := nhdsWithin 0 {0}ᶜ)
      (F := fun h ξ => ‖r h ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun ξ => ENNReal.ofReal ((4 * Real.pi) ^ 2) *
        ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ))
      (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound) hfin
      (Filter.Eventually.of_forall hpoint)
    simp only [lintegral_zero] at hint
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
      ENNReal.toReal_ofNat, one_div]
    convert
      (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hint using 1 <;>
      simp [Function.comp_def, ENNReal.zero_rpow_of_pos
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
  have hout := sobolevFourier.symm.continuous.tendsto _ |>.comp hinner
  simpa [quotientCoordinate, derivativeCoordinate, g, Function.comp_def] using hout

private def translateL2LI (h : ℝ) : FourierL2 →ₗᵢ[ℂ] FourierL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + h)
    (MeasureTheory.measurePreserving_add_right volume h)

lemma coe_translateL2 (h : ℝ) (f : FourierL2) :
    (translateL2 h f : ℝ → ℂ) =ᵐ[volume] fun x => (f : ℝ → ℂ) (x + h) := by
  unfold translateL2
  exact MemLp.coeFn_toLp _

lemma translateL2LI_apply (h : ℝ) (f : FourierL2) :
    translateL2LI h f = translateL2 h f := by
  change Lp.compMeasurePreserving (fun x : ℝ => x + h)
    (MeasureTheory.measurePreserving_add_right volume h) f = translateL2 h f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      (MeasureTheory.measurePreserving_add_right volume h),
    coe_translateL2 h f] with x hli ht
  rw [hli, ht]
  rfl

/-- Translation preserves the extended norm on the canonical `L²` model. -/
lemma enorm_translateL2 (h : ℝ) (f : FourierL2) :
    ‖translateL2 h f‖ₑ = ‖f‖ₑ := by
  rw [← translateL2LI_apply h f]
  exact LinearIsometry.enorm_map (translateL2LI h) f

lemma norm_translationPhase (h ξ : ℝ) : ‖translationPhase h ξ‖ = 1 := by
  unfold translationPhase
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma norm_translationPhase_le (h ξ : ℝ) : ‖translationPhase h ξ‖ ≤ 1 := by
  rw [norm_translationPhase]

private def translateSchwartz (h : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => x + h) (by fun_prop) (by
    refine ⟨1, 1 + |h|, fun x => ?_⟩
    norm_num
    calc
      |x| = |(x + h) - h| := by ring_nf
      _ ≤ |x + h| + |h| := abs_sub _ _
      _ ≤ (1 + |h|) * (1 + |x + h|) := by
        nlinarith [abs_nonneg h, abs_nonneg (x + h)])

private lemma translateSchwartz_apply (h : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    translateSchwartz h φ x = φ (x + h) := rfl

private lemma translateL2_schwartz (h : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    translateL2 h (φ.toLp 2 volume) = (translateSchwartz h φ).toLp 2 volume := by
  have hφshift : ∀ᵐ x : ℝ ∂volume,
      (φ.toLp 2 volume : ℝ → ℂ) (x + h) = φ (x + h) := by
    change (fun x : ℝ => x + h) ⁻¹'
      {y | (φ.toLp 2 volume : ℝ → ℂ) y = φ y} ∈ ae volume
    exact (MeasureTheory.measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
      (φ.coeFn_toLp 2 volume)
  apply Lp.ext
  filter_upwards [coe_translateL2 h (φ.toLp 2 volume),
    (translateSchwartz h φ).coeFn_toLp 2 volume, hφshift]
    with x ht hψ hφ
  rw [ht, hψ, translateSchwartz_apply, hφ]

private lemma fourier_translateL2_schwartz (h : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    sobolevFourier (translateL2 h (φ.toLp 2 volume)) =
      boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
        (norm_translationPhase_le h) (sobolevFourier (φ.toLp 2 volume)) := by
  rw [translateL2_schwartz]
  change 𝓕 ((translateSchwartz h φ).toLp 2 volume) =
    boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
      (norm_translationPhase_le h) (𝓕 (φ.toLp 2 volume))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (translateSchwartz h φ)).coeFn_toLp 2 volume,
    coe_boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1
      (by norm_num) (norm_translationPhase_le h) ((𝓕 φ).toLp 2 volume),
    (𝓕 φ).coeFn_toLp 2 volume] with ξ hleft hmul hright
  rw [hleft, hmul, hright]
  have hclassic := Fourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (φ : ℝ → ℂ) h
  have hpoint := congrFun hclassic ξ
  change 𝓕 ((φ : ℝ → ℂ) ∘ fun x => x + h) ξ =
    translationPhase h ξ * 𝓕 (φ : ℝ → ℂ) ξ
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  change Fourier.fourierIntegral Real.fourierChar volume
      ((φ : ℝ → ℂ) ∘ fun x => x + h) ξ =
    translationPhase h ξ *
      Fourier.fourierIntegral Real.fourierChar volume (φ : ℝ → ℂ) ξ
  rw [hpoint]
  unfold translationPhase
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  push_cast
  ring

lemma fourier_translateL2 (h : ℝ) (f : FourierL2) :
    sobolevFourier (translateL2 h f) =
      boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
        (norm_translationPhase_le h) (sobolevFourier f) := by
  let L : FourierL2 →L[ℂ] FourierL2 :=
    sobolevFourier.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (translateL2LI h).toContinuousLinearMap
  let R : FourierL2 →L[ℂ] FourierL2 :=
    (boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
      (norm_translationPhase_le h)).comp
        sobolevFourier.toContinuousLinearEquiv.toContinuousLinearMap
  have hLR : L = R := by
    have hdense : DenseRange (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume) :=
      SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
    have hfun : (L : FourierL2 → FourierL2) = (R : FourierL2 → FourierL2) :=
      hdense.equalizer L.continuous R.continuous (by
        funext φ
        change L (φ.toLp 2 volume) = R (φ.toLp 2 volume)
        simpa [L, R, translateL2LI_apply] using fourier_translateL2_schwartz h φ)
    exact DFunLike.ext _ _ (fun x => congrFun hfun x)
  have happ := congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A f) hLR
  simpa [L, R, translateL2LI_apply] using happ

/-- Pointwise almost-everywhere form of the Fourier translation law. -/
lemma coe_fourier_translateL2 (h : ℝ) (f : FourierL2) :
    (sobolevFourier (translateL2 h f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => translationPhase h ξ * (sobolevFourier f : ℝ → ℂ) ξ := by
  rw [fourier_translateL2]
  exact coe_boundedMulCLM (translationPhase h) (continuous_translationPhase h)
    1 (by norm_num) (norm_translationPhase_le h) (sobolevFourier f)

private lemma besselNegativeHalf_lineDeriv_Hs (f : Hs (1 / 2 : ℝ)) :
    TemperedDistribution.besselPotential ℝ ℂ (-(1 / 2 : ℝ))
        (LineDeriv.lineDerivOp (1 : ℝ) (Hs.toTempered (1 / 2 : ℝ) f)) =
      MeasureTheory.Lp.toTemperedDistribution (derivativeCoordinate f) := by
  apply tempered_eq_of_fourier_eq
  rw [TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
    TemperedDistribution.fourier_lineDerivOp_eq, fourier_Hs_toTempered,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  rw [← sobolevFourier_eq_fourier, fourier_derivativeCoordinate]
  rw [toTemperedDistribution_boundedMulCLM derivativeCoordinateSymbol
    continuous_derivativeCoordinateSymbol hasTemperateGrowth_derivativeCoordinateSymbol]
  have hw : (fun x : ℝ =>
      (((1 + ‖x‖ ^ 2) ^ ((-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) =
      negativeHalfWeight := by
    funext ξ
    norm_num [negativeHalfWeight]
  have hx : (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)) =
      fun x : ℝ => ((x : ℝ) : ℂ) := by
    funext ξ
    simp
  rw [hw, hx, map_smul]
  have hxt : (fun x : ℝ => ((x : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      hasTemperateGrowth_negativeHalfWeight hxt,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (hasTemperateGrowth_negativeHalfWeight.mul hxt)
      hasTemperateGrowth_negativeHalfWeight]
  change ((2 * (Real.pi : ℂ) * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ
        ((negativeHalfWeight * fun x : ℝ => ((x : ℝ) : ℂ)) * negativeHalfWeight))
      (MeasureTheory.Lp.toTemperedDistribution (sobolevFourier f)) = _
  rw [← TemperedDistribution.smulLeftCLM_smul
    ((hasTemperateGrowth_negativeHalfWeight.mul hxt).mul
      hasTemperateGrowth_negativeHalfWeight)]
  congr 2
  funext ξ
  rw [derivativeCoordinateSymbol_factor]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  push_cast
  ring

private def physicalQuotient (h : ℝ) (f : Hs (1 / 2 : ℝ)) : FourierL2 :=
  ((h : ℂ)⁻¹) •
    (translateL2 h (Hs.toL2 (by norm_num) f) - Hs.toL2 (by norm_num) f)

private lemma negativeHalf_fourier_physicalQuotient_eq (h : ℝ)
    (f : Hs (1 / 2 : ℝ)) :
    boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
        norm_negativeHalfWeight_le (sobolevFourier (physicalQuotient h f)) =
      sobolevFourier (quotientCoordinate h f) := by
  rw [physicalQuotient, map_smul, map_sub, fourier_translateL2, fourier_Hs_toL2]
  change _ = sobolevFourier (sobolevFourier.symm
    (boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
      (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h)
      (sobolevFourier f)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [coe_boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
      (by norm_num) norm_negativeHalfWeight_le
      (((h : ℂ)⁻¹) •
        (boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
            (norm_translationPhase_le h)
            (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
              norm_negativeHalfWeight_le (sobolevFourier f)) -
          boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
            norm_negativeHalfWeight_le (sobolevFourier f))),
    Lp.coeFn_smul ((h : ℂ)⁻¹)
      (boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
          (norm_translationPhase_le h)
          (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
            norm_negativeHalfWeight_le (sobolevFourier f)) -
        boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
          norm_negativeHalfWeight_le (sobolevFourier f)),
    Lp.coeFn_sub
      (boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1 (by norm_num)
        (norm_translationPhase_le h)
        (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
          norm_negativeHalfWeight_le (sobolevFourier f)))
      (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
        norm_negativeHalfWeight_le (sobolevFourier f)),
    coe_boundedMulCLM (translationPhase h) (continuous_translationPhase h) 1
      (by norm_num) (norm_translationPhase_le h)
      (boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1 (by norm_num)
        norm_negativeHalfWeight_le (sobolevFourier f)),
    coe_boundedMulCLM negativeHalfWeight continuous_negativeHalfWeight 1
      (by norm_num) norm_negativeHalfWeight_le (sobolevFourier f),
    coe_boundedMulCLM (quotientCoordinateSymbol h) (continuous_quotientCoordinateSymbol h)
      (2 * Real.pi) (by positivity) (norm_quotientCoordinateSymbol_le h)
      (sobolevFourier f)] with ξ hout hsmul hsub hphase hhalf hquot
  rw [hout, hsmul, hquot]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hphase, hhalf]
  simp [negativeHalfWeight, quotientCoordinateSymbol, normalizedFrequency]
  have hr : ((1 + ξ ^ 2) ^ (-(1 : ℝ) / 4)) ^ (2 : ℕ) *
      Real.sqrt (1 + ξ ^ 2) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + ξ ^ 2),
      Real.sqrt_eq_rpow,
      ← Real.rpow_add (by positivity : 0 < 1 + ξ ^ 2)]
    norm_num
  have hrc : (((1 + ξ ^ 2) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) ^ (2 : ℕ) *
      ((Real.sqrt (1 + ξ ^ 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hr
  field_simp [ne_of_gt (sqrt_one_add_sq_pos ξ)]
  ring_nf at hrc ⊢
  rw [hrc]
  ring

private lemma besselNegativeHalf_physicalQuotient (h : ℝ)
    (f : Hs (1 / 2 : ℝ)) :
    TemperedDistribution.besselPotential ℝ ℂ (-(1 / 2 : ℝ))
        (MeasureTheory.Lp.toTemperedDistribution (physicalQuotient h f)) =
      MeasureTheory.Lp.toTemperedDistribution (quotientCoordinate h f) := by
  apply tempered_eq_of_fourier_eq
  rw [fourier_besselNegativeHalf_toTemperedDistribution,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  congr 1
  rw [← sobolevFourier_eq_fourier]
  exact negativeHalf_fourier_physicalQuotient_eq h f

private lemma derivativeCoordinate_toTempered (f : Hs (1 / 2 : ℝ)) :
    Hs.toTempered (-(1 / 2 : ℝ)) (derivativeCoordinate f) =
      LineDeriv.lineDerivOp (1 : ℝ) (Hs.toTempered (1 / 2 : ℝ) f) := by
  rw [Hs.toTempered, besselMultiplier]
  norm_num
  change TemperedDistribution.besselPotential ℝ ℂ (1 / 2 : ℝ)
      (MeasureTheory.Lp.toTemperedDistribution (derivativeCoordinate f)) = _
  exact (TemperedDistribution.besselPotential_neg_apply_eq_iff (1 / 2 : ℝ)
    (LineDeriv.lineDerivOp (1 : ℝ) (Hs.toTempered (1 / 2 : ℝ) f))
    (MeasureTheory.Lp.toTemperedDistribution (derivativeCoordinate f))).mp
      (besselNegativeHalf_lineDeriv_Hs f)

private lemma quotientCoordinate_toTempered (h : ℝ) (f : Hs (1 / 2 : ℝ)) :
    Hs.toTempered (-(1 / 2 : ℝ)) (quotientCoordinate h f) =
      MeasureTheory.Lp.toTemperedDistribution (physicalQuotient h f) := by
  rw [Hs.toTempered, besselMultiplier]
  norm_num
  change TemperedDistribution.besselPotential ℝ ℂ (1 / 2 : ℝ)
      (MeasureTheory.Lp.toTemperedDistribution (quotientCoordinate h f)) = _
  exact (TemperedDistribution.besselPotential_neg_apply_eq_iff (1 / 2 : ℝ)
    (MeasureTheory.Lp.toTemperedDistribution (physicalQuotient h f))
    (MeasureTheory.Lp.toTemperedDistribution (quotientCoordinate h f))).mp
      (besselNegativeHalf_physicalQuotient h f)

/-- `lem:translation-dq`: strong `H^{1/2} → H^{-1/2}` difference quotients. -/
theorem translation_dq :
  ∃ D : Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)),
  ∃ Q : ℝ → Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)),
    (∀ f,
      Hs.toTempered (-(1 / 2 : ℝ)) (D f) =
        LineDeriv.lineDerivOp (1 : ℝ) (Hs.toTempered (1 / 2 : ℝ) f)) ∧
    (∀ h : ℝ, h ≠ 0 → ∀ f,
      Hs.toTempered (-(1 / 2 : ℝ)) (Q h f) =
        MeasureTheory.Lp.toTemperedDistribution
          (((h : ℂ)⁻¹) •
            (translateL2 h (Hs.toL2 (by norm_num) f) - Hs.toL2 (by norm_num) f))) ∧
    (∀ f, Tendsto (fun h : ℝ => Q h f)
      (nhdsWithin 0 {0}ᶜ) (𝓝 (D f))) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, h ≠ 0 → ∀ f,
      ‖Q h f‖ ≤ C * ‖f‖ := by
  refine ⟨derivativeCoordinate, quotientCoordinate, derivativeCoordinate_toTempered,
    ?_, tendsto_quotientCoordinate, 2 * Real.pi, by positivity, ?_⟩
  · intro h _ f
    simpa [physicalQuotient] using quotientCoordinate_toTempered h f
  · intro h _ f
    exact norm_quotientCoordinate_le h f

/-- `lem:H1-C0`: continuous representative, vanishing tails, and the sharp 1D bound. -/
theorem H1_C0 (f f' : ℝ → ℂ) (hf : MemLp f 2 volume) (hf' : MemLp f' 2 volume)
    (hFTC : ∀ a b : ℝ, f b - f a = ∫ x in a..b, f' x) :
  ∃ g : ℝ → ℂ,
    Continuous g ∧ f =ᵐ[volume] g ∧
    Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0) ∧
    (⨆ x : ℝ, ‖g x‖₊) ^ (2 : ℕ) ≤
      2 * eLpNorm f 2 volume * eLpNorm f' 2 volume := by
  have hf'loc : LocallyIntegrable f' volume := hf'.locallyIntegrable (by norm_num)
  have hrepr : f = fun x => f 0 + ∫ y in (0 : ℝ)..x, f' y := by
    funext x
    rw [← hFTC 0 x]
    abel
  have hfcont : Continuous f := by
    rw [hrepr]
    exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hf'loc.integrableOn_isCompact isCompact_uIcc |>.intervalIntegrable) 0)
  have hfderiv : ∀ᵐ x : ℝ ∂volume, HasDerivAt f (f' x) x := by
    rw [hrepr]
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf'loc] with x hx
    simpa using hx 0
  let q : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let q' : ℝ → ℝ := fun x => 2 * @inner ℝ ℂ _ (f x) (f' x)
  have hqderiv : ∀ᵐ x : ℝ ∂volume, HasDerivAt q (q' x) x := by
    filter_upwards [hfderiv] with x hx
    exact hx.norm_sq
  have hf'int (a b : ℝ) : IntervalIntegrable f' volume a b :=
    hf'loc.integrableOn_isCompact isCompact_uIcc |>.intervalIntegrable
  have hreFTC (a b : ℝ) : (f b).re - (f a).re = ∫ x in a..b, (f' x).re := by
    have hint : (∫ x in a..b, (f' x).re) = (∫ x in a..b, f' x).re := by
      simpa only [RCLike.re_to_complex] using
        (intervalIntegral.intervalIntegral_re (hf'int a b))
    calc
      (f b).re - (f a).re = (f b - f a).re := by simp
      _ = (∫ x in a..b, f' x).re := congrArg Complex.re (hFTC a b)
      _ = ∫ x in a..b, (f' x).re := hint.symm
  have himFTC (a b : ℝ) : (f b).im - (f a).im = ∫ x in a..b, (f' x).im := by
    have hint : (∫ x in a..b, (f' x).im) = (∫ x in a..b, f' x).im := by
      simpa only [RCLike.im_to_complex] using
        (intervalIntegral.intervalIntegral_im (hf'int a b))
    calc
      (f b).im - (f a).im = (f b - f a).im := by simp
      _ = (∫ x in a..b, f' x).im := congrArg Complex.im (hFTC a b)
      _ = ∫ x in a..b, (f' x).im := hint.symm
  have hqac (a b : ℝ) : AbsolutelyContinuousOnInterval q a b := by
    have hre'int : IntervalIntegrable (fun x => (f' x).re) volume a b :=
      (hf'.re.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc
        |>.intervalIntegrable
    have him'int : IntervalIntegrable (fun x => (f' x).im) volume a b :=
      (hf'.im.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc
        |>.intervalIntegrable
    have hreac : AbsolutelyContinuousOnInterval (fun x => (f x).re) a b := by
      have hrep : (fun x => (f x).re) =
          fun x => (f a).re + ∫ y in a..x, (f' y).re := by
        funext x
        rw [← hreFTC a x]
        ring
      rw [hrep]
      exact (LipschitzWith.const (f a).re).lipschitzOnWith.absolutelyContinuousOnInterval.add
        (hre'int.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
    have himac : AbsolutelyContinuousOnInterval (fun x => (f x).im) a b := by
      have hrep : (fun x => (f x).im) =
          fun x => (f a).im + ∫ y in a..x, (f' y).im := by
        funext x
        rw [← himFTC a x]
        ring
      rw [hrep]
      exact (LipschitzWith.const (f a).im).lipschitzOnWith.absolutelyContinuousOnInterval.add
        (him'int.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
    have hcomponents : q = fun x => (f x).re * (f x).re + (f x).im * (f x).im := by
      funext x
      simp [q, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [hcomponents]
    exact (hreac.fun_mul hreac).add (himac.fun_mul himac)
  have hqFTC (a b : ℝ) : q b - q a = ∫ x in a..b, q' x := by
    rw [← (hqac a b).integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqderiv] with x hx _
    exact hx.deriv
  have hinner : MemLp (fun x => @inner ℝ ℂ _ (f x) (f' x)) 1 volume := by
    apply MemLp.of_bilin (fun z w : ℂ => @inner ℝ ℂ _ z w) 1 hf hf'
    · exact hf.1.inner hf'.1
    · filter_upwards with x
      simpa using (nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f x) (f' x))
  have hq'mem : MemLp q' 1 volume := by
    simpa [q'] using hinner.const_mul (2 : ℝ)
  have hq'int : Integrable q' volume := memLp_one_iff_integrable.mp hq'mem
  have hqmem : MemLp q 1 volume := by
    simpa [q, pow_two] using hf.norm.mul' hf.norm
  have hqint : Integrable q volume := memLp_one_iff_integrable.mp hqmem
  have hqnonneg (x : ℝ) : 0 ≤ q x := by simp [q]
  let Lplus : ℝ := q 0 + ∫ x in Ioi (0 : ℝ), q' x
  have hqtopL : Tendsto q atTop (𝓝 Lplus) := by
    have hi := intervalIntegral_tendsto_integral_Ioi (μ := volume) (f := q') 0
      hq'int.integrableOn tendsto_id
    have hlim : Tendsto (fun b => q 0 + ∫ x in (0 : ℝ)..b, q' x) atTop (𝓝 Lplus) := by
      simpa [Lplus] using tendsto_const_nhds.add hi
    apply hlim.congr'
    filter_upwards with b
    rw [← hqFTC 0 b]
    ring
  have hLplus_nonneg : 0 ≤ Lplus :=
    isClosed_Ici.mem_of_tendsto hqtopL (Eventually.of_forall hqnonneg)
  have hLplus : Lplus = 0 := by
    by_contra hne
    have hpos : 0 < Lplus := lt_of_le_of_ne hLplus_nonneg (Ne.symm hne)
    have hev : ∀ᶠ x : ℝ in atTop, Lplus / 2 < q x :=
      hqtopL.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨A, hA⟩ := (eventually_atTop.1 hev)
    have hsubset : Ioi A ⊆ {x : ℝ | Lplus / 2 ≤ ‖q x‖} := by
      intro x hx
      change Lplus / 2 ≤ ‖q x‖
      rw [Real.norm_of_nonneg (hqnonneg x)]
      exact (hA x hx.le).le
    have hfinite := hqint.measure_norm_ge_lt_top (half_pos hpos)
    have hinfinite : volume (Ioi A) = ⊤ := Real.volume_Ioi
    have hle := measure_mono (μ := volume) hsubset
    rw [hinfinite] at hle
    exact (not_lt_of_ge hle) hfinite
  have hqtop : Tendsto q atTop (𝓝 0) := by simpa [hLplus] using hqtopL
  let Lminus : ℝ := q 0 - ∫ x in Iic (0 : ℝ), q' x
  have hqbotL : Tendsto q atBot (𝓝 Lminus) := by
    have hi := intervalIntegral_tendsto_integral_Iic (μ := volume) (f := q') 0
      hq'int.integrableOn tendsto_id
    have hlim : Tendsto (fun a => q 0 - ∫ x in a..(0 : ℝ), q' x) atBot (𝓝 Lminus) := by
      simpa [Lminus] using tendsto_const_nhds.sub hi
    apply hlim.congr'
    filter_upwards with a
    rw [← hqFTC a 0]
    ring
  have hLminus_nonneg : 0 ≤ Lminus :=
    isClosed_Ici.mem_of_tendsto hqbotL (Eventually.of_forall hqnonneg)
  have hLminus : Lminus = 0 := by
    by_contra hne
    have hpos : 0 < Lminus := lt_of_le_of_ne hLminus_nonneg (Ne.symm hne)
    have hev : ∀ᶠ x : ℝ in atBot, Lminus / 2 < q x :=
      hqbotL.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨A, hA⟩ := (eventually_atBot.1 hev)
    have hsubset : Iio A ⊆ {x : ℝ | Lminus / 2 ≤ ‖q x‖} := by
      intro x hx
      change Lminus / 2 ≤ ‖q x‖
      rw [Real.norm_of_nonneg (hqnonneg x)]
      exact (hA x hx.le).le
    have hfinite := hqint.measure_norm_ge_lt_top (half_pos hpos)
    have hinfinite : volume (Iio A) = ⊤ := Real.volume_Iio
    have hle := measure_mono (μ := volume) hsubset
    rw [hinfinite] at hle
    exact (not_lt_of_ge hle) hfinite
  have hqbot : Tendsto q atBot (𝓝 0) := by simpa [hLminus] using hqbotL
  have hftop : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsqrt := hqtop.sqrt
    simpa only [q, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hfbot : Tendsto f atBot (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsqrt := hqbot.sqrt
    simpa only [q, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hqIoi (x : ℝ) : q x = -(∫ y in Ioi x, q' y) := by
    have hi := intervalIntegral_tendsto_integral_Ioi (μ := volume) (f := q') x
      hq'int.integrableOn tendsto_id
    have hlim : Tendsto (fun b => q b - q x) atTop (𝓝 (∫ y in Ioi x, q' y)) := by
      apply hi.congr'
      filter_upwards with b
      exact (hqFTC x b).symm
    have heq : -q x = ∫ y in Ioi x, q' y := by
      simpa using tendsto_nhds_unique (hqtop.sub_const (q x)) hlim
    linarith
  have hq'bound : eLpNorm q' 1 volume ≤
      2 * eLpNorm f 2 volume * eLpNorm f' 2 volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (p := 2) (q := 2) (r := 1) hf.1 hf'.1
      (fun z w : ℂ => 2 * @inner ℝ ℂ _ z w) 2 (by
        filter_upwards with x
        change ‖(2 : ℝ) * @inner ℝ ℂ _ (f x) (f' x)‖ ≤
          (2 : ℝ) * ‖f x‖ * ‖f' x‖
        rw [norm_mul, Real.norm_of_nonneg (by norm_num), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm (f x) (f' x))
          (by norm_num))
    simpa [q'] using h
  let B : ℝ≥0∞ := 2 * eLpNorm f 2 volume * eLpNorm f' 2 volume
  have hBtop : B ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp) (ne_of_lt hf.2)
    · exact ne_of_lt hf'.2
  have hpoint (x : ℝ) : ((‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ≤ B := by
    have hset : ‖∫ y in Ioi x, q' y‖ₑ ≤ eLpNorm q' 1 volume := by
      calc
        ‖∫ y in Ioi x, q' y‖ₑ ≤ ∫⁻ y in Ioi x, ‖q' y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, ‖q' y‖ₑ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
        _ = eLpNorm q' 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    have hqenorm : ENNReal.ofReal (q x) = ‖∫ y in Ioi x, q' y‖ₑ := by
      have hI : (∫ y in Ioi x, q' y) = -q x := by linarith [hqIoi x]
      symm
      calc
        ‖∫ y in Ioi x, q' y‖ₑ = ‖-q x‖ₑ := congrArg (fun r : ℝ => ‖r‖ₑ) hI
        _ = ‖q x‖ₑ := enorm_neg _
        _ = ENNReal.ofReal (q x) := Real.enorm_eq_ofReal (hqnonneg x)
    have htoB : eLpNorm q' 1 volume ≤ B := by simpa [B] using hq'bound
    calc
      (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) = ENNReal.ofReal (q x) := by
        change ‖f x‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (q x)
        simp [q, ENNReal.ofReal_pow]
      _ = ‖∫ y in Ioi x, q' y‖ₑ := hqenorm
      _ ≤ eLpNorm q' 1 volume := hset
      _ ≤ B := htoB
  have hrealpoint (x : ℝ) : ‖f x‖ ^ (2 : ℕ) ≤ B.toReal := by
    have h := ENNReal.toReal_mono hBtop (hpoint x)
    simpa using h
  let bnn : NNReal := ⟨Real.sqrt (B.toReal), Real.sqrt_nonneg _⟩
  have hnorm_le (x : ℝ) : ‖f x‖₊ ≤ bnn := by
    change ‖f x‖ ≤ Real.sqrt (B.toReal)
    exact (Real.le_sqrt (norm_nonneg _) ENNReal.toReal_nonneg).2 (hrealpoint x)
  have hbdd : BddAbove (Set.range fun x : ℝ => ‖f x‖₊) :=
    ⟨bnn, by rintro _ ⟨x, rfl⟩; exact hnorm_le x⟩
  have hbddpow : BddAbove (Set.range fun x : ℝ => ‖f x‖₊ ^ (2 : ℕ)) :=
    ⟨bnn ^ (2 : ℕ), by
      rintro _ ⟨x, rfl⟩
      exact pow_le_pow_left₀ (by positivity) (hnorm_le x) 2⟩
  refine ⟨f, hfcont, Eventually.of_forall (fun _ => rfl), hftop, hfbot, ?_⟩
  change (↑((⨆ x : ℝ, ‖f x‖₊) ^ (2 : ℕ)) : ℝ≥0∞) ≤ B
  calc
    (↑((⨆ x : ℝ, ‖f x‖₊) ^ (2 : ℕ)) : ℝ≥0∞) =
        ↑(⨆ x : ℝ, ‖f x‖₊ ^ (2 : ℕ)) := by rw [NNReal.iSup_pow]
    _ = (⨆ x : ℝ, (↑(‖f x‖₊ ^ (2 : ℕ)) : ℝ≥0∞)) := ENNReal.coe_iSup hbddpow
    _ ≤ B := iSup_le hpoint


private theorem logform_integrable (f : Hs (1 / 2 : ℝ)) (φ : 𝓢(ℝ, ℝ)) :
    Integrable (fun x : ℝ =>
      (SchwartzMap.derivCLM ℝ ℝ φ) x *
        ‖(Hs.toL2 (by norm_num) f : ℝ → ℂ) x‖ ^ 2) volume := by
  let w : FourierL2 := Hs.toL2 (by norm_num) f
  have hw : MemLp (fun x : ℝ => ‖(w : ℝ → ℂ) x‖ ^ 2) 1 volume := by
    simpa [pow_two] using (Lp.memLp w).norm.mul' (Lp.memLp w).norm
  have hd : MemLp (SchwartzMap.derivCLM ℝ ℝ φ : ℝ → ℝ) ⊤ volume :=
    (SchwartzMap.derivCLM ℝ ℝ φ).memLp_top volume
  obtain ⟨C, _, hC⟩ := (SchwartzMap.derivCLM ℝ ℝ φ).decay 0 0
  have hp := (memLp_one_iff_integrable.1 hw).bdd_mul hd.1
    (ae_of_all volume fun x => by simpa using hC x)
  simpa [w, mul_comm] using hp

/-- `lem:realpart-logform`: the real current form is determined by the density. -/
theorem realpart_logform (f : Hs (1 / 2 : ℝ)) :
  ∃ J : 𝓢(ℝ, ℝ) →ₗ[ℝ] ℂ, ∀ φ : 𝓢(ℝ, ℝ),
    (J φ).re =
      -(1 / 2 : ℝ) * ∫ x : ℝ,
        deriv (φ : ℝ → ℝ) x * ‖(Hs.toL2 (by norm_num) f : ℝ → ℂ) x‖ ^ 2 := by
  let J : 𝓢(ℝ, ℝ) →ₗ[ℝ] ℂ :=
    { toFun := fun φ => ((-(1 / 2 : ℝ) * ∫ x : ℝ,
          (SchwartzMap.derivCLM ℝ ℝ φ) x *
            ‖(Hs.toL2 (by norm_num) f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)
      map_add' := by
        intro φ ψ
        simp only [map_add, add_apply, add_mul]
        rw [integral_add (logform_integrable f φ) (logform_integrable f ψ)]
        push_cast
        ring
      map_smul' := by
        intro c φ
        simp only [map_smul, smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        rw [integral_const_mul]
        push_cast
        rw [Complex.real_smul]
        ring }
  refine ⟨J, fun φ => ?_⟩
  simp only [J, LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_re]
  congr 2

/-- `lem:tensor-norm`: L² tensor membership and exact norm factorization. -/
theorem tensor_norm (f g : FourierL2) :
  MemLp (fun p : ℝ × ℝ => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2) 2
      (volume.prod volume) ∧
    eLpNorm (fun p : ℝ × ℝ => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2) 2
      (volume.prod volume) = eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2)
      (volume.prod volume) :=
    (Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd
  have heq : eLpNorm
      (fun p : ℝ × ℝ => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2) 2
      (volume.prod volume) = eLpNorm f 2 volume * eLpNorm g 2 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num [enorm_mul]
    simp_rw [mul_pow]
    rw [lintegral_prod_mul
      ((Lp.aestronglyMeasurable f).enorm.pow_const 2)
      ((Lp.aestronglyMeasurable g).enorm.pow_const 2)]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine ⟨⟨hmeas, ?_⟩, heq⟩
  rw [heq]
  exact ENNReal.mul_lt_top (Lp.memLp f).2 (Lp.memLp g).2

end CubicNLSPhaseRetrieval
