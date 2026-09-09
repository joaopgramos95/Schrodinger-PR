import Lean_Code.HsPairingPhysical
import Lean_Code.FrequencySmoothing

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology
open LineDeriv

noncomputable section
namespace CubicNLSPhaseRetrieval

def regularizedDerivativeSymbol (n : ℕ) (ξ : ℝ) : ℂ :=
  (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * resolventSymbol n ξ

lemma continuous_regularizedDerivativeSymbol (n : ℕ) :
    Continuous (regularizedDerivativeSymbol n) := by
  unfold regularizedDerivativeSymbol
  exact ((Complex.continuous_ofReal.comp
    (continuous_const.mul continuous_id)).mul continuous_const).mul
      (continuous_resolventSymbol n)

lemma norm_regularizedDerivativeSymbol_le (n : ℕ) (ξ : ℝ) :
    ‖regularizedDerivativeSymbol n ξ‖ ≤ 2 * Real.pi * (n + 1 : ℝ) := by
  rw [regularizedDerivativeSymbol, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  rw [abs_mul, abs_of_nonneg hpi]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hden : 0 < 1 + ξ ^ 2 / (n + 1 : ℝ) := by positivity
  have hr : ‖resolventSymbol n ξ‖ =
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ := by
    rw [resolventSymbol, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hden]
  rw [hr]
  have hxi : |ξ| ≤ 1 + ξ ^ 2 := by
    nlinarith [sq_nonneg (|ξ| - 1), sq_abs ξ]
  have hsmall : |ξ| * (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ ≤
      (n + 1 : ℝ) := by
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hden]
    calc
      |ξ| ≤ 1 + ξ ^ 2 := hxi
      _ ≤ (n + 1 : ℝ) + ξ ^ 2 := by
        gcongr
        norm_num
      _ = (n + 1 : ℝ) * (1 + ξ ^ 2 / (n + 1 : ℝ)) := by
        field_simp
  calc
    2 * Real.pi * |ξ| * (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ =
        (2 * Real.pi) *
          (|ξ| * (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹) := by ring
    _ ≤ (2 * Real.pi) * (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hsmall hpi

/-- The physical first spatial derivative of the resolvent-smoothed `L²`
function. -/
def frequencySmoothDerivativeCLM (n : ℕ) : L2 →L[ℂ] L2 :=
  fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMulCLM (regularizedDerivativeSymbol n)
      (continuous_regularizedDerivativeSymbol n)
      (2 * Real.pi * (n + 1 : ℝ)) (by positivity)
      (norm_regularizedDerivativeSymbol_le n)).comp
        fourierL2.toContinuousLinearEquiv.toContinuousLinearMap)

lemma fourier_frequencySmoothDerivativeCLM (n : ℕ) (f : L2) :
    fourierL2 (frequencySmoothDerivativeCLM n f) =
      boundedMulCLM (regularizedDerivativeSymbol n)
        (continuous_regularizedDerivativeSymbol n)
        (2 * Real.pi * (n + 1 : ℝ)) (by positivity)
        (norm_regularizedDerivativeSymbol_le n) (fourierL2 f) := by
  simp [frequencySmoothDerivativeCLM]

lemma coe_fourier_frequencySmoothDerivativeCLM (n : ℕ) (f : L2) :
    (fourierL2 (frequencySmoothDerivativeCLM n f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
        (fourierL2 (frequencySmoothCLM n f) : ℝ → ℂ) ξ := by
  rw [fourier_frequencySmoothDerivativeCLM]
  filter_upwards [coe_boundedMulCLM (regularizedDerivativeSymbol n)
      (continuous_regularizedDerivativeSymbol n)
      (2 * Real.pi * (n + 1 : ℝ)) (by positivity)
      (norm_regularizedDerivativeSymbol_le n) (fourierL2 f),
    coe_fourier_frequencySmoothCLM n f] with ξ hq hw
  rw [hq, hw]
  simp [regularizedDerivativeSymbol]
  ring

lemma lineDeriv_frequencySmooth_toTempered (n : ℕ) (f : L2) :
    LineDeriv.lineDerivOp (1 : ℝ)
        (MeasureTheory.Lp.toTemperedDistribution (frequencySmoothCLM n f)) =
      MeasureTheory.Lp.toTemperedDistribution
        (frequencySmoothDerivativeCLM n f) := by
  apply tempered_eq_of_fourier_eq
  rw [TemperedDistribution.fourier_lineDerivOp_eq,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  ext ψ
  simp only [ContinuousLinearMap.smul_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, smul_eq_mul]
  rw [MeasureTheory.Lp.toTemperedDistribution_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  change (2 * (Real.pi : ℂ) * Complex.I) •
      (∫ x : ℝ, ((SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)) ψ) x) •
          (fourierL2 (frequencySmoothCLM n f) : ℝ → ℂ) x) = _
  rw [← MeasureTheory.integral_smul]
  apply integral_congr_ae
  filter_upwards [coe_fourier_frequencySmoothDerivativeCLM n f] with ξ hξ
  change (2 * (Real.pi : ℂ) * Complex.I) •
      ((SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)) ψ) ξ) •
          (fourierL2 (frequencySmoothCLM n f) : ℝ → ℂ) ξ =
      ψ ξ • (fourierL2 (frequencySmoothDerivativeCLM n f) : ℝ → ℂ) ξ
  rw [hξ]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [smul_eq_mul]
  ring

/-- The physical derivative after multiplication by a Schwartz cutoff. -/
def cutoffDerivativeL2 (chi : SchwartzMap ℝ ℂ) (w q : L2) : L2 :=
  cutoffL2CLM chi q +
    cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ chi) w

lemma lineDeriv_cutoff_toTempered (chi : SchwartzMap ℝ ℂ) (w q : L2)
    (hq : LineDeriv.lineDerivOp (1 : ℝ)
        (MeasureTheory.Lp.toTemperedDistribution w) =
      MeasureTheory.Lp.toTemperedDistribution q) :
    LineDeriv.lineDerivOp (1 : ℝ)
        (MeasureTheory.Lp.toTemperedDistribution (cutoffL2CLM chi w)) =
      MeasureTheory.Lp.toTemperedDistribution
        (cutoffDerivativeL2 chi w q) := by
  ext psi
  let chip : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (chi : ℝ → ℂ) psi
  have hqp := congrArg (fun T : 𝓢'(ℝ, ℂ) => T chip) hq
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply] at hqp ⊢
  have hcutw := coe_cutoffL2CLM chi w
  have hcutq := coe_cutoffL2CLM chi q
  have hcutdw := coe_cutoffL2CLM
    (SchwartzMap.derivCLM ℂ ℂ chi) w
  have hadd := Lp.coeFn_add (cutoffL2CLM chi q)
    (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ chi) w)
  rw [show cutoffDerivativeL2 chi w q =
      cutoffL2CLM chi q +
        cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ chi) w by rfl]
  have hint (phi : SchwartzMap ℝ ℂ) (z : L2) :
      Integrable (fun x : ℝ => phi x • (z : ℝ → ℂ) x) volume := by
    rw [← memLp_one_iff_integrable]
    simpa [smul_eq_mul] using
      (Lp.memLp z).mul' (phi.memLp 2 volume)
  have hrhs :
      (∫ x : ℝ, psi x •
          (((cutoffL2CLM chi q +
            cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ chi) w) : L2) :
              ℝ → ℂ) x) =
        (∫ x : ℝ, psi x • (cutoffL2CLM chi q : ℝ → ℂ) x) +
          ∫ x : ℝ, psi x •
            (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ chi) w : ℝ → ℂ) x := by
    rw [integral_congr_ae (by
      filter_upwards [hadd] with x hx
      rw [hx])]
    simp only [Pi.add_apply, smul_add]
    exact integral_add (hint psi _) (hint psi _)
  have hlhs :
      (∫ x : ℝ, (-LineDeriv.lineDerivOp (1 : ℝ) psi) x •
          (cutoffL2CLM chi w : ℝ → ℂ) x) =
        ∫ x : ℝ, (-LineDeriv.lineDerivOp (1 : ℝ) psi) x •
          (chi x * (w : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards [hcutw] with x hx
    rw [hx]
  have hqterm :
      (∫ x : ℝ, psi x • (cutoffL2CLM chi q : ℝ → ℂ) x) =
        ∫ x : ℝ, psi x • (chi x * (q : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards [hcutq] with x hx
    rw [hx]
  have hdterm :
      (∫ x : ℝ, psi x •
          (cutoffL2CLM (SchwartzMap.derivCLM ℂ ℂ chi) w : ℝ → ℂ) x) =
        ∫ x : ℝ, psi x •
          ((SchwartzMap.derivCLM ℂ ℂ chi) x * (w : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards [hcutdw] with x hx
    rw [hx]
  rw [hlhs, hrhs, hqterm, hdterm]
  have hchip (x : ℝ) : chip x = chi x * psi x := by
    dsimp [chip]
    exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) psi x
  have hdchip (x : ℝ) :
      (LineDeriv.lineDerivOp (1 : ℝ) chip) x =
        (SchwartzMap.derivCLM ℂ ℂ chi) x * psi x +
          chi x * (LineDeriv.lineDerivOp (1 : ℝ) psi) x := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [show (chip : ℝ → ℂ) = fun y => chi y * psi y from funext hchip]
    change fderiv ℝ (fun y : ℝ => chi y * psi y) x 1 = _
    rw [show (fun y : ℝ => chi y * psi y) =
      (chi : ℝ → ℂ) * (psi : ℝ → ℂ) by rfl]
    rw [fderiv_mul chi.differentiableAt psi.differentiableAt]
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_apply_one_eq_deriv]
    rw [SchwartzMap.derivCLM_apply]
    ring
  have hqpL :
      (∫ x : ℝ, (-LineDeriv.lineDerivOp (1 : ℝ) chip) x •
          (w : ℝ → ℂ) x) =
        ∫ x : ℝ,
          (-((SchwartzMap.derivCLM ℂ ℂ chi) x * psi x) •
              (w : ℝ → ℂ) x) +
            (-(chi x * (LineDeriv.lineDerivOp (1 : ℝ) psi) x) •
              (w : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards with x
    change (-(LineDeriv.lineDerivOp (1 : ℝ) chip) x) •
      (w : ℝ → ℂ) x = _
    rw [hdchip x]
    simp only [neg_add_rev, add_smul, neg_smul]
    ring
  have hqpR :
      (∫ x : ℝ, chip x • (q : ℝ → ℂ) x) =
        ∫ x : ℝ, (chi x * psi x) • (q : ℝ → ℂ) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hchip x]
  rw [hqpL, hqpR] at hqp
  have hfirst : Integrable (fun x : ℝ =>
      (-((SchwartzMap.derivCLM ℂ ℂ chi) x * psi x)) •
        (w : ℝ → ℂ) x) volume := by
    have hi := hint
      (SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.derivCLM ℂ ℂ chi : ℝ → ℂ) psi) w
    have hi' : Integrable (fun x : ℝ =>
        ((SchwartzMap.derivCLM ℂ ℂ chi) x * psi x) •
          (w : ℝ → ℂ) x) volume := by
      apply hi.congr
      filter_upwards with x
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp [smul_eq_mul]
    apply hi'.neg.congr
    filter_upwards with x
    simp only [Pi.neg_apply, neg_smul]
  have hsecond : Integrable (fun x : ℝ =>
      (-(chi x * (LineDeriv.lineDerivOp (1 : ℝ) psi) x)) •
        (w : ℝ → ℂ) x) volume := by
    have hi := hint
      (SchwartzMap.smulLeftCLM ℂ (chi : ℝ → ℂ)
        (LineDeriv.lineDerivOp (1 : ℝ) psi)) w
    have hi' : Integrable (fun x : ℝ =>
        (chi x * (LineDeriv.lineDerivOp (1 : ℝ) psi) x) •
          (w : ℝ → ℂ) x) volume := by
      apply hi.congr
      filter_upwards with x
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp [smul_eq_mul]
    apply hi'.neg.congr
    filter_upwards with x
    simp only [Pi.neg_apply, neg_smul]
  rw [integral_add hfirst hsecond] at hqp
  have hfirst_eq :
      (∫ x : ℝ,
          (-((SchwartzMap.derivCLM ℂ ℂ chi) x * psi x)) •
            (w : ℝ → ℂ) x) =
        -(∫ x : ℝ, psi x •
          ((SchwartzMap.derivCLM ℂ ℂ chi) x * (w : ℝ → ℂ) x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp [smul_eq_mul]
    ring
  have hsecond_eq :
      (∫ x : ℝ,
          (-(chi x * (LineDeriv.lineDerivOp (1 : ℝ) psi) x)) •
            (w : ℝ → ℂ) x) =
        ∫ x : ℝ, (-LineDeriv.lineDerivOp (1 : ℝ) psi) x •
          (chi x * (w : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards with x
    simp [smul_eq_mul]
    ring
  have hright_eq :
      (∫ x : ℝ, (chi x * psi x) • (q : ℝ → ℂ) x) =
        ∫ x : ℝ, psi x • (chi x * (q : ℝ → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards with x
    simp [smul_eq_mul]
    ring
  rw [hfirst_eq, hsecond_eq, hright_eq] at hqp
  linear_combination hqp

lemma criticalDerivative_localized_frequencySmooth (n : ℕ) (f : L2)
    (chi : SchwartzMap ℝ ℂ) (h : Hs (1 / 2 : ℝ))
    (hreal : Hs.toL2 (by norm_num) h =
      cutoffL2CLM chi (frequencySmoothCLM n f)) :
    criticalDerivative h = hsNegOfL2
      (cutoffDerivativeL2 chi (frequencySmoothCLM n f)
        (frequencySmoothDerivativeCLM n f)) := by
  apply Hs.toTempered_injective (-(1 / 2 : ℝ))
  rw [criticalDerivative_toTempered, hsNegOfL2_toTempered,
    Hs.toTempered_toL2 (s := (1 / 2 : ℝ)) (by norm_num), hreal]
  exact lineDeriv_cutoff_toTempered chi _ _
    (lineDeriv_frequencySmooth_toTempered n f)

end CubicNLSPhaseRetrieval
