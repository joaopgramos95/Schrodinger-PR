import Lean_Code.FrequencySmoothing
import Lean_Code.BanachFTC

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

def regularizationGeneratorBound (n : ℕ) : ℝ :=
  4 * Real.pi ^ 2 * (n + 1)

lemma regularizationGeneratorBound_nonneg (n : ℕ) :
    0 ≤ regularizationGeneratorBound n := by
  unfold regularizationGeneratorBound
  positivity

lemma generator_resolvent_norm_le (n : ℕ) (ξ : ℝ) :
    ‖schrodingerGenerator ξ‖ * ‖resolventSymbol n ξ‖ ≤
      regularizationGeneratorBound n := by
  rw [norm_schrodingerGenerator]
  have hden : 0 < 1 + ξ ^ 2 / (n + 1 : ℝ) := by positivity
  have hm : ‖resolventSymbol n ξ‖ =
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ := by
    rw [resolventSymbol, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hden]
  rw [hm]
  change 4 * Real.pi ^ 2 * ξ ^ 2 *
    (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ ≤
      4 * Real.pi ^ 2 * (n + 1)
  rw [show 4 * Real.pi ^ 2 * ξ ^ 2 *
      (1 + ξ ^ 2 / (n + 1 : ℝ))⁻¹ =
      4 * Real.pi ^ 2 *
        (ξ ^ 2 / (1 + ξ ^ 2 / (n + 1 : ℝ))) by ring]
  gcongr
  rw [div_le_iff₀ hden]
  calc
    ξ ^ 2 ≤ (n + 1 : ℝ) + ξ ^ 2 := by
      linarith [show 0 ≤ (n + 1 : ℝ) by positivity]
    _ = (n + 1 : ℝ) * (1 + ξ ^ 2 / (n + 1 : ℝ)) := by
      field_simp

lemma regularized_symbol_sub_bound (n : ℕ) (s t ξ : ℝ) :
    ‖(schrodingerSymbol t ξ - schrodingerSymbol s ξ) *
        resolventSymbol n ξ‖ ≤
      regularizationGeneratorBound n * |t - s| := by
  by_cases hts : t = s
  · subst t
    simp [regularizationGeneratorBound_nonneg]
  · let h := t - s
    have hh : h ≠ 0 := sub_ne_zero.mpr hts
    have hslope := norm_schrodingerSymbol_slope_le s ξ h hh
    have hrewrite : s + h = t := by dsimp [h]; ring
    rw [hrewrite] at hslope
    have hdiff : ‖schrodingerSymbol t ξ - schrodingerSymbol s ξ‖ ≤
        |h| * ‖schrodingerGenerator ξ‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs] at hslope
      have habs : 0 < |h| := abs_pos.mpr hh
      rw [inv_mul_le_iff₀ habs] at hslope
      simpa [norm_schrodingerGenerator, mul_comm] using hslope
    rw [norm_mul]
    calc
      _ ≤ (|h| * ‖schrodingerGenerator ξ‖) * ‖resolventSymbol n ξ‖ := by
        gcongr
      _ = |h| * (‖schrodingerGenerator ξ‖ * ‖resolventSymbol n ξ‖) := by ring
      _ ≤ |h| * regularizationGeneratorBound n := by
        gcongr
        exact generator_resolvent_norm_le n ξ
      _ = regularizationGeneratorBound n * |t - s| := by
        dsimp [h]
        ring

/-- The free group with the resolvent applied first, as an operator-valued
curve. -/
def regularizedFreeCLM (n : ℕ) (t : ℝ) : L2 →L[ℂ] L2 :=
  (freePropLIE t).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (frequencySmoothCLM n)

@[simp] lemma regularizedFreeCLM_apply (n : ℕ) (t : ℝ) (f : L2) :
    regularizedFreeCLM n t f = freeProp t (frequencySmoothCLM n f) := rfl

lemma fourier_regularizedFreeCLM_ae (n : ℕ) (t : ℝ) (f : L2) :
    (fourierL2 (regularizedFreeCLM n t f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => schrodingerSymbol t ξ * resolventSymbol n ξ *
        (fourierL2 f : ℝ → ℂ) ξ := by
  change (fourierL2 (freeProp t (frequencySmoothCLM n f)) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [fourier_freeProp t (frequencySmoothCLM n f),
    coe_fourier_frequencySmoothCLM n f] with ξ hfree hs
  rw [hfree, hs]
  ring

lemma norm_regularizedFreeCLM_sub_apply_le (n : ℕ) (s t : ℝ) (f : L2) :
    ‖(regularizedFreeCLM n t - regularizedFreeCLM n s) f‖ ≤
      (regularizationGeneratorBound n * |t - s|) * ‖f‖ := by
  let K : ℝ := regularizationGeneratorBound n * |t - s|
  have hK : 0 ≤ K := mul_nonneg (regularizationGeneratorBound_nonneg n) (abs_nonneg _)
  let g : L2 := (K : ℂ) • fourierL2 f
  have hout : (fourierL2
      ((regularizedFreeCLM n t - regularizedFreeCLM n s) f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((schrodingerSymbol t ξ - schrodingerSymbol s ξ) *
        resolventSymbol n ξ) * (fourierL2 f : ℝ → ℂ) ξ := by
    filter_upwards [fourier_regularizedFreeCLM_ae n t f,
      fourier_regularizedFreeCLM_ae n s f,
      Lp.coeFn_sub (regularizedFreeCLM n t f) (regularizedFreeCLM n s f),
      Lp.coeFn_sub
        (fourierL2 (regularizedFreeCLM n t f))
        (fourierL2 (regularizedFreeCLM n s f))] with ξ ht hs hout hfour
    change (fourierL2
      ((regularizedFreeCLM n t - regularizedFreeCLM n s) f) : ℝ → ℂ) ξ = _
    rw [show (regularizedFreeCLM n t - regularizedFreeCLM n s) f =
      regularizedFreeCLM n t f - regularizedFreeCLM n s f by rfl]
    rw [map_sub, hfour, Pi.sub_apply, ht, hs]
    ring
  have hg : (g : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (K : ℂ) * (fourierL2 f : ℝ → ℂ) ξ := by
    exact Lp.coeFn_smul (K : ℂ) (fourierL2 f)
  have hmono : eLpNorm
      (fourierL2 ((regularizedFreeCLM n t - regularizedFreeCLM n s) f) : ℝ → ℂ)
        2 volume ≤ eLpNorm (g : ℝ → ℂ) 2 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [hout, hg] with ξ ho hgξ
    rw [ho, hgξ]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hK]
    gcongr
    simpa [K, norm_mul] using regularized_symbol_sub_bound n s t ξ
  calc
    _ = ‖fourierL2 ((regularizedFreeCLM n t - regularizedFreeCLM n s) f)‖ := by
      rw [fourierL2.norm_map]
    _ ≤ ‖g‖ := by
      rw [Lp.norm_def, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) hmono
    _ = K * ‖f‖ := by
      dsimp [g]
      change ‖(K : ℂ) • fourierL2 f‖ = K * ‖f‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK,
        fourierL2.norm_map]
    _ = _ := rfl

lemma norm_regularizedFreeCLM_sub_le (n : ℕ) (s t : ℝ) :
    ‖regularizedFreeCLM n t - regularizedFreeCLM n s‖ ≤
      regularizationGeneratorBound n * |t - s| := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (regularizationGeneratorBound_nonneg n) (abs_nonneg _))
  exact norm_regularizedFreeCLM_sub_apply_le n s t

lemma lipschitzWith_regularizedFreeCLM (n : ℕ) :
    LipschitzWith (NNReal.mk (regularizationGeneratorBound n)
      (regularizationGeneratorBound_nonneg n)) (regularizedFreeCLM n) := by
  let K : NNReal := NNReal.mk (regularizationGeneratorBound n)
    (regularizationGeneratorBound_nonneg n)
  change LipschitzWith K (regularizedFreeCLM n)
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm, Real.dist_eq]
  change ‖regularizedFreeCLM n s - regularizedFreeCLM n t‖ ≤
    (K : ℝ) * |s - t|
  rw [show (K : ℝ) = regularizationGeneratorBound n by rfl]
  simpa [mul_comm] using norm_regularizedFreeCLM_sub_le n t s

lemma regularizedFreeCLM_absolutelyContinuousOnInterval (n : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (regularizedFreeCLM n) a b := by
  exact (lipschitzWith_regularizedFreeCLM n).lipschitzOnWith
    |>.absolutelyContinuousOnInterval

end CubicNLSPhaseRetrieval
