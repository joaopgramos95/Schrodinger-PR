import Lean_Code.FourierSobolev
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The free Schrödinger group

Blueprint chapter: `chap:free-group` (module 2).
Imports: module 1 (`FourierSobolev`).
-/

open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The complex Hilbert space `L²(ℝ)`. This unfolds to the showcase's canonical `L2`. -/
abbrev L2 : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- Mathlib's unitary Fourier transform on `L²(ℝ)`. -/
def fourierL2 : L2 ≃ₗᵢ[ℂ] L2 := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-- The multiplier `exp (-4π² i t ξ²)` for the free Schrödinger group. -/
def schrodingerSymbol (t ξ : ℝ) : ℂ :=
  Complex.exp (((-(4 * Real.pi ^ 2 * t * ξ ^ 2) : ℝ) : ℂ) * Complex.I)

lemma norm_schrodingerSymbol (t ξ : ℝ) : ‖schrodingerSymbol t ξ‖ = 1 := by
  unfold schrodingerSymbol
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_schrodingerSymbol (t : ℝ) : Continuous (schrodingerSymbol t) := by
  unfold schrodingerSymbol
  fun_prop

/-- Multiplication by the bounded unit-modulus Schrödinger symbol on `L²`. -/
def multSymbol (t : ℝ) (g : L2) : L2 :=
  MemLp.toLp (fun ξ => schrodingerSymbol t ξ * (⇑g) ξ) (by
    have hmeas : AEStronglyMeasurable (fun ξ => schrodingerSymbol t ξ * (⇑g) ξ) volume :=
      (continuous_schrodingerSymbol t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)
    refine ((Lp.memLp g).norm).mono' hmeas ?_
    filter_upwards with ξ
    rw [norm_mul, norm_schrodingerSymbol, one_mul])

/-- The free one-dimensional Schrödinger propagator. This unfolds to the showcase definition. -/
def freeProp (t : ℝ) (f : L2) : L2 := fourierL2.symm (multSymbol t (fourierL2 f))

lemma coeFn_multSymbol (t : ℝ) (g : L2) :
    (⇑(multSymbol t g) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => schrodingerSymbol t ξ * (⇑g) ξ := by
  unfold multSymbol
  exact MemLp.coeFn_toLp _

/-- Fourier-multiplier characterization of `freeProp`. -/
lemma fourier_freeProp (t : ℝ) (f : L2) :
    (⇑(fourierL2 (freeProp t f)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => schrodingerSymbol t ξ * (⇑(fourierL2 f)) ξ := by
  unfold freeProp
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact coeFn_multSymbol t (fourierL2 f)

lemma norm_multSymbol (t : ℝ) (g : L2) : ‖multSymbol t g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [coeFn_multSymbol t g] with ξ hξ
  rw [hξ, norm_mul, norm_schrodingerSymbol, one_mul]

/-- Unitarity of the free group at the level needed by the canonical solution class. -/
lemma norm_freeProp (t : ℝ) (f : L2) : ‖freeProp t f‖ = ‖f‖ := by
  unfold freeProp
  rw [LinearIsometryEquiv.norm_map, norm_multSymbol, LinearIsometryEquiv.norm_map]

private lemma multSymbol_smul (c : ℂ) (t : ℝ) (g : L2) :
    multSymbol t (c • g) = c • multSymbol t g := by
  apply Lp.ext
  filter_upwards [coeFn_multSymbol t (c • g), coeFn_multSymbol t g,
    Lp.coeFn_smul c g, Lp.coeFn_smul c (multSymbol t g)] with ξ hleft hright hg hsmul
  rw [hleft, hg, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hright]
  ring

/-- Complex linearity of the free propagator. -/
lemma freeProp_smul (c : ℂ) (t : ℝ) (f : L2) :
    freeProp t (c • f) = c • freeProp t f := by
  unfold freeProp
  rw [map_smul, multSymbol_smul, map_smul]

private lemma multSymbol_add (t : ℝ) (f g : L2) :
    multSymbol t (f + g) = multSymbol t f + multSymbol t g := by
  apply Lp.ext
  filter_upwards [coeFn_multSymbol t (f + g), coeFn_multSymbol t f,
    coeFn_multSymbol t g, Lp.coeFn_add f g,
    Lp.coeFn_add (multSymbol t f) (multSymbol t g)] with ξ hfg hf hg hadd hout
  rw [hfg, hadd, hout]
  simp only [Pi.add_apply]
  rw [hf, hg]
  ring

/-- Additivity of the free propagator. -/
lemma freeProp_add_apply (t : ℝ) (f g : L2) :
    freeProp t (f + g) = freeProp t f + freeProp t g := by
  unfold freeProp
  rw [map_add, multSymbol_add, map_add]

/-- Subtractivity of the free propagator. -/
lemma freeProp_sub (t : ℝ) (f g : L2) :
    freeProp t (f - g) = freeProp t f - freeProp t g := by
  rw [sub_eq_add_neg, freeProp_add_apply, ← neg_one_smul ℂ g,
    freeProp_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

/-- The oscillatory free kernel, with the principal square root boundary value. -/
def freeKernel (t x y : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℝ) : ℂ) *
    (Complex.sqrt ((((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I)))⁻¹ *
    Complex.exp (Complex.I * (((x - y) ^ 2 / (4 * t) : ℝ) : ℂ))

/-- Integral realization of the free kernel on an L¹ representative. -/
def freeKernelOp (t : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, freeKernel t x y * f y

private lemma schrodingerSymbol_mul (s t ξ : ℝ) :
    schrodingerSymbol t ξ * schrodingerSymbol s ξ =
      schrodingerSymbol (t + s) ξ := by
  rw [schrodingerSymbol, schrodingerSymbol, schrodingerSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma freeProp_add (s t : ℝ) (f : L2) :
    freeProp t (freeProp s f) = freeProp (t + s) f := by
  apply fourierL2.injective
  apply Lp.ext
  filter_upwards [fourier_freeProp t (freeProp s f), fourier_freeProp s f,
    fourier_freeProp (t + s) f] with ξ hts hs hsum
  rw [hts, hs, hsum, ← mul_assoc, schrodingerSymbol_mul]

private lemma freeProp_zero (f : L2) : freeProp 0 f = f := by
  apply fourierL2.injective
  apply Lp.ext
  filter_upwards [fourier_freeProp 0 f] with ξ hξ
  rw [hξ]
  simp [schrodingerSymbol]

/-- The free propagator at a fixed time, bundled as a linear isometric
equivalence.  Its inverse is propagation by the opposite time. -/
def freePropLIE (t : ℝ) : L2 ≃ₗᵢ[ℂ] L2 where
  toFun := freeProp t
  invFun := freeProp (-t)
  map_add' := freeProp_add_apply t
  map_smul' := fun c f => freeProp_smul c t f
  left_inv f := by
    rw [freeProp_add]
    simpa using freeProp_zero f
  right_inv f := by
    rw [freeProp_add]
    simpa using freeProp_zero f
  norm_map' := norm_freeProp t

@[simp] lemma freePropLIE_apply (t : ℝ) (f : L2) :
    freePropLIE t f = freeProp t f := rfl

@[simp] lemma freePropLIE_symm_apply (t : ℝ) (f : L2) :
    (freePropLIE t).symm f = freeProp (-t) f := rfl

/-- Preservation of the `L²` inner product by the free group. -/
lemma inner_freeProp (t : ℝ) (f g : L2) :
    @inner ℂ L2 _ (freeProp t f) (freeProp t g) = @inner ℂ L2 _ f g := by
  exact (freePropLIE t).inner_map_map f g

/-- Moving a free propagator from the first argument of the inner product to
the second reverses time. -/
lemma inner_freeProp_left (t : ℝ) (f g : L2) :
    @inner ℂ L2 _ (freeProp t f) g = @inner ℂ L2 _ f (freeProp (-t) g) := by
  simpa using (freePropLIE t).inner_map_eq_flip f g

private lemma continuous_multSymbol (g : L2) : Continuous (fun t => multSymbol t g) := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let r : ℝ → ℝ → ℂ := fun t ξ =>
    (schrodingerSymbol t ξ - schrodingerSymbol t0 ξ) * (g : ℝ → ℂ) ξ
  have hraw (t : ℝ) :
      eLpNorm ((multSymbol t g : ℝ → ℂ) - (multSymbol t0 g : ℝ → ℂ)) 2 volume =
        eLpNorm (r t) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [coeFn_multSymbol t g, coeFn_multSymbol t0 g] with ξ ht ht0
    simp only [Pi.sub_apply, ht, ht0]
    dsimp [r]
    ring
  simp_rw [hraw]
  have hmeas : ∀ t : ℝ, AEMeasurable (fun ξ => ‖r t ξ‖ₑ ^ (2 : ℝ)) volume := by
    intro t
    apply AEMeasurable.pow_const
    apply AEStronglyMeasurable.enorm
    exact ((continuous_schrodingerSymbol t).aestronglyMeasurable.sub
      (continuous_schrodingerSymbol t0).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable g)
  have hbound : ∀ t : ℝ, ∀ᵐ ξ : ℝ ∂volume,
      ‖r t ξ‖ₑ ^ (2 : ℝ) ≤ 4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
    intro t
    filter_upwards with ξ
    have hs : ‖schrodingerSymbol t ξ - schrodingerSymbol t0 ξ‖ ≤ 2 := by
      calc
        ‖schrodingerSymbol t ξ - schrodingerSymbol t0 ξ‖ ≤
            ‖schrodingerSymbol t ξ‖ + ‖schrodingerSymbol t0 ξ‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_schrodingerSymbol, norm_schrodingerSymbol]; norm_num
    dsimp [r]
    rw [enorm_mul]
    have hse : ‖schrodingerSymbol t ξ - schrodingerSymbol t0 ξ‖ₑ ≤ 2 := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)
    calc
      (‖schrodingerSymbol t ξ - schrodingerSymbol t0 ξ‖ₑ * ‖(g : ℝ → ℂ) ξ‖ₑ) ^
          (2 : ℝ) =
          ‖schrodingerSymbol t ξ - schrodingerSymbol t0 ξ‖ₑ ^ (2 : ℝ) *
            ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ (2 : ℝ≥0∞) ^ (2 : ℝ) * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by gcongr
      _ = 4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by norm_num
  have hfin : (∫⁻ ξ : ℝ, 4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂volume) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp g).2).ne
  have hpoint : ∀ ξ : ℝ,
      Tendsto (fun t => ‖r t ξ‖ₑ ^ (2 : ℝ)) (𝓝 t0) (𝓝 0) := by
    intro ξ
    have hr : Tendsto (fun t => r t ξ) (𝓝 t0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => r t ξ) t0 := by
        dsimp [r, schrodingerSymbol]
        fun_prop
      simpa [r] using hc.tendsto
    convert
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hr.enorm using 1 <;>
      simp [Function.comp_def]
  have hint := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := volume) (l := 𝓝 t0)
    (F := fun t ξ => ‖r t ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
    (fun ξ => 4 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ))
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound) hfin
    (Filter.Eventually.of_forall hpoint)
  simp only [lintegral_zero] at hint
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, one_div]
  convert
    (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hint using 1 <;>
    simp [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]

private lemma continuous_freeProp (f : L2) : Continuous (fun t => freeProp t f) := by
  exact fourierL2.symm.continuous.comp (continuous_multSymbol (fourierL2 f))

private def schrodingerFrequency (ξ : ℝ) : ℝ := 4 * Real.pi ^ 2 * ξ ^ 2

def schrodingerGenerator (ξ : ℝ) : ℂ :=
  ((-schrodingerFrequency ξ : ℝ) : ℂ) * Complex.I

private lemma schrodingerFrequency_nonneg (ξ : ℝ) : 0 ≤ schrodingerFrequency ξ := by
  dsimp [schrodingerFrequency]
  positivity

lemma norm_schrodingerGenerator (ξ : ℝ) :
    ‖schrodingerGenerator ξ‖ = schrodingerFrequency ξ := by
  rw [schrodingerGenerator, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (schrodingerFrequency_nonneg ξ)]

private lemma schrodingerSymbol_eq_generator_exp (t ξ : ℝ) :
    schrodingerSymbol t ξ = Complex.exp ((t : ℂ) * schrodingerGenerator ξ) := by
  rw [schrodingerSymbol, schrodingerGenerator, schrodingerFrequency]
  congr 1
  push_cast
  ring

private lemma hasDerivAt_schrodingerSymbol (t ξ : ℝ) :
    HasDerivAt (fun s => schrodingerSymbol s ξ)
      (schrodingerGenerator ξ * schrodingerSymbol t ξ) t := by
  simp_rw [schrodingerSymbol_eq_generator_exp]
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * schrodingerGenerator ξ)
      (schrodingerGenerator ξ) t := by
    simpa using Complex.ofRealCLM.hasDerivAt.mul_const (schrodingerGenerator ξ)
  simpa [mul_comm] using hlin.cexp

lemma norm_schrodingerSymbol_slope_le (t ξ h : ℝ) (hh : h ≠ 0) :
    ‖((h : ℂ)⁻¹) * (schrodingerSymbol (t + h) ξ - schrodingerSymbol t ξ)‖ ≤
      schrodingerFrequency ξ := by
  have hgroup : schrodingerSymbol (t + h) ξ =
      schrodingerSymbol t ξ * schrodingerSymbol h ξ := by
    rw [mul_comm, schrodingerSymbol_mul t h ξ, add_comm]
  have hosc : schrodingerSymbol h ξ =
      Complex.exp (Complex.I * ((-schrodingerFrequency ξ * h : ℝ) : ℂ)) := by
    rw [schrodingerSymbol_eq_generator_exp, schrodingerGenerator]
    congr 1
    push_cast
    ring
  rw [hgroup]
  have hfactor : schrodingerSymbol t ξ * schrodingerSymbol h ξ -
      schrodingerSymbol t ξ =
        schrodingerSymbol t ξ * (schrodingerSymbol h ξ - 1) := by ring
  rw [hfactor, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, norm_schrodingerSymbol, one_mul, hosc]
  have htrig := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := -schrodingerFrequency ξ * h)
  calc
    |h|⁻¹ * ‖Complex.exp (Complex.I * ((-schrodingerFrequency ξ * h : ℝ) : ℂ)) - 1‖ ≤
        |h|⁻¹ * ‖-schrodingerFrequency ξ * h‖ :=
      mul_le_mul_of_nonneg_left htrig (inv_nonneg.mpr (abs_nonneg h))
    _ = schrodingerFrequency ξ := by
      rw [Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg (schrodingerFrequency_nonneg ξ)]
      field_simp [abs_ne_zero.mpr hh]

lemma continuous_schrodingerGenerator : Continuous schrodingerGenerator := by
  unfold schrodingerGenerator schrodingerFrequency
  fun_prop

lemma generator_symbol_mul_memLp (g : L2)
    (hgen : MemLp (fun ξ : ℝ => schrodingerGenerator ξ * (g : ℝ → ℂ) ξ) 2 volume)
    (t : ℝ) : MemLp (fun ξ : ℝ =>
      schrodingerGenerator ξ * schrodingerSymbol t ξ * (g : ℝ → ℂ) ξ) 2 volume := by
  refine ⟨((continuous_schrodingerGenerator.aestronglyMeasurable.mul
    (continuous_schrodingerSymbol t).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g)), ?_⟩
  have heq : eLpNorm (fun ξ : ℝ =>
        schrodingerGenerator ξ * schrodingerSymbol t ξ * (g : ℝ → ℂ) ξ) 2 volume =
      eLpNorm (fun ξ : ℝ => schrodingerGenerator ξ * (g : ℝ → ℂ) ξ) 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with ξ
    simp only [norm_mul, norm_schrodingerSymbol, mul_one]
  rw [heq]
  exact hgen.2

lemma hasDerivAt_multSymbol (g : L2)
    (hgen : MemLp (fun ξ : ℝ => schrodingerGenerator ξ * (g : ℝ → ℂ) ξ) 2 volume)
    (t : ℝ) :
    HasDerivAt (fun s => multSymbol s g)
      ((generator_symbol_mul_memLp g hgen t).toLp
        (fun ξ : ℝ => schrodingerGenerator ξ * schrodingerSymbol t ξ *
          (g : ℝ → ℂ) ξ)) t := by
  let dg : ℝ → ℂ := fun ξ =>
    schrodingerGenerator ξ * schrodingerSymbol t ξ * (g : ℝ → ℂ) ξ
  have hdg : MemLp dg 2 volume := generator_symbol_mul_memLp g hgen t
  change HasDerivAt (fun s => multSymbol s g) (hdg.toLp dg) t
  rw [hasDerivAt_iff_tendsto_slope_zero, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let r : ℝ → ℝ → ℂ := fun h ξ =>
    ((h : ℂ)⁻¹) * (schrodingerSymbol (t + h) ξ - schrodingerSymbol t ξ) *
        (g : ℝ → ℂ) ξ - dg ξ
  have hraw (h : ℝ) :
      eLpNorm
          ((↑(h⁻¹ • (multSymbol (t + h) g - multSymbol t g)) : ℝ → ℂ) -
            (↑(hdg.toLp dg) : ℝ → ℂ)) 2 volume = eLpNorm (r h) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (multSymbol (t + h) g) (multSymbol t g),
      Lp.coeFn_smul h⁻¹ (multSymbol (t + h) g - multSymbol t g),
      coeFn_multSymbol (t + h) g, coeFn_multSymbol t g, hdg.coeFn_toLp]
      with ξ hsub hsmul hth ht0 hd
    simp only [Pi.sub_apply]
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hth, ht0, hd]
    dsimp [r]
    push_cast
    ring
  simp_rw [hraw]
  have hmeas : ∀ h : ℝ, AEMeasurable (fun ξ => ‖r h ξ‖ₑ ^ (2 : ℝ)) volume := by
    intro h
    apply AEMeasurable.pow_const
    apply AEStronglyMeasurable.enorm
    exact ((((continuous_schrodingerSymbol (t + h)).aestronglyMeasurable.sub
      (continuous_schrodingerSymbol t).aestronglyMeasurable).const_mul ((h : ℂ)⁻¹)).mul
        (Lp.aestronglyMeasurable g)).sub hdg.1
  have hbound : ∀ᶠ h : ℝ in nhdsWithin 0 {0}ᶜ, ∀ᵐ ξ : ℝ ∂volume,
      ‖r h ξ‖ₑ ^ (2 : ℝ) ≤
        4 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    filter_upwards with ξ
    have hslope := norm_schrodingerSymbol_slope_le t ξ h hh0
    have hrnorm : ‖r h ξ‖ ≤
        2 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ := by
      dsimp [r, dg]
      calc
        ‖((h : ℂ)⁻¹) * (schrodingerSymbol (t + h) ξ - schrodingerSymbol t ξ) *
              (g : ℝ → ℂ) ξ -
            schrodingerGenerator ξ * schrodingerSymbol t ξ * (g : ℝ → ℂ) ξ‖ ≤
            ‖((h : ℂ)⁻¹) * (schrodingerSymbol (t + h) ξ - schrodingerSymbol t ξ) *
              (g : ℝ → ℂ) ξ‖ +
            ‖schrodingerGenerator ξ * schrodingerSymbol t ξ * (g : ℝ → ℂ) ξ‖ :=
          norm_sub_le _ _
        _ ≤ schrodingerFrequency ξ * ‖(g : ℝ → ℂ) ξ‖ +
            schrodingerFrequency ξ * ‖(g : ℝ → ℂ) ξ‖ := by
          gcongr
          · simpa [norm_mul] using
              mul_le_mul_of_nonneg_right hslope (norm_nonneg ((g : ℝ → ℂ) ξ))
          · rw [norm_mul, norm_mul, norm_schrodingerGenerator,
              norm_schrodingerSymbol, mul_one]
        _ = 2 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ := by
          rw [norm_mul, norm_schrodingerGenerator]
          ring
    have hre : ‖r h ξ‖ₑ ≤ 2 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ₑ := by
      simpa [← ofReal_norm, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using
        ENNReal.ofReal_le_ofReal hrnorm
    calc
      ‖r h ξ‖ₑ ^ (2 : ℝ) ≤
          (2 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ₑ) ^ (2 : ℝ) := by gcongr
      _ = 4 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  have hfin : (∫⁻ ξ : ℝ,
      4 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂volume) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hgen.2).ne
  have hpoint : ∀ ξ : ℝ, Tendsto (fun h => ‖r h ξ‖ₑ ^ (2 : ℝ))
      (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
    intro ξ
    have hs := (hasDerivAt_schrodingerSymbol t ξ).tendsto_slope_zero
    have hr : Tendsto (fun h => r h ξ) (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
      have hm := hs.mul_const ((g : ℝ → ℂ) ξ)
      have hz := hm.sub_const (dg ξ)
      convert hz using 1 <;> simp [r, dg, mul_assoc]
    convert
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hr.enorm using 1 <;>
      simp [Function.comp_def]
  have hint := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := volume) (l := nhdsWithin 0 {0}ᶜ)
    (F := fun h ξ => ‖r h ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
    (fun ξ => 4 * ‖schrodingerGenerator ξ * (g : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ))
    (Filter.Eventually.of_forall hmeas) hbound hfin (Filter.Eventually.of_forall hpoint)
  simp only [lintegral_zero] at hint
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, one_div]
  convert
    (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hint using 1 <;>
    simp [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]

private lemma schwartz_fourier_second_deriv (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 ((SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) φ))) ξ =
      (((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) * (𝓕 φ) ξ) := by
  let dφ := (SchwartzMap.derivCLM ℂ ℂ) φ
  have h1 := Real.fourier_deriv φ.integrable φ.differentiable dφ.integrable
  have h2 := Real.fourier_deriv dφ.integrable dφ.differentiable
    ((SchwartzMap.derivCLM ℂ ℂ) dφ).integrable
  change 𝓕 (deriv (dφ : ℝ → ℂ)) ξ = _
  rw [congrFun h2 ξ]
  change (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) *
      𝓕 (deriv (φ : ℝ → ℂ)) ξ = _
  rw [congrFun h1 ξ]
  rw [SchwartzMap.fourier_coe]
  simp only [smul_eq_mul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma coe_fourierL2_schwartz (ψ : 𝓢(ℝ, ℂ)) :
    (fourierL2 (ψ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume] fun ξ => (𝓕 ψ) ξ := by
  have hfourier : fourierL2 (ψ.toLp 2 volume) = (𝓕 ψ).toLp 2 volume := by
    unfold fourierL2
    exact SchwartzMap.toLp_fourier_eq ψ
  rw [hfourier]
  exact MemLp.coeFn_toLp ((𝓕 ψ).memLp 2 volume)

private lemma schwartz_generator_memLp (φ : 𝓢(ℝ, ℂ)) :
    MemLp (fun ξ : ℝ => schrodingerGenerator ξ *
      (fourierL2 (φ.toLp 2 volume) : ℝ → ℂ) ξ) 2 volume := by
  let φ'' := (SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) φ)
  have hsch : MemLp (fun ξ : ℝ => schrodingerGenerator ξ * (𝓕 φ) ξ) 2 volume := by
    refine (𝓕 φ'').memLp 2 volume |>.congr_norm
      (continuous_schrodingerGenerator.aestronglyMeasurable.mul
        (𝓕 φ).continuous.aestronglyMeasurable) ?_
    filter_upwards with ξ
    dsimp [φ'']
    rw [schwartz_fourier_second_deriv]
    unfold schrodingerGenerator schrodingerFrequency
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_neg]
  refine hsch.congr_norm
    (continuous_schrodingerGenerator.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (fourierL2 (φ.toLp 2 volume)))) ?_
  filter_upwards [coe_fourierL2_schwartz φ] with ξ hξ
  rw [hξ]

private lemma schwartz_free_derivative (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (fun s => freeProp s (φ.toLp 2 volume))
      (Complex.I • freeProp t
        (((SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) φ)).toLp 2 volume)) t := by
  let g : L2 := fourierL2 (φ.toLp 2 volume)
  let φ'' := (SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) φ)
  let dg : ℝ → ℂ := fun ξ =>
    schrodingerGenerator ξ * schrodingerSymbol t ξ * (g : ℝ → ℂ) ξ
  have hgen : MemLp (fun ξ : ℝ =>
      schrodingerGenerator ξ * (g : ℝ → ℂ) ξ) 2 volume :=
    schwartz_generator_memLp φ
  have hdg : MemLp dg 2 volume := generator_symbol_mul_memLp g hgen t
  have hm : HasDerivAt (fun s => multSymbol s g) (hdg.toLp dg) t := by
    simpa [dg] using hasDerivAt_multSymbol g hgen t
  let U : L2 ≃L[ℂ] L2 := fourierL2.symm.toContinuousLinearEquiv
  let UR : L2 →L[ℝ] L2 := (U.restrictScalars ℝ).toContinuousLinearMap
  have hcomp := UR.hasFDerivAt.comp_hasDerivAt t hm
  have hfree : HasDerivAt (fun s => freeProp s (φ.toLp 2 volume))
      (fourierL2.symm (hdg.toLp dg)) t := by
    simpa [freeProp, g, U, UR, Function.comp_def] using hcomp
  have htarget : fourierL2.symm (hdg.toLp dg) = Complex.I • freeProp t (φ''.toLp 2 volume) := by
    apply fourierL2.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul]
    apply Lp.ext
    filter_upwards [hdg.coeFn_toLp, Lp.coeFn_smul Complex.I (fourierL2 (freeProp t (φ''.toLp 2 volume))),
      fourier_freeProp t (φ''.toLp 2 volume), coe_fourierL2_schwartz φ'',
      coe_fourierL2_schwartz φ] with ξ hd hsmul hfree' hφ'' hφ
    rw [hd, hsmul]
    simp only [Pi.smul_apply]
    rw [hfree', hφ'']
    dsimp [dg]
    rw [hφ]
    dsimp [φ'']
    rw [schwartz_fourier_second_deriv]
    unfold schrodingerGenerator schrodingerFrequency
    push_cast
    ring
  rw [htarget] at hfree
  exact hfree

/-- `lem:propagator-unitary`: unitarity, group law, strong continuity, and the free PDE. -/
theorem propagator_unitary :
  (∀ t : ℝ, ∀ f : L2, ‖freeProp t f‖ = ‖f‖) ∧
  (∀ s t : ℝ, ∀ f : L2, freeProp t (freeProp s f) = freeProp (t + s) f) ∧
  (∀ f : L2, freeProp 0 f = f) ∧
  (∀ f : L2, Continuous (fun t => freeProp t f)) ∧
  ∀ φ : 𝓢(ℝ, ℂ), ∀ t : ℝ,
    HasDerivAt (fun s => freeProp s (φ.toLp 2 volume))
      (Complex.I • freeProp t
        (((SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) φ)).toLp 2 volume)) t := by
  exact ⟨norm_freeProp, freeProp_add, freeProp_zero, continuous_freeProp,
    schwartz_free_derivative⟩

/-- Joint continuity of the free group in time and data.  Strong continuity
and unitarity suffice: split the increment into a data increment at the new
time and a time increment of the fixed limiting datum. -/
theorem continuous_freeProp_joint :
    Continuous (fun p : ℝ × L2 => freeProp p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hdata : Tendsto (fun q : ℝ × L2 => freeProp q.1 (q.2 - p.2))
      (𝓝 p) (𝓝 0) := by
    have hsub : Continuous (fun q : ℝ × L2 => q.2 - p.2) :=
      continuous_snd.sub continuous_const
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht : Tendsto (fun q : ℝ × L2 => ‖q.2 - p.2‖)
        (𝓝 p) (𝓝 ‖p.2 - p.2‖) := hsub.norm.continuousAt
    simpa only [sub_zero, norm_freeProp, sub_self, norm_zero] using ht
  have htime : Tendsto (fun q : ℝ × L2 => freeProp q.1 p.2)
      (𝓝 p) (𝓝 (freeProp p.1 p.2)) :=
    ((propagator_unitary.2.2.2.1 p.2).comp continuous_fst).continuousAt
  change Tendsto (fun q : ℝ × L2 => freeProp q.1 q.2)
    (𝓝 p) (𝓝 (freeProp p.1 p.2))
  convert hdata.add htime using 1
  · funext q
    rw [← freeProp_add_apply]
    congr 1
    abel
  · simp

/-- `lem:complex-gaussian-kernel`: the complex Gaussian integral on the right half-plane. -/
theorem complex_gaussian_kernel (z : ℂ) (hz : 0 < z.re) (a : ℝ) :
  ∫ ξ : ℝ, Complex.exp (-z * (ξ : ℂ) ^ 2 + Complex.I * (a * ξ : ℝ)) =
    ((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt z)⁻¹ *
      Complex.exp (-((a ^ 2 : ℝ) : ℂ) / (4 * z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simpa using hz
  have harg : z.arg ≠ Real.pi := by
    rw [ne_eq, Complex.arg_eq_pi_iff]
    exact not_and_of_not_left _ (not_lt_of_ge hz.le)
  have hdiv0 : ((Real.pi : ℂ) / z) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz0
  have hlogpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℝ) := by
    simpa using (Complex.log_ofReal_mul Real.pi_pos (x := (1 : ℂ)) one_ne_zero)
  have hfac : ((Real.pi : ℂ) / z) ^ (1 / 2 : ℂ) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt z)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    simp only [Complex.sqrt]
    norm_num
    rw [Complex.cpow_def_of_ne_zero hdiv0,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      Complex.cpow_def_of_ne_zero hz0]
    rw [div_eq_mul_inv, Complex.log_ofReal_mul Real.pi_pos (inv_ne_zero hz0),
      Complex.log_inv z harg, add_mul, Complex.exp_add, hlogpi]
    rw [show -Complex.log z * (1 / 2 : ℂ) =
      -(Complex.log z * (1 / 2 : ℂ)) by ring, Complex.exp_neg]
  have hgauss := fourierIntegral_gaussian hz (a : ℂ)
  rw [hfac] at hgauss
  calc
    ∫ ξ : ℝ, Complex.exp (-z * (ξ : ℂ) ^ 2 + Complex.I * (a * ξ : ℝ)) =
        ∫ ξ : ℝ, Complex.exp (Complex.I * (a : ℂ) * ξ) *
          Complex.exp (-z * (ξ : ℂ) ^ 2) := by
            congr 1
            funext ξ
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
    _ = ((Real.sqrt Real.pi : ℝ) : ℂ) * (Complex.sqrt z)⁻¹ *
          Complex.exp (-((a : ℂ) ^ 2) / (4 * z)) := hgauss
    _ = _ := by norm_num

theorem norm_freeKernel (t : ℝ) (ht : t ≠ 0) (x y : ℝ) :
    ‖freeKernel t x y‖ = (4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ)) := by
  unfold freeKernel
  rw [norm_mul, norm_mul, norm_inv]
  have hsqrtNorm :
      ‖(((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I) ^ (2⁻¹ : ℂ)‖ =
        ‖((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I‖ ^ (1 / 2 : ℝ) := by
    convert
      (Complex.norm_cpow_inv_nat
        (((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * Complex.I) 2) using 1 <;>
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

theorem enorm_freeKernel (t x y : ℝ) :
    ‖freeKernel t x y‖ₑ =
      ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) := by
  by_cases ht : t = 0
  · subst t
    simp [freeKernel]
  · rw [← ofReal_norm, norm_freeKernel t ht]

/-- `lem:dispersive-1d`: the sharp one-dimensional L¹-to-L∞ estimate. -/
theorem dispersive_1d (t : ℝ) (ht : t ≠ 0) (f : ℝ → ℂ) (hf : MemLp f 1 volume) :
  eLpNorm (freeKernelOp t f) ⊤ volume ≤
    ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * eLpNorm f 1 volume := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards with x
  rw [freeKernelOp]
  calc
    ‖∫ y : ℝ, freeKernel t x y * f y‖ₑ ≤
        ∫⁻ y : ℝ, ‖freeKernel t x y * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y : ℝ,
        ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * ‖f y‖ₑ := by
      apply lintegral_congr
      intro y
      rw [enorm_mul, ← ofReal_norm, norm_freeKernel t ht]
    _ = ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        ∫⁻ y : ℝ, ‖f y‖ₑ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by rw [← eLpNorm_one_eq_lintegral_enorm]

end CubicNLSPhaseRetrieval
