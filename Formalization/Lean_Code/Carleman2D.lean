import Lean_Code.ScalarMixedNorms
import Lean_Code.FreeSchrodinger
import Lean_Code.FractionalIntegration
import Lean_Code.CarlemanODE

/-!
# A self-contained half-space Carleman theorem

Blueprint chapter: `chap:carleman` (module 13).
Imports: modules 0, 2, and 3.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Scalar spacetime fields in two spatial dimensions. -/
abbrev Spacetime2 := ℝ × (ℝ × ℝ) → ℂ

/-- The energy Carleman source gauge `L¹_t L²_z`.

Only this summand is used by the phase-retrieval argument.  Assigning infinite
gauge to nonmeasurable representatives keeps all triangle and multiplier
statements sound for raw functions. -/
def carlemanXNorm (J : Set ℝ) (f : Spacetime2) : ℝ≥0∞ :=
  @ite ℝ≥0∞
    (AEStronglyMeasurable f ((volume.restrict J).prod (volume.prod volume)))
    (Classical.propDecidable _)
    (scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2 f) ⊤

/-- The energy Carleman solution gauge `L∞_t L²_z`. -/
def carlemanXprimeNorm (J : Set ℝ) (f : Spacetime2) : ℝ≥0∞ :=
  @ite ℝ≥0∞
    (AEStronglyMeasurable f ((volume.restrict J).prod (volume.prod volume)))
    (Classical.propDecidable _)
    (scalarMixedENorm (volume.restrict J) (volume.prod volume) ⊤ 2 f) ⊤

/-- The potential gauge `L¹_t L∞_z` used in the energy absorption. -/
def carlemanYNorm (J : Set ℝ) (W : Spacetime2) : ℝ≥0∞ :=
  @ite ℝ≥0∞
    (AEStronglyMeasurable W ((volume.restrict J).prod (volume.prod volume)))
    (Classical.propDecidable _)
    (scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 ⊤ W) ⊤

private lemma sectionENorm_two_aemeasurable
    (J : Set ℝ) (f : Spacetime2)
    (hf : AEStronglyMeasurable f
      ((volume.restrict J).prod (volume.prod volume))) :
    AEMeasurable (fun t => sectionENorm (volume.prod volume) 2 f t)
      (volume.restrict J) := by
  unfold sectionENorm
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply AEMeasurable.pow_const
  exact (hf.aemeasurable.enorm.pow_const _).lintegral_prod_right'

private lemma aestronglyMeasurable_section_ae
    (J : Set ℝ) (f : Spacetime2)
    (hf : AEStronglyMeasurable f
      ((volume.restrict J).prod (volume.prod volume))) :
    ∀ᵐ t ∂volume.restrict J,
      AEStronglyMeasurable (fun x => f (t, x)) (volume.prod volume) := by
  have hfm : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  have hae := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  filter_upwards [hae] with t ht
  exact ((hfm.comp measurable_prodMk_left).aestronglyMeasurable).congr (by
    filter_upwards [ht] with x hx
    simpa only [Function.comp_apply] using hx.symm)

private lemma sectionENorm_top_aemeasurable
    (J : Set ℝ) (f : Spacetime2)
    (hf : AEStronglyMeasurable f
      ((volume.restrict J).prod (volume.prod volume))) :
    AEMeasurable (fun t => sectionENorm (volume.prod volume) ⊤ f t)
      (volume.restrict J) := by
  have hfm : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  have hm : Measurable (fun t =>
      sectionENorm (volume.prod volume) ⊤ (hf.mk f) t) :=
    measurable_esssup_section (volume.restrict J) (volume.prod volume)
      (hf.mk f) hfm
  have hae := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  exact hm.aemeasurable.congr (by
    filter_upwards [hae] with t ht
    apply eLpNorm_congr_ae
    filter_upwards [ht] with x hx
    exact hx.symm)

private theorem scalarMixedENorm_mul_le_one_two
    (J : Set ℝ) (W Z : Spacetime2)
    (hW : AEStronglyMeasurable W
      ((volume.restrict J).prod (volume.prod volume)))
    (hZ : AEStronglyMeasurable Z
      ((volume.restrict J).prod (volume.prod volume))) :
    scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2
        (fun p => W p * Z p) ≤
      scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 ⊤ W *
        scalarMixedENorm (volume.restrict J) (volume.prod volume) ⊤ 2 Z := by
  let A : ℝ → ℝ≥0∞ := fun t => sectionENorm (volume.prod volume) ⊤ W t
  let B : ℝ → ℝ≥0∞ := fun t => sectionENorm (volume.prod volume) 2 Z t
  have hA : AEStronglyMeasurable A (volume.restrict J) :=
    (sectionENorm_top_aemeasurable J W hW).aestronglyMeasurable
  have hB : AEStronglyMeasurable B (volume.restrict J) :=
    (sectionENorm_two_aemeasurable J Z hZ).aestronglyMeasurable
  have hZsections := aestronglyMeasurable_section_ae J Z hZ
  have hsection : ∀ᵐ t ∂volume.restrict J,
      sectionENorm (volume.prod volume) 2 (fun p => W p * Z p) t ≤
        A t * B t := by
    filter_upwards [hZsections] with t hZt
    unfold sectionENorm A B
    change eLpNorm ((fun x => W (t, x)) • (fun x => Z (t, x))) 2
        (volume.prod volume) ≤
      eLpNorm (fun x => W (t, x)) ⊤ (volume.prod volume) *
        eLpNorm (fun x => Z (t, x)) 2 (volume.prod volume)
    exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hZt
      (fun x => W (t, x))
  unfold scalarMixedENorm
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  simp only [enorm_eq_self]
  have hBbound : ∀ᵐ t ∂volume.restrict J,
      B t ≤ essSup B (volume.restrict J) := ENNReal.ae_le_essSup B
  calc
    (∫⁻ t, sectionENorm (volume.prod volume) 2
        (fun p => W p * Z p) t ∂volume.restrict J) ≤
        ∫⁻ t, A t * B t ∂volume.restrict J := lintegral_mono_ae hsection
    _ ≤ ∫⁻ t, A t * essSup B (volume.restrict J) ∂volume.restrict J := by
      apply lintegral_mono_ae
      filter_upwards [hBbound] with t ht
      exact mul_le_mul_left' ht _
    _ = (∫⁻ t, A t ∂volume.restrict J) * essSup B (volume.restrict J) :=
      lintegral_mul_const'' _ hA.aemeasurable

private lemma scalarMixedENorm_add_le_one_two
    (J : Set ℝ) (f g : Spacetime2)
    (hf : AEStronglyMeasurable f
      ((volume.restrict J).prod (volume.prod volume)))
    (hg : AEStronglyMeasurable g
      ((volume.restrict J).prod (volume.prod volume))) :
    scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2
        (fun p => f p + g p) ≤
      scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2 f +
        scalarMixedENorm (volume.restrict J) (volume.prod volume) 1 2 g := by
  let A := fun t => sectionENorm (volume.prod volume) 2 f t
  let B := fun t => sectionENorm (volume.prod volume) 2 g t
  have hA : AEStronglyMeasurable A (volume.restrict J) :=
    (sectionENorm_two_aemeasurable J f hf).aestronglyMeasurable
  have hB : AEStronglyMeasurable B (volume.restrict J) :=
    (sectionENorm_two_aemeasurable J g hg).aestronglyMeasurable
  have hfm : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  have hgm : Measurable (hg.mk g) := hg.stronglyMeasurable_mk.measurable
  have hsectionsF : ∀ᵐ t ∂volume.restrict J,
      AEStronglyMeasurable (fun x => f (t, x)) (volume.prod volume) := by
    have hae := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
    filter_upwards [hae] with t ht
    exact ((hfm.comp measurable_prodMk_left).aestronglyMeasurable).congr (by
      filter_upwards [ht] with x hx
      simpa only [Function.comp_apply] using hx.symm)
  have hsectionsG : ∀ᵐ t ∂volume.restrict J,
      AEStronglyMeasurable (fun x => g (t, x)) (volume.prod volume) := by
    have hae := Measure.ae_ae_of_ae_prod hg.ae_eq_mk
    filter_upwards [hae] with t ht
    exact ((hgm.comp measurable_prodMk_left).aestronglyMeasurable).congr (by
      filter_upwards [ht] with x hx
      simpa only [Function.comp_apply] using hx.symm)
  unfold scalarMixedENorm
  calc
    eLpNorm
        (fun t => sectionENorm (volume.prod volume) 2 (fun p => f p + g p) t)
        1 (volume.restrict J) ≤
        eLpNorm (fun t => A t + B t) 1 (volume.restrict J) := by
      apply eLpNorm_mono_enorm_ae
      filter_upwards [hsectionsF, hsectionsG] with t hft hgt
      exact eLpNorm_add_le hft hgt (by norm_num)
    _ ≤ eLpNorm A 1 (volume.restrict J) +
        eLpNorm B 1 (volume.restrict J) :=
      eLpNorm_add_le hA hB (by norm_num)

/-- Triangle inequality for the measurable energy source gauge. -/
theorem carlemanXNorm_add_le (J : Set ℝ) (f g : Spacetime2) :
    carlemanXNorm J (fun p => f p + g p) ≤
      carlemanXNorm J f + carlemanXNorm J g := by
  by_cases hf : AEStronglyMeasurable f
      ((volume.restrict J).prod (volume.prod volume))
  · by_cases hg : AEStronglyMeasurable g
        ((volume.restrict J).prod (volume.prod volume))
    · have hsum : AEStronglyMeasurable (fun p => f p + g p)
          ((volume.restrict J).prod (volume.prod volume)) := by
        change AEStronglyMeasurable (f + g)
          ((volume.restrict J).prod (volume.prod volume))
        exact hf.add hg
      simp only [carlemanXNorm, if_pos hf, if_pos hg, if_pos hsum]
      exact scalarMixedENorm_add_le_one_two J f g hf hg
    · simp [carlemanXNorm, hg]
  · simp [carlemanXNorm, hf]

/-- The free two-dimensional Schrödinger differential expression. -/
def schrodinger2D (F : Spacetime2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  Complex.I * deriv (fun t => F (t, p.2)) p.1 +
    iteratedDeriv 2 (fun x => F (p.1, (x, p.2.2))) p.2.1 +
    iteratedDeriv 2 (fun y => F (p.1, (p.2.1, y))) p.2.2

/-- `def:conjugated-operator`: `e^{βz₁} P e^{-βz₁}`. -/
def conjugatedOperator (β : ℝ) (F : Spacetime2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  schrodinger2D F p -
    ((2 * β : ℝ) : ℂ) * deriv (fun x => F (p.1, (x, p.2.2))) p.2.1 +
    ((β ^ 2 : ℝ) : ℂ) * F p

/-- Raw spatial Fourier section, using Mathlib's `2π` convention. -/
def spatialFourierSection (f : Spacetime2) (t : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  ∫ z : ℝ × ℝ,
    Complex.exp (-Complex.I * ((2 * Real.pi * (ξ.1 * z.1 + ξ.2 * z.2) : ℝ) : ℂ)) *
      f (t, z) ∂(volume.prod volume)

/-- Frequency-side selected-branch inverse of the conjugated operator. -/
def TbetaHat (β : ℝ) (f : Spacetime2) (t : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  let a : ℝ := β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2)
  if ξ.1 < 0 then
    -Complex.I * ∫ s in Set.Iic t,
      Complex.exp ((Complex.I * (a : ℂ) + ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) *
        (t - s)) *
        spatialFourierSection f s ξ
  else if 0 < ξ.1 then
    Complex.I * ∫ s in Set.Ici t,
      Complex.exp ((Complex.I * (a : ℂ) + ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) *
        (t - s)) *
        spatialFourierSection f s ξ
  else 0

/-- `def:Tbeta`: inverse spatial Fourier realization of the selected branch. -/
def Tbeta (β : ℝ) (f : Spacetime2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∫ ξ : ℝ × ℝ,
    Complex.exp (Complex.I *
      ((2 * Real.pi * (ξ.1 * p.2.1 + ξ.2 * p.2.2) : ℝ) : ℂ)) *
      TbetaHat β f p.1 ξ ∂(volume.prod volume)

/-- Fourier symbol of the time-increment kernel. -/
def TbetaSymbol (β τ : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  if τ * ξ.1 < 0 then
    -Complex.I * Complex.exp
      ((Complex.I *
          ((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) +
        ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) * τ)
  else 0

/-- `lem:Tbeta-symbol`: branch support, damping, and the `L²` multiplier bound. -/
theorem Tbeta_symbol (β τ : ℝ) (hβ : 0 < β) (hτ : τ ≠ 0) :
  (∀ ξ : ℝ × ℝ, τ * ξ.1 ≥ 0 → TbetaSymbol β τ ξ = 0) ∧
  (∀ ξ : ℝ × ℝ, ‖TbetaSymbol β τ ξ‖ ≤ 1) := by
  constructor
  · intro ξ hξ
    simp [TbetaSymbol, not_lt.mpr hξ]
  · intro ξ
    rw [TbetaSymbol]
    split_ifs with hξ
    · have hnormI : ‖-Complex.I‖ = 1 := by norm_num
      rw [norm_mul, hnormI, one_mul, Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, neg_mul, zero_mul,
        sub_zero, mul_zero, add_zero]
      have hcoef : 0 < 4 * Real.pi * β := by positivity
      have hprod : 4 * Real.pi * β * ξ.1 * τ < 0 := by
        rw [show 4 * Real.pi * β * ξ.1 * τ =
          (4 * Real.pi * β) * (τ * ξ.1) by ring]
        exact mul_neg_of_pos_of_neg hcoef hξ
      simpa only [zero_add] using hprod.le
    · simp

/-- Kernel action defined directly from the multiplier symbol. -/
def Kbeta (β τ : ℝ) (g : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  ∫ ξ : ℝ × ℝ,
    Complex.exp (Complex.I * ((2 * Real.pi * (ξ.1 * z.1 + ξ.2 * z.2) : ℝ) : ℂ)) *
      TbetaSymbol β τ ξ *
      (∫ y : ℝ × ℝ,
        Complex.exp (-Complex.I * ((2 * Real.pi * (ξ.1 * y.1 + ξ.2 * y.2) : ℝ) : ℂ)) *
          g y ∂(volume.prod volume)) ∂(volume.prod volume)

/-- `lem:XY-multiplier`: potential multiplication sends `Y × X'` into `X`. -/
theorem XY_multiplier :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (J : Set ℝ) (W Z : Spacetime2),
    carlemanYNorm J W < ⊤ → carlemanXprimeNorm J Z < ⊤ →
    carlemanXNorm J (fun p => W p * Z p) ≤
      C * carlemanYNorm J W * carlemanXprimeNorm J Z := by
  refine ⟨1, by norm_num, ?_⟩
  intro J W Z hWfinite hZfinite
  have hWmeas : AEStronglyMeasurable W
      ((volume.restrict J).prod (volume.prod volume)) := by
    by_contra hn
    simp [carlemanYNorm, hn] at hWfinite
  have hZmeas : AEStronglyMeasurable Z
      ((volume.restrict J).prod (volume.prod volume)) := by
    by_contra hn
    simp [carlemanXprimeNorm, hn] at hZfinite
  have hmul : AEStronglyMeasurable (fun p => W p * Z p)
      ((volume.restrict J).prod (volume.prod volume)) := by
    change AEStronglyMeasurable (W * Z)
      ((volume.restrict J).prod (volume.prod volume))
    exact hWmeas.mul hZmeas
  simp only [carlemanXNorm, if_pos hmul,
    carlemanYNorm, if_pos hWmeas,
    carlemanXprimeNorm, if_pos hZmeas]
  simpa only [one_mul] using
    scalarMixedENorm_mul_le_one_two J W Z hWmeas hZmeas

/-- Exponential weight in the first spatial coordinate. -/
def exponentialWeight (β : ℝ) (F : Spacetime2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  Complex.exp ((β * p.2.1 : ℝ) : ℂ) * F p

/-- Spatial convolution by a two-dimensional kernel. -/
def spatialConvolution (ρ : ℝ × ℝ → ℂ) (f : Spacetime2)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∫ z : ℝ × ℝ, ρ (p.2 - z) * f (p.1, z) ∂(volume.prod volume)

/-- Standard two-dimensional rescaling of a mollifier. -/
def scaledMollifier (ρ : ℝ × ℝ → ℂ) (ε : ℝ) (z : ℝ × ℝ) : ℂ :=
  (((ε⁻¹) ^ 2 : ℝ) : ℂ) * ρ (ε⁻¹ • z)

/-- Distributional scalar first-order ODE. -/
def IsWeakFirstOrderODE (y : ℝ → ℂ) (lam : ℂ) (g : ℝ → ℂ) : Prop :=
  ∀ η : 𝓢(ℝ, ℂ),
    ∫ t, y t * (-deriv (η : ℝ → ℂ) t - lam * η t) = ∫ t, g t * η t

/-- Weak parameter-family ODE, tested by separated Schwartz functions. -/
def IsWeakParameterODE (y : ℝ × (ℝ × ℝ) → ℂ)
    (lam : ℝ × ℝ → ℂ) (g : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ (η : 𝓢(ℝ, ℂ)) (φ : 𝓢(ℝ × ℝ, ℂ)),
    ∫ ξ, ∫ t, y (t, ξ) *
      (-deriv (η : ℝ → ℂ) t - lam ξ * η t) * φ ξ ∂volume ∂(volume.prod volume) =
      ∫ ξ, ∫ t, g (t, ξ) * η t * φ ξ ∂volume ∂(volume.prod volume)

/-- A field is supported in a bounded time interval. -/
def HasBoundedTimeSupport (F : Spacetime2) : Prop :=
  ∃ a b : ℝ, a < b ∧ ∀ᵐ p ∂(volume.prod (volume.prod volume)),
    p.1 ∉ Set.Icc a b → F p = 0

/-- The formal adjoint of `i∂ₜ + Δ` applied to a scalar test function. -/
def schrodinger2DAdjointTest (Ψ : Spacetime2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  -Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
    iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
    iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2

/-- Weak free Schrödinger equation `P U = R`.

The integrability fields are part of the predicate.  This is essential:
Mathlib's Bochner integral is defined to be zero for non-integrable functions,
so a bare equality of integrals is not a sound distributional interface.  We
test against smooth compactly supported scalar functions, the standard
`C_c^∞` definition of a distributional solution. -/
def IsWeakSchrodinger2D (U R : Spacetime2) : Prop :=
  ∀ Ψ : Spacetime2, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ →
    Integrable (fun p => U p * Ψ p) (volume.prod (volume.prod volume)) ∧
    Integrable (fun p => U p * schrodinger2DAdjointTest Ψ p)
      (volume.prod (volume.prod volume)) ∧
    Integrable (fun p => R p * Ψ p) (volume.prod (volume.prod volume)) ∧
    (∫ p, U p * schrodinger2DAdjointTest Ψ p
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, R p * Ψ p ∂(volume.prod (volume.prod volume))

/-- Weak form of the conjugated equation
`(i∂ₜ + Δ - 2β∂₁ + β²) U = R`, using Mathlib's physical spatial
coordinates.  The first-order term changes sign in the adjoint test. -/
def IsWeakConjugatedSchrodinger2D (β : ℝ) (U R : Spacetime2) : Prop :=
  ∀ Ψ : 𝓢(ℝ × (ℝ × ℝ), ℂ),
    ∫ p, U p *
      (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
        iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
        iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2 +
        ((2 * β : ℝ) : ℂ) * deriv (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
        ((β ^ 2 : ℝ) : ℂ) * Ψ p)
        ∂(volume.prod (volume.prod volume)) =
      ∫ p, R p * Ψ p ∂(volume.prod (volume.prod volume))

/-- The weak two-dimensional Schrödinger equation tested only inside a time
set.  As in the global predicate, both distributional pairings are required
to be genuinely Bochner-integrable. -/
def IsWeakSchrodinger2DOn (J : Set ℝ) (U R : Spacetime2) : Prop :=
  ∀ Ψ : Spacetime2, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ →
    (∀ p ∈ tsupport Ψ, p.1 ∈ J) →
    Integrable (fun p => U p * Ψ p) ∧
    Integrable (fun p => U p * schrodinger2DAdjointTest Ψ p) ∧
    Integrable (fun p => R p * Ψ p) ∧
    (∫ p, U p * schrodinger2DAdjointTest Ψ p
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, R p * Ψ p ∂(volume.prod (volume.prod volume))

/-- Vanishing above a fixed vertical half-space. -/
def VanishesAbove (H : ℝ) (U : Spacetime2) : Prop :=
  ∀ᵐ p ∂(volume.prod (volume.prod volume)), H < p.2.1 → U p = 0

/-- The proposition asserted by `lem:carleman-closure`: graph closure of the
smooth Carleman estimate.

The weighted graph-membership premise is mathematically essential. It says
that the solution side is an actual `L∞ₜL²_z` representative, rather than a
raw function for which `carlemanXprimeNorm` is `⊤`. The unique-continuation
consumer already supplies precisely this premise for every positive weight. -/
def CarlemanClosureStatement : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (β H : ℝ), 0 < β → ∀ (U R : Spacetime2),
    HasBoundedTimeSupport U → VanishesAbove H U →
    IsWeakSchrodinger2D U R →
    carlemanXprimeNorm Set.univ (exponentialWeight β U) < ⊤ →
    carlemanXNorm Set.univ (exponentialWeight β R) < ⊤ →
    carlemanXprimeNorm Set.univ (exponentialWeight β U) ≤
      C * carlemanXNorm Set.univ (exponentialWeight β R)

/-- `lem:exponential-separation`: small potentials force vanishing past the interface.

The explicit weighted-`X'` finiteness premise is essential for sound
absorption in `ℝ≥0∞`: without it the Carleman inequality can reduce to the
vacuous statement `∞ ≤ ∞`.  In the propagation argument this premise follows
from the unweighted local `X'` bound and the upper half-space support. -/
theorem exponential_separation_of_carleman_closure
    (hcarleman : CarlemanClosureStatement) :
  ∃ εstar : ℝ≥0∞, 0 < εstar ∧ ∀ (H : ℝ) (U V R : Spacetime2),
    HasBoundedTimeSupport U → VanishesAbove H U →
    IsWeakSchrodinger2D U (fun p => V p * U p + R p) →
    (∀ β : ℝ, 0 < β →
      carlemanXprimeNorm Set.univ (exponentialWeight β U) < ⊤) →
    carlemanYNorm Set.univ V ≤ εstar →
    Tendsto (fun β : ℝ => carlemanXNorm Set.univ (exponentialWeight β R)) atTop (nhds 0) →
    ∀ᵐ p ∂(volume.prod (volume.prod volume)), 0 < p.2.1 → U p = 0 := by
  obtain ⟨Ccl, hCcltop, hclosure⟩ := hcarleman
  obtain ⟨Cmul, hCmultop, hmultiplier⟩ := XY_multiplier
  let d : ℝ≥0∞ := Ccl * Cmul
  let εstar : ℝ≥0∞ := min 1 (2 * d)⁻¹
  have hdtop : d < ⊤ := ENNReal.mul_lt_top hCcltop hCmultop
  have hinvpos : 0 < (2 * d)⁻¹ := ENNReal.inv_pos.2 (by
    exact ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hdtop.ne)
  have hεstar : 0 < εstar := by
    dsimp only [εstar]
    exact lt_min (by norm_num) hinvpos
  refine ⟨εstar, hεstar, ?_⟩
  intro H U V R hUtime hUzero hweak hUfinite hVsmall hRzero
  let A : ℝ → ℝ≥0∞ := fun β =>
    carlemanXprimeNorm Set.univ (exponentialWeight β U)
  let E : ℝ → ℝ≥0∞ := fun β =>
    carlemanXNorm Set.univ (exponentialWeight β R)
  have hcoefficient : d * carlemanYNorm Set.univ V ≤ 1 / 2 := by
    by_cases hd0 : d = 0
    · simp [hd0]
    calc
      d * carlemanYNorm Set.univ V ≤ d * (2 * d)⁻¹ := by
        exact mul_le_mul_left' (hVsmall.trans (min_le_right _ _)) d
      _ = (d * d⁻¹) * 2⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        ac_rfl
      _ = 1 / 2 := by
        rw [ENNReal.mul_inv_cancel hd0 hdtop.ne]
        norm_num
  have hestimate (β : ℝ) (hβ : 0 < β) (hEtop : E β < ⊤) :
      A β ≤ 2 * Ccl * E β := by
    have hclose := hclosure β H hβ U (fun p => V p * U p + R p)
      hUtime hUzero hweak (hUfinite β hβ)
    have hsource : exponentialWeight β (fun p => V p * U p + R p) =
        fun p => V p * exponentialWeight β U p + exponentialWeight β R p := by
      funext p
      unfold exponentialWeight
      ring
    rw [hsource] at hclose
    have hadd := carlemanXNorm_add_le Set.univ
      (fun p => V p * exponentialWeight β U p) (exponentialWeight β R)
    have hVfinite : carlemanYNorm Set.univ V < ⊤ :=
      hVsmall.trans_lt ((min_le_left _ _).trans_lt (by norm_num))
    have hmul := hmultiplier Set.univ V (exponentialWeight β U)
      hVfinite (hUfinite β hβ)
    have hraw : A β ≤ (d * carlemanYNorm Set.univ V) * A β + Ccl * E β := by
      have hsourceFinite : carlemanXNorm Set.univ
          (exponentialWeight β (fun p => V p * U p + R p)) < ⊤ := by
        rw [hsource]
        exact (carlemanXNorm_add_le Set.univ
          (fun p => V p * exponentialWeight β U p)
          (exponentialWeight β R)).trans_lt
            (ENNReal.add_lt_top.2 ⟨
              (hmultiplier Set.univ V (exponentialWeight β U)
                hVfinite (hUfinite β hβ)).trans_lt
                  (ENNReal.mul_lt_top
                    (ENNReal.mul_lt_top hCmultop hVfinite)
                    (hUfinite β hβ)),
              hEtop⟩)
      rw [hsource] at hsourceFinite
      specialize hclose hsourceFinite
      calc
        A β ≤ Ccl * carlemanXNorm Set.univ
            (fun p => V p * exponentialWeight β U p + exponentialWeight β R p) := by
          simpa only [A] using hclose
        _ ≤ Ccl * (carlemanXNorm Set.univ
              (fun p => V p * exponentialWeight β U p) + E β) := by
          exact mul_le_mul_left' (by simpa only [E] using hadd) Ccl
        _ ≤ Ccl * ((Cmul * carlemanYNorm Set.univ V * A β) + E β) := by
          apply mul_le_mul_left'
          exact add_le_add (by simpa only [A] using hmul) le_rfl
        _ = (d * carlemanYNorm Set.univ V) * A β + Ccl * E β := by
          dsimp only [d]
          ring
    have hhalf : A β / 2 ≤ Ccl * E β := by
      have hAfin : A β < ⊤ := hUfinite β hβ
      rw [← ENNReal.sub_half hAfin.ne]
      apply (tsub_le_iff_left).2
      calc
        A β ≤ (d * carlemanYNorm Set.univ V) * A β + Ccl * E β := hraw
        _ ≤ (1 / 2) * A β + Ccl * E β := by
          exact add_le_add (mul_le_mul_right' hcoefficient (A β)) le_rfl
        _ = A β / 2 + Ccl * E β := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
          norm_num
    calc
      A β = A β / 2 + A β / 2 := (ENNReal.add_halves (A β)).symm
      _ ≤ Ccl * E β + Ccl * E β := add_le_add hhalf hhalf
      _ = 2 * Ccl * E β := by ring
  have hEfinite : ∀ᶠ β : ℝ in atTop, E β < ⊤ := by
    have h := (tendsto_order.1 hRzero).2 ⊤ (by simp)
    simpa only [E] using h
  have hAupper : ∀ᶠ β : ℝ in atTop, A β ≤ 2 * Ccl * E β := by
    filter_upwards [hEfinite, eventually_gt_atTop (0 : ℝ)] with β hEtop hβ
    exact hestimate β hβ hEtop
  have hupperZero : Tendsto (fun β => 2 * Ccl * E β) atTop (nhds 0) := by
    have hEtend : Tendsto E atTop (nhds 0) := by
      simpa only [E] using hRzero
    have hc : (2 * Ccl : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hCcltop.ne
    change Tendsto ((fun x : ℝ≥0∞ => (2 * Ccl) * x) ∘ E) atTop (nhds 0)
    simpa only [mul_zero] using
      (ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp hEtend
  have hAzero : Tendsto A atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperZero
      (Filter.Eventually.of_forall fun _ => bot_le) hAupper
  let S : Set (ℝ × (ℝ × ℝ)) := {p | 0 < p.2.1}
  let Upos : Spacetime2 := S.indicator U
  have hweightedFinite : A 1 < ⊤ := hUfinite 1 (by norm_num)
  have hweightedMeas : AEStronglyMeasurable (exponentialWeight 1 U)
      ((volume.restrict Set.univ).prod (volume.prod volume)) := by
    by_contra hn
    change carlemanXprimeNorm Set.univ (exponentialWeight 1 U) < ⊤ at hweightedFinite
    rw [carlemanXprimeNorm, if_neg hn] at hweightedFinite
    exact (lt_irrefl ⊤ hweightedFinite)
  have hUmeas : AEStronglyMeasurable U
      (volume.prod (volume.prod volume)) := by
    have hm : AEStronglyMeasurable
        (fun p : ℝ × (ℝ × ℝ) => Complex.exp ((-p.2.1 : ℝ) : ℂ))
        (volume.prod (volume.prod volume)) :=
      (by fun_prop : Measurable
        (fun p : ℝ × (ℝ × ℝ) => Complex.exp ((-p.2.1 : ℝ) : ℂ))).aestronglyMeasurable
    have hw : AEStronglyMeasurable (exponentialWeight 1 U)
        (volume.prod (volume.prod volume)) := by
      simpa only [Measure.restrict_univ] using hweightedMeas
    exact (hm.mul hw).congr (Filter.Eventually.of_forall fun p => by
      unfold exponentialWeight
      change Complex.exp ((-p.2.1 : ℝ) : ℂ) *
          (Complex.exp ((1 * p.2.1 : ℝ) : ℂ) * U p) = U p
      rw [← mul_assoc, ← Complex.exp_add]
      simp)
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)
  have hUposMeas : AEStronglyMeasurable Upos
      (volume.prod (volume.prod volume)) := hUmeas.indicator hS
  let B : ℝ≥0∞ :=
    scalarMixedENorm volume (volume.prod volume) ⊤ 2 Upos
  have hBupper : ∀ᶠ β : ℝ in atTop, B ≤ A β := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
    have hpoint : ∀ p : ℝ × (ℝ × ℝ), ‖Upos p‖ₑ ≤
        ‖exponentialWeight β U p‖ₑ := by
      intro p
      by_cases hp : p ∈ S
      · have hp0 : 0 ≤ p.2.1 := by
          change 0 < p.2.1 at hp
          exact hp.le
        have hexp : 1 ≤ Real.exp (β * p.2.1) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hβ hp0)
        rw [show Upos p = U p by simp [Upos, hp]]
        unfold exponentialWeight
        rw [← ofReal_norm, ← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul, Complex.norm_exp]
        simp only [Complex.ofReal_re]
        exact le_mul_of_one_le_left (norm_nonneg _) hexp
      · simp [Upos, hp]
    calc
      B ≤ scalarMixedENorm volume (volume.prod volume) ⊤ 2
          (exponentialWeight β U) := by
        unfold B scalarMixedENorm sectionENorm
        apply eLpNorm_mono_enorm
        intro t
        apply eLpNorm_mono_enorm
        intro z
        exact hpoint (t, z)
      _ ≤ A β := by
        have hmeas : AEStronglyMeasurable (exponentialWeight β U)
            ((volume.restrict Set.univ).prod (volume.prod volume)) := by
          rcases hβ.lt_or_eq with hβpos | hβzero
          · by_contra hn
            have hf := hUfinite β hβpos
            rw [carlemanXprimeNorm, if_neg hn] at hf
            exact lt_irrefl ⊤ hf
          · subst β
            have hz : AEStronglyMeasurable (exponentialWeight 0 U)
                (volume.prod (volume.prod volume)) :=
              hUmeas.congr (Filter.Eventually.of_forall fun p => by
                simp [exponentialWeight])
            simpa only [Measure.restrict_univ] using hz
        change scalarMixedENorm volume (volume.prod volume) ⊤ 2
            (exponentialWeight β U) ≤
          carlemanXprimeNorm Set.univ (exponentialWeight β U)
        rw [carlemanXprimeNorm, if_pos hmeas]
        simp only [Measure.restrict_univ]
        exact le_rfl
  have hBzeroTendsto : Tendsto (fun _ : ℝ => B) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAzero
      (Filter.Eventually.of_forall fun _ => bot_le) hBupper
  have hBzero : B = 0 := tendsto_nhds_unique tendsto_const_nhds hBzeroTendsto
  have hUposZero : Upos =ᵐ[volume.prod (volume.prod volume)] 0 := by
    have hUposMeas' : AEStronglyMeasurable Upos
        ((volume.restrict Set.univ).prod (volume.prod volume)) := by
      simpa only [Measure.restrict_univ] using hUposMeas
    have hsectionMeas : AEStronglyMeasurable
        (fun t => sectionENorm (volume.prod volume) 2 Upos t) volume := by
      simpa only [Measure.restrict_univ] using
        (sectionENorm_two_aemeasurable Set.univ Upos hUposMeas').aestronglyMeasurable
    have hsectionZero :
        (fun t => sectionENorm (volume.prod volume) 2 Upos t) =ᵐ[volume] 0 := by
      apply (eLpNorm_eq_zero_iff hsectionMeas (by simp : (⊤ : ℝ≥0∞) ≠ 0)).1
      simpa only [B, scalarMixedENorm] using hBzero
    have hslicesMeas : ∀ᵐ t ∂volume,
        AEStronglyMeasurable (fun z => Upos (t, z)) (volume.prod volume) := by
      simpa only [Measure.restrict_univ] using
        aestronglyMeasurable_section_ae Set.univ Upos hUposMeas'
    let M : Spacetime2 := hUposMeas.mk Upos
    have hUM : Upos =ᵐ[volume.prod (volume.prod volume)] M := hUposMeas.ae_eq_mk
    have hsliceEq : ∀ᵐ t ∂volume,
        (fun z => Upos (t, z)) =ᵐ[volume.prod volume] fun z => M (t, z) :=
      Measure.ae_ae_of_ae_prod hUM
    have hMzeroSlices : ∀ᵐ t ∂volume, ∀ᵐ z ∂volume.prod volume,
        M (t, z) = 0 := by
      filter_upwards [hsectionZero, hslicesMeas, hsliceEq] with t ht hmt heq
      have hz : (fun z => Upos (t, z)) =ᵐ[volume.prod volume] 0 := by
        apply (eLpNorm_eq_zero_iff hmt (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1
        change sectionENorm (volume.prod volume) 2 Upos t = 0 at ht
        simpa only [sectionENorm] using ht
      filter_upwards [heq, hz] with z heqz hzz
      rw [← heqz]
      exact hzz
    have hMzero : M =ᵐ[volume.prod (volume.prod volume)] 0 := by
      change ∀ᵐ p ∂volume.prod (volume.prod volume), M p = 0
      rw [Measure.ae_prod_iff_ae_ae]
      · exact hMzeroSlices
      · exact measurableSet_eq_fun
          hUposMeas.stronglyMeasurable_mk.measurable measurable_const
    exact hUM.trans hMzero
  filter_upwards [hUposZero] with p hp
  intro hpositive
  have hpS : p ∈ S := hpositive
  simpa [Upos, hpS] using hp

end CubicNLSPhaseRetrieval
