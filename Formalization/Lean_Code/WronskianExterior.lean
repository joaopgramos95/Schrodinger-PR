import Lean_Code.DensityCurrent
import Lean_Code.WeakMild
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Wronskian and the exterior product

Blueprint chapter: `chap:wronskian-exterior` (module 10).
Imports: modules 7, 8, and 9.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The two-particle `L²(ℝ²)` space. -/
abbrev TwoParticleL2 := Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))

/-- Bundled tensor product of two one-particle `L²` functions. -/
def tensorProductL2 (f g : L2) : TwoParticleL2 :=
  (tensor_norm f g).1.toLp
    (fun p : ℝ × ℝ => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2)

lemma coe_tensorProductL2 (f g : L2) :
    (tensorProductL2 f g : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun p => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2 :=
  MemLp.coeFn_toLp _

lemma norm_tensorProductL2 (f g : L2) : ‖tensorProductL2 f g‖ = ‖f‖ * ‖g‖ := by
  rw [tensorProductL2, Lp.norm_toLp, (tensor_norm f g).2, Lp.norm_def, Lp.norm_def,
    ENNReal.toReal_mul]

private noncomputable def tensorProductLinear :
    L2 →ₗ[ℂ] L2 →ₗ[ℂ] TwoParticleL2 :=
  LinearMap.mk₂ ℂ tensorProductL2
    (fun f1 f2 g => by
      apply Lp.ext
      have hadd := (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae (Lp.coeFn_add f1 f2)
      filter_upwards [coe_tensorProductL2 (f1 + f2) g, coe_tensorProductL2 f1 g,
        coe_tensorProductL2 f2 g, hadd,
        Lp.coeFn_add (tensorProductL2 f1 g) (tensorProductL2 f2 g)]
      with p h h1 h2 hadd hout
      simp only [h, h1, h2, hadd, hout, Pi.add_apply]
      ring)
    (fun c f g => by
      apply Lp.ext
      have hsmul := (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae (Lp.coeFn_smul c f)
      filter_upwards [coe_tensorProductL2 (c • f) g, coe_tensorProductL2 f g,
        hsmul, Lp.coeFn_smul c (tensorProductL2 f g)]
      with p h hfg hf hout
      simp only [h, hfg, hf, hout, Pi.smul_apply]
      ring)
    (fun f g1 g2 => by
      apply Lp.ext
      have hadd := (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae (Lp.coeFn_add g1 g2)
      filter_upwards [coe_tensorProductL2 f (g1 + g2), coe_tensorProductL2 f g1,
        coe_tensorProductL2 f g2, hadd,
        Lp.coeFn_add (tensorProductL2 f g1) (tensorProductL2 f g2)]
      with p h h1 h2 hadd hout
      simp only [h, h1, h2, hadd, hout, Pi.add_apply]
      ring)
    (fun c f g => by
      apply Lp.ext
      have hsmul := (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae (Lp.coeFn_smul c g)
      filter_upwards [coe_tensorProductL2 f (c • g), coe_tensorProductL2 f g,
        hsmul, Lp.coeFn_smul c (tensorProductL2 f g)]
      with p h hfg hg hout
      simp only [h, hfg, hg, hout, Pi.smul_apply]
      ring)

/-- Continuous bilinear tensor product. -/
noncomputable def tensorProductCLM : L2 →L[ℂ] L2 →L[ℂ] TwoParticleL2 :=
  tensorProductLinear.mkContinuous₂ 1 (fun f g => by
    change ‖tensorProductL2 f g‖ ≤ 1 * ‖f‖ * ‖g‖
    rw [norm_tensorProductL2, one_mul])

/-- The same tensor product regarded as a real-bilinear map, for calculus in
the real time variable. -/
private noncomputable def tensorProductRealLinear :
    L2 →ₗ[ℝ] L2 →ₗ[ℝ] TwoParticleL2 :=
  LinearMap.mk₂ ℝ tensorProductL2
    (fun f₁ f₂ g => by
      change tensorProductCLM (f₁ + f₂) g =
        tensorProductCLM f₁ g + tensorProductCLM f₂ g
      simp)
    (fun c f g => by
      change tensorProductCLM ((c : ℂ) • f) g =
        (c : ℂ) • tensorProductCLM f g
      simpa only [map_smul, ContinuousLinearMap.smul_apply])
    (fun f g₁ g₂ => by
      change tensorProductCLM f (g₁ + g₂) =
        tensorProductCLM f g₁ + tensorProductCLM f g₂
      simp)
    (fun c f g => by
      change tensorProductCLM f ((c : ℂ) • g) =
        (c : ℂ) • tensorProductCLM f g
      simpa only [map_smul])

private noncomputable def tensorProductRealCLM :
    L2 →L[ℝ] L2 →L[ℝ] TwoParticleL2 :=
  tensorProductRealLinear.mkContinuous₂ 1 (fun f g => by
    change ‖tensorProductL2 f g‖ ≤ 1 * ‖f‖ * ‖g‖
    rw [norm_tensorProductL2, one_mul])

lemma tensorProductRealCLM_eq_tensorProductL2 (f g : L2) :
    tensorProductRealCLM f g = tensorProductL2 f g := rfl

lemma tensorProductL2_smul_left (c : ℂ) (f g : L2) :
    tensorProductL2 (c • f) g = c • tensorProductL2 f g := by
  change tensorProductCLM (c • f) g = c • tensorProductCLM f g
  simpa only [map_smul, ContinuousLinearMap.smul_apply]

lemma tensorProductL2_smul_right (c : ℂ) (f g : L2) :
    tensorProductL2 f (c • g) = c • tensorProductL2 f g := by
  change tensorProductCLM f (c • g) = c • tensorProductCLM f g
  rw [map_smul]

/-- Bundled antisymmetric exterior product. -/
noncomputable def exteriorProductL2 (f g : L2) : TwoParticleL2 :=
  tensorProductCLM f g - tensorProductCLM g f

lemma coe_exteriorProductL2 (f g : L2) :
    (exteriorProductL2 f g : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun p => (f : ℝ → ℂ) p.1 * (g : ℝ → ℂ) p.2 -
        (g : ℝ → ℂ) p.1 * (f : ℝ → ℂ) p.2 := by
  filter_upwards [coe_tensorProductL2 f g, coe_tensorProductL2 g f,
    Lp.coeFn_sub (tensorProductCLM f g) (tensorProductCLM g f)] with p hfg hgf hout
  simpa [exteriorProductL2, tensorProductCLM, tensorProductLinear] using
    hout.trans (congrArg₂ (· - ·) hfg hgf)

lemma continuous_exteriorProductL2 (u v : ℝ → L2) (hu : Continuous u)
    (hv : Continuous v) : Continuous (fun t => exteriorProductL2 (u t) (v t)) := by
  apply Continuous.sub
  · exact Continuous.clm_apply (tensorProductCLM.continuous.comp hu)
      hv
  · exact Continuous.clm_apply (tensorProductCLM.continuous.comp hv)
      hu

/-- The exterior product of two interaction-picture solution curves is
absolutely continuous on compact time intervals. -/
theorem interaction_exterior_absolutelyContinuousOnInterval (sigma : ℝ)
    (u v : GlobalSolution sigma) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => exteriorProductL2 (freeProp (-t) (u.u t))
        (freeProp (-t) (v.u t))) a b := by
  have hu := interaction_curve_absolutelyContinuousOnInterval sigma u a b
  have hv := interaction_curve_absolutelyContinuousOnInterval sigma v a b
  change AbsolutelyContinuousOnInterval
    (fun t => tensorProductRealCLM (freeProp (-t) (u.u t))
          (freeProp (-t) (v.u t)) -
        tensorProductRealCLM (freeProp (-t) (v.u t))
          (freeProp (-t) (u.u t))) a b
  exact (AbsolutelyContinuousOnInterval.clm_apply hu hv tensorProductRealCLM).sub
    (AbsolutelyContinuousOnInterval.clm_apply hv hu tensorProductRealCLM)

/-- Product rule for the exterior interaction curve. -/
theorem interaction_exterior_ae_hasDerivAt (sigma : ℝ)
    (u v : GlobalSolution sigma) (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt
        (fun s => exteriorProductL2 (freeProp (-s) (u.u s))
          (freeProp (-s) (v.u s)))
        ((tensorProductRealCLM
              (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (u.nonlin t))
              (freeProp (-t) (v.u t)) +
            tensorProductRealCLM (freeProp (-t) (u.u t))
              (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (v.nonlin t))) -
          (tensorProductRealCLM
              (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (v.nonlin t))
              (freeProp (-t) (u.u t)) +
            tensorProductRealCLM (freeProp (-t) (v.u t))
              (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (u.nonlin t)))) t := by
  have hu := interaction_curve_ae_hasDerivAt sigma u a b
  have hv := interaction_curve_ae_hasDerivAt sigma v a b
  filter_upwards [hu, hv] with t hut hvt htmem
  have hut' := hut htmem
  have hvt' := hvt htmem
  have huTensor : HasDerivAt
      (fun s => tensorProductRealCLM (freeProp (-s) (u.u s)))
      (tensorProductRealCLM
        (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (u.nonlin t))) t := by
    exact tensorProductRealCLM.hasFDerivAt.comp_hasDerivAt t hut'
  have hvTensor : HasDerivAt
      (fun s => tensorProductRealCLM (freeProp (-s) (v.u s)))
      (tensorProductRealCLM
        (-(Complex.I * (sigma : ℂ)) • freeProp (-t) (v.nonlin t))) t := by
    exact tensorProductRealCLM.hasFDerivAt.comp_hasDerivAt t hvt'
  change HasDerivAt
    (fun s => tensorProductRealCLM (freeProp (-s) (u.u s))
          (freeProp (-s) (v.u s)) -
        tensorProductRealCLM (freeProp (-s) (v.u s))
          (freeProp (-s) (u.u s))) _ t
  exact (huTensor.clm_apply hvt').sub (hvTensor.clm_apply hut')

/-- `def:exterior-product`: the two-particle antisymmetric product. -/
def exteriorProduct (u v : ℝ → L2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (u p.1 : ℝ → ℂ) p.2.1 * (v p.1 : ℝ → ℂ) p.2.2 -
    (v p.1 : ℝ → ℂ) p.2.1 * (u p.1 : ℝ → ℂ) p.2.2

/-- Distributional adjoint of `i∂t + ∂x² + ∂y²` on a test function. -/
def twoParticleAdjointTest (Ψ : 𝓢(ℝ × (ℝ × ℝ), ℂ))
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  -Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
    iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
    iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2

/-- Weak two-particle Schrödinger equation on spacetime, including the
integrability needed for both distributional pairings. -/
def IsWeakTwoParticleEquation (F R : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ Ψ : ℝ × (ℝ × ℝ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ →
    Integrable (fun p => F p * Ψ p) (volume.prod (volume.prod volume)) ∧
    Integrable (fun p => F p *
      (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
        iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
        iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2))
      (volume.prod (volume.prod volume)) ∧
    Integrable (fun p => R p * Ψ p) (volume.prod (volume.prod volume)) ∧
    (∫ p, F p *
      (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
        iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
        iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2)
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, R p * Ψ p ∂(volume.prod (volume.prod volume))

/-- The weak two-particle equation tested only inside a time set. -/
def IsWeakTwoParticleEquationOn (I : Set ℝ) (F R : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ Ψ : ℝ × (ℝ × ℝ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ →
    (∀ p ∈ tsupport Ψ, p.1 ∈ I) →
    Integrable (fun p => F p * Ψ p) (volume.prod (volume.prod volume)) ∧
    Integrable (fun p => F p *
      (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
        iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
        iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2))
      (volume.prod (volume.prod volume)) ∧
    Integrable (fun p => R p * Ψ p) (volume.prod (volume.prod volume)) ∧
    (∫ p, F p *
      (-Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
        iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
        iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2)
        ∂(volume.prod (volume.prod volume))) =
      ∫ p, R p * Ψ p ∂(volume.prod (volume.prod volume))

/-- The factored two-particle forcing `σ(ρ(x)+ρ(y))F`. -/
def exteriorForcing (σ : ℝ) (u v : ℝ → L2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ((σ * (‖(u p.1 : ℝ → ℂ) p.2.1‖ ^ 2 +
      ‖(u p.1 : ℝ → ℂ) p.2.2‖ ^ 2) : ℝ) : ℂ) * exteriorProduct u v p

/-- Orthogonal map from normal/tangential `(s,r)` to particle `(x,y)` coordinates.
The normal coordinate is placed first so the half-space theorem applies without
an additional coordinate reflection. -/
def fromNormalCoordinates (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (p.1, ((p.2.2 + p.2.1) / Real.sqrt 2, (p.2.2 - p.2.1) / Real.sqrt 2))

/-- The spatial part of `fromNormalCoordinates`, bundled as a real linear
equivalence.  Its inverse sends `(x,y)` to the normal/tangential coordinates
`((x-y)/√2,(x+y)/√2)`. -/
noncomputable def normalToParticle : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun z := ((z.2 + z.1) / Real.sqrt 2, (z.2 - z.1) / Real.sqrt 2)
  invFun z := ((z.1 - z.2) / Real.sqrt 2, (z.1 + z.2) / Real.sqrt 2)
  map_add' z w := by ext <;> dsimp <;> ring
  map_smul' c z := by ext <;> dsimp <;> ring
  left_inv z := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    ext <;> dsimp
    · field_simp
      rw [hs2]
      ring
    · field_simp
      rw [hs2]
      ring
  right_inv z := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    ext <;> dsimp
    · field_simp
      rw [hs2]
      ring
    · field_simp
      rw [hs2]
      ring

lemma fromNormalCoordinates_eq (p : ℝ × (ℝ × ℝ)) :
    fromNormalCoordinates p = (p.1, normalToParticle p.2) := rfl

/-- The normal-coordinate rotation has unit Jacobian in the orientation used
in this development. -/
lemma normalToParticle_det : LinearMap.det (normalToParticle :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, normalToParticle, Module.Basis.finTwoProd]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs0]
  nlinarith [hs]

/-- Lebesgue measure is exactly preserved by the normal-coordinate rotation. -/
lemma normalToParticle_measurePreserving :
    MeasurePreserving normalToParticle
      (volume.prod volume : Measure (ℝ × ℝ)) (volume.prod volume) := by
  refine ⟨normalToParticle.toLinearMap.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map
    (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
      (volume.prod volume) = volume.prod volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
    (f := (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))
    (volume.prod volume : Measure (ℝ × ℝ))
    (by rw [normalToParticle_det]; norm_num)]
  rw [normalToParticle_det]
  simp

lemma normalToParticle_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving normalToParticle
      (volume.prod volume : Measure (ℝ × ℝ)) (volume.prod volume) := by
  apply Measure.LinearMap.quasiMeasurePreserving (volume.prod volume)
  exact (LinearEquiv.isUnit_det' normalToParticle).ne_zero

lemma normalToParticle_symm_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving normalToParticle.symm
      (volume.prod volume : Measure (ℝ × ℝ)) (volume.prod volume) := by
  apply Measure.LinearMap.quasiMeasurePreserving (volume.prod volume)
  exact (LinearEquiv.isUnit_det' normalToParticle.symm).ne_zero

/-- Composition with the normal-to-particle linear equivalence preserves
finite `Lᵖ` membership.  Its Jacobian need not be normalized explicitly:
the determinant factor is a finite scalar multiple of Lebesgue measure. -/
lemma MemLp.comp_normalToParticle {p : ℝ≥0∞} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g p (volume.prod volume)) :
    MemLp (g ∘ normalToParticle) p (volume.prod volume) := by
  let c : ℝ≥0∞ := ENNReal.ofReal
    |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|
  have hdet : LinearMap.det (normalToParticle :
      (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' normalToParticle).ne_zero
  have hmap : Measure.map normalToParticle (volume.prod volume) =
      c • (volume.prod volume) := by
    simpa [c] using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar
        (volume.prod volume : Measure (ℝ × ℝ)) hdet)
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgmap : MemLp g p (Measure.map normalToParticle (volume.prod volume)) := by
    rw [hmap]
    exact hg.smul_measure hc
  exact hgmap.comp_of_map normalToParticle_quasiMeasurePreserving.measurable.aemeasurable

/-- Quantitative version of `MemLp.comp_normalToParticle`; the fixed finite
Jacobian factor is left symbolic because only finiteness is used downstream. -/
lemma eLpNorm_comp_normalToParticle_le {p : ℝ≥0∞} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g p (volume.prod volume)) :
    eLpNorm (g ∘ normalToParticle) p (volume.prod volume) ≤
      (ENNReal.ofReal
        |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|) ^
          (1 / p).toReal • eLpNorm g p (volume.prod volume) := by
  let c : ℝ≥0∞ := ENNReal.ofReal
    |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|
  have hdet : LinearMap.det (normalToParticle :
      (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' normalToParticle).ne_zero
  have hmap : Measure.map normalToParticle (volume.prod volume) =
      c • (volume.prod volume) := by
    simpa [c] using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar
        (volume.prod volume : Measure (ℝ × ℝ)) hdet)
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgmap : MemLp g p (Measure.map normalToParticle (volume.prod volume)) := by
    rw [hmap]
    exact hg.smul_measure hc
  rw [← eLpNorm_map_measure hgmap.aestronglyMeasurable
    normalToParticle_quasiMeasurePreserving.measurable.aemeasurable, hmap]
  simpa [c, ENNReal.smul_def] using
    (eLpNorm_smul_measure_le c g p (volume.prod volume))

/-- Reflection across the diagonal in normal/tangential coordinates. -/
def normalReflection : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (-z.1, z.2)
  invFun z := (-z.1, z.2)
  map_add' z w := by ext <;> dsimp <;> ring
  map_smul' c z := by ext <;> simp
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

lemma normalReflection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving normalReflection
      (volume.prod volume : Measure (ℝ × ℝ)) (volume.prod volume) := by
  apply Measure.LinearMap.quasiMeasurePreserving (volume.prod volume)
  exact (LinearEquiv.isUnit_det' normalReflection).ne_zero

/-- `def:normal-tangential-coords`: exterior product in `(t,r,s)` coordinates. -/
def normalExterior (u v : ℝ → L2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  exteriorProduct u v (fromNormalCoordinates p)

lemma normalExterior_reflection (u v : ℝ → L2) (t : ℝ) (z : ℝ × ℝ) :
    normalExterior u v (t, normalReflection z) = -normalExterior u v (t, z) := by
  simp [normalExterior, normalReflection, fromNormalCoordinates, exteriorProduct]
  ring_nf

/-- Vanishing in normal coordinates is equivalent, up to null sets, to
vanishing in the original particle coordinates. -/
lemma exterior_ae_zero_of_normal_ae_zero (u v : ℝ → L2) (t : ℝ)
    (h : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), normalExterior u v (t, z) = 0) :
    ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), exteriorProduct u v (t, z) = 0 := by
  have h' := normalToParticle_symm_quasiMeasurePreserving.ae h
  filter_upwards [h'] with z hz
  simpa [normalExterior, fromNormalCoordinates_eq] using hz

/-- The real, `s`-even ridge potential in normal/tangential coordinates. -/
def ridgePotential (σ : ℝ) (u : ℝ → L2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ((σ * (‖(u p.1 : ℝ → ℂ) ((p.2.2 + p.2.1) / Real.sqrt 2)‖ ^ 2 +
      ‖(u p.1 : ℝ → ℂ) ((p.2.2 - p.2.1) / Real.sqrt 2)‖ ^ 2) : ℝ) : ℂ)

/-! Jointly measurable representatives used on the unique-continuation path. -/

/-- A jointly measurable scalar representative of a continuous global
solution curve.  The strengthened representative theorem identifies every
time slice, not merely almost every time slice. -/
def solutionRepresentative (σ : ℝ) (u : GlobalSolution σ) : ℝ × ℝ → ℂ :=
  Classical.choose (joint_representative_L2_measurable_strong volume u.u
    u.continuous.stronglyMeasurable)

lemma solutionRepresentative_measurable (σ : ℝ) (u : GlobalSolution σ) :
    Measurable (solutionRepresentative σ u) :=
  (Classical.choose_spec (joint_representative_L2_measurable_strong volume u.u
    u.continuous.stronglyMeasurable)).1

lemma solutionRepresentative_slice (σ : ℝ) (u : GlobalSolution σ) (t : ℝ) :
    (fun x => solutionRepresentative σ u (t, x)) =ᵐ[volume]
      (u.u t : ℝ → ℂ) :=
  (Classical.choose_spec (joint_representative_L2_measurable_strong volume u.u
    u.continuous.stronglyMeasurable)).2 t

/-- Exterior product formed from the jointly measurable solution
representatives. -/
def measurableExterior {σ : ℝ} (u v : GlobalSolution σ) :
    ℝ × (ℝ × ℝ) → ℂ := fun p =>
  solutionRepresentative σ u (p.1, p.2.1) *
      solutionRepresentative σ v (p.1, p.2.2) -
    solutionRepresentative σ v (p.1, p.2.1) *
      solutionRepresentative σ u (p.1, p.2.2)

lemma measurableExterior_measurable {σ : ℝ} (u v : GlobalSolution σ) :
    Measurable (measurableExterior u v) := by
  have hu := solutionRepresentative_measurable σ u
  have hv := solutionRepresentative_measurable σ v
  exact ((hu.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hv.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).sub
    ((hv.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hu.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))

lemma measurableExterior_slice {σ : ℝ} (u v : GlobalSolution σ) (t : ℝ) :
    (fun z => measurableExterior u v (t, z)) =ᵐ[volume.prod volume]
      fun z => exteriorProduct u.u v.u (t, z) := by
  have hut := solutionRepresentative_slice σ u t
  have hvt := solutionRepresentative_slice σ v t
  have hux : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      solutionRepresentative σ u (t, z.1) = (u.u t : ℝ → ℂ) z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hut
  have huy : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      solutionRepresentative σ u (t, z.2) = (u.u t : ℝ → ℂ) z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hut
  have hvx : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      solutionRepresentative σ v (t, z.1) = (v.u t : ℝ → ℂ) z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hvt
  have hvy : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      solutionRepresentative σ v (t, z.2) = (v.u t : ℝ → ℂ) z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hvt
  filter_upwards [hux, huy, hvx, hvy] with z hux huy hvx hvy
  simp only [measurableExterior, exteriorProduct, hux, huy, hvx, hvy]

/-- The measurable exterior product in normal/tangential coordinates. -/
def measurableNormalExterior {σ : ℝ} (u v : GlobalSolution σ) :
    ℝ × (ℝ × ℝ) → ℂ :=
  fun p => measurableExterior u v (fromNormalCoordinates p)

lemma measurableNormalExterior_measurable {σ : ℝ} (u v : GlobalSolution σ) :
    Measurable (measurableNormalExterior u v) := by
  exact (measurableExterior_measurable u v).comp (by
    unfold fromNormalCoordinates
    fun_prop)

lemma measurableNormalExterior_slice {σ : ℝ} (u v : GlobalSolution σ) (t : ℝ) :
    (fun z => measurableNormalExterior u v (t, z)) =ᵐ[volume.prod volume]
      fun z => normalExterior u.u v.u (t, z) := by
  have h := normalToParticle_quasiMeasurePreserving.ae
    (measurableExterior_slice u v t)
  filter_upwards [h] with z hz
  simpa only [measurableNormalExterior, normalExterior, fromNormalCoordinates_eq,
    Function.comp_apply] using hz

lemma measurableNormalExterior_reflection {σ : ℝ} (u v : GlobalSolution σ)
    (t : ℝ) (z : ℝ × ℝ) :
    measurableNormalExterior u v (t, normalReflection z) =
      -measurableNormalExterior u v (t, z) := by
  simp [measurableNormalExterior, measurableExterior, normalReflection,
    fromNormalCoordinates]
  ring_nf

/-- Ridge potential formed from the same jointly measurable representative. -/
def measurableRidgePotential (σ : ℝ) (u : GlobalSolution σ) :
    ℝ × (ℝ × ℝ) → ℂ := fun p =>
  ((σ *
    (‖solutionRepresentative σ u
        (p.1, (p.2.2 + p.2.1) / Real.sqrt 2)‖ ^ 2 +
      ‖solutionRepresentative σ u
        (p.1, (p.2.2 - p.2.1) / Real.sqrt 2)‖ ^ 2) : ℝ) : ℂ)

lemma measurableRidgePotential_measurable (σ : ℝ) (u : GlobalSolution σ) :
    Measurable (measurableRidgePotential σ u) := by
  have hu := solutionRepresentative_measurable σ u
  unfold measurableRidgePotential
  fun_prop

lemma measurableRidgePotential_slice (σ : ℝ) (u : GlobalSolution σ) (t : ℝ) :
    (fun z => measurableRidgePotential σ u (t, z)) =ᵐ[volume.prod volume]
      fun z => ridgePotential σ u.u (t, z) := by
  have hut := solutionRepresentative_slice σ u t
  have hxy : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      solutionRepresentative σ u (t, z.1) = (u.u t : ℝ → ℂ) z.1 ∧
        solutionRepresentative σ u (t, z.2) = (u.u t : ℝ → ℂ) z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hut,
      Measure.quasiMeasurePreserving_snd.ae hut] with z hx hy
    exact ⟨hx, hy⟩
  have hnormal := normalToParticle_quasiMeasurePreserving.ae hxy
  filter_upwards [hnormal] with z hz
  change
    solutionRepresentative σ u
          (t, (z.2 + z.1) / Real.sqrt 2) =
          (u.u t : ℝ → ℂ) ((z.2 + z.1) / Real.sqrt 2) ∧
      solutionRepresentative σ u
          (t, (z.2 - z.1) / Real.sqrt 2) =
          (u.u t : ℝ → ℂ) ((z.2 - z.1) / Real.sqrt 2) at hz
  simp only [measurableRidgePotential, ridgePotential, hz.1, hz.2]

/-- A horizontal strip in the normal coordinate. -/
def normalStrip (a h : ℝ) : Set (ℝ × ℝ) := {z | a < z.1 ∧ z.1 < a + h}

end CubicNLSPhaseRetrieval
