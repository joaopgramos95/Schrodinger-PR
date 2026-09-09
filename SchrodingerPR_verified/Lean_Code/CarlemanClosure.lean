import Lean_Code.CarlemanFourier2D
import Lean_Code.CarlemanWeakODE
import Lean_Code.CarlemanMultiplierSemigroup

/-! Axiom-free graph closure for the two-dimensional Carleman estimate. -/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

private def spatialExponential (β : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((β * x : ℝ) : ℂ)

private lemma spatialExponential_hasDerivAt (β x : ℝ) :
    HasDerivAt (spatialExponential β)
      ((β : ℂ) * spatialExponential β x) x := by
  have hlin : HasDerivAt (fun y : ℝ => ((β * y : ℝ) : ℂ)) (β : ℂ) x := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_one, mul_one] using!
      (hasDerivAt_id x).ofReal_comp.const_mul (β : ℂ)
  simpa only [spatialExponential, mul_comm] using! hlin.cexp

private lemma spatialExponential_contDiff (β : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (spatialExponential β) := by
  unfold spatialExponential
  exact Complex.contDiff_exp.comp
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))

private lemma spatialExponential_deriv (β x : ℝ) :
    deriv (spatialExponential β) x =
      (β : ℂ) * spatialExponential β x :=
  (spatialExponential_hasDerivAt β x).deriv

private lemma spatialExponential_iteratedDeriv_two (β x : ℝ) :
    iteratedDeriv 2 (spatialExponential β) x =
      ((β ^ 2 : ℝ) : ℂ) * spatialExponential β x := by
  rw [show iteratedDeriv 2 (spatialExponential β) =
      deriv (deriv (spatialExponential β)) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  rw [show deriv (spatialExponential β) =
      fun y => (β : ℂ) * spatialExponential β y by
    funext y
    exact spatialExponential_deriv β y]
  rw [deriv_const_mul _ (spatialExponential_hasDerivAt β x).differentiableAt]
  rw [spatialExponential_deriv]
  push_cast
  ring

private lemma iteratedDeriv_mul_two_formula_local (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (f * g) x = iteratedDeriv 2 f x * g x +
      2 * deriv f x * deriv g x + f x * iteratedDeriv 2 g x := by
  rw [iteratedDeriv_mul hf hg]
  norm_num [iteratedDeriv_zero, iteratedDeriv_one, Finset.sum_range_succ]
  ring

private def weightedTest (β : ℝ) (Ψ : Spacetime2) : Spacetime2 :=
  fun p => spatialExponential β p.2.1 * Ψ p

private def conjugatedAdjointTest (β : ℝ) (Ψ : Spacetime2) : Spacetime2 :=
  fun p =>
    -Complex.I * deriv (fun t => Ψ (t, p.2)) p.1 +
      iteratedDeriv 2 (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
      iteratedDeriv 2 (fun y => Ψ (p.1, (p.2.1, y))) p.2.2 +
      ((2 * β : ℝ) : ℂ) * deriv
        (fun x => Ψ (p.1, (x, p.2.2))) p.2.1 +
      ((β ^ 2 : ℝ) : ℂ) * Ψ p

private lemma weightedTest_contDiff (β : ℝ) (Ψ : Spacetime2)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weightedTest β Ψ) := by
  unfold weightedTest
  apply ContDiff.mul
  · exact (spatialExponential_contDiff β).comp
      (contDiff_fst.comp (contDiff_snd : ContDiff ℝ _ (Prod.snd :
        ℝ × (ℝ × ℝ) → ℝ × ℝ)))
  · exact hΨ

private lemma weightedTest_hasCompactSupport (β : ℝ) (Ψ : Spacetime2)
    (hΨ : HasCompactSupport Ψ) : HasCompactSupport (weightedTest β Ψ) := by
  change HasCompactSupport
    (fun p => spatialExponential β p.2.1 * Ψ p)
  exact hΨ.mul_left

private lemma schrodingerAdjoint_weightedTest (β : ℝ) (Ψ : Spacetime2)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (p : ℝ × (ℝ × ℝ)) :
    schrodinger2DAdjointTest (weightedTest β Ψ) p =
      spatialExponential β p.2.1 * conjugatedAdjointTest β Ψ p := by
  let t := p.1
  let x := p.2.1
  let y := p.2.2
  have ht : deriv (fun s => weightedTest β Ψ (s, (x, y))) t =
      spatialExponential β x * deriv (fun s => Ψ (s, (x, y))) t := by
    change deriv (fun s => spatialExponential β x * Ψ (s, (x, y))) t = _
    exact deriv_const_mul _
      ((hΨ.comp (contDiff_id.prodMk
        (contDiff_const.prodMk contDiff_const))).differentiable
          (by simp) t)
  have hEx : ContDiffAt ℝ 2 (spatialExponential β) x :=
    (spatialExponential_contDiff β).contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hΨx : ContDiffAt ℝ 2 (fun z => Ψ (t, (z, y))) x :=
    (hΨ.comp (contDiff_const.prodMk
      (contDiff_id.prodMk contDiff_const))).contDiffAt.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hx : iteratedDeriv 2
      (fun z => weightedTest β Ψ (t, (z, y))) x =
      spatialExponential β x *
        (iteratedDeriv 2 (fun z => Ψ (t, (z, y))) x +
          ((2 * β : ℝ) : ℂ) * deriv (fun z => Ψ (t, (z, y))) x +
          ((β ^ 2 : ℝ) : ℂ) * Ψ (t, (x, y))) := by
    change iteratedDeriv 2
      (spatialExponential β * fun z => Ψ (t, (z, y))) x = _
    rw [iteratedDeriv_mul_two_formula_local _ _ x hEx hΨx,
      spatialExponential_iteratedDeriv_two,
      spatialExponential_deriv]
    push_cast
    ring
  have hΨy : ContDiffAt ℝ 2 (fun z => Ψ (t, (x, z))) y :=
    (hΨ.comp (contDiff_const.prodMk
      (contDiff_const.prodMk contDiff_id))).contDiffAt.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hy : iteratedDeriv 2
      (fun z => weightedTest β Ψ (t, (x, z))) y =
      spatialExponential β x *
        iteratedDeriv 2 (fun z => Ψ (t, (x, z))) y := by
    change iteratedDeriv 2
      (fun z => spatialExponential β x * Ψ (t, (x, z))) y = _
    exact iteratedDeriv_const_mul _ hΨy
  unfold schrodinger2DAdjointTest conjugatedAdjointTest
  change -Complex.I * deriv (fun s => weightedTest β Ψ (s, (x, y))) t +
      iteratedDeriv 2 (fun z => weightedTest β Ψ (t, (z, y))) x +
      iteratedDeriv 2 (fun z => weightedTest β Ψ (t, (x, z))) y = _
  rw [ht, hx, hy]
  ring

private theorem weak_weighted_equation_data (β : ℝ) (U R : Spacetime2)
    (hweak : IsWeakSchrodinger2D U R) :
    ∀ Ψ : Spacetime2,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ →
      Integrable (fun p => exponentialWeight β U p *
        conjugatedAdjointTest β Ψ p)
        (volume.prod (volume.prod volume)) ∧
      Integrable (fun p => exponentialWeight β R p * Ψ p)
        (volume.prod (volume.prod volume)) ∧
      (∫ p, exponentialWeight β U p * conjugatedAdjointTest β Ψ p
          ∂(volume.prod (volume.prod volume))) =
        ∫ p, exponentialWeight β R p * Ψ p
          ∂(volume.prod (volume.prod volume)) := by
  intro Ψ hΨ hΨc
  obtain ⟨-, hUint, hRint, heq⟩ := hweak (weightedTest β Ψ)
    (weightedTest_contDiff β Ψ hΨ)
    (weightedTest_hasCompactSupport β Ψ hΨc)
  have hUint' : Integrable (fun p => exponentialWeight β U p *
      conjugatedAdjointTest β Ψ p)
      (volume.prod (volume.prod volume)) := by
    apply hUint.congr
    filter_upwards with p
    rw [schrodingerAdjoint_weightedTest β Ψ hΨ]
    simp only [exponentialWeight, spatialExponential]
    ring
  have hRint' : Integrable (fun p => exponentialWeight β R p * Ψ p)
      (volume.prod (volume.prod volume)) := by
    apply hRint.congr
    filter_upwards with p
    simp only [exponentialWeight, weightedTest, spatialExponential]
    ring
  refine ⟨hUint', hRint', ?_⟩
  calc
    (∫ p, exponentialWeight β U p * conjugatedAdjointTest β Ψ p
        ∂(volume.prod (volume.prod volume))) =
        ∫ p, U p * schrodinger2DAdjointTest (weightedTest β Ψ) p
          ∂(volume.prod (volume.prod volume)) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [schrodingerAdjoint_weightedTest β Ψ hΨ]
      simp only [exponentialWeight, spatialExponential]
      ring
    _ = ∫ p, R p * weightedTest β Ψ p
          ∂(volume.prod (volume.prod volume)) := heq
    _ = ∫ p, exponentialWeight β R p * Ψ p
          ∂(volume.prod (volume.prod volume)) := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [exponentialWeight, weightedTest, spatialExponential]
      ring

private theorem weak_weighted_equation (β : ℝ) (U R : Spacetime2)
    (hweak : IsWeakSchrodinger2D U R) :
    ∀ Ψ : Spacetime2,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ →
      (∫ p, exponentialWeight β U p * conjugatedAdjointTest β Ψ p
          ∂(volume.prod (volume.prod volume))) =
        ∫ p, exponentialWeight β R p * Ψ p
          ∂(volume.prod (volume.prod volume)) := by
  intro Ψ hΨ hΨc
  exact (weak_weighted_equation_data β U R hweak Ψ hΨ hΨc).2.2

private def pairConjugatedSpatial (β : ℝ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  pairPartial0 (pairPartial0 φ) + pairPartial1 (pairPartial1 φ) +
    ((2 * β : ℝ) : ℂ) • pairPartial0 φ +
    ((β ^ 2 : ℝ) : ℂ) • φ

private lemma pairPartial0_two_apply (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial0 (pairPartial0 φ) z =
      iteratedDeriv 2 (fun x => φ (x, z.2)) z.1 := by
  rw [pairPartial0_apply]
  have hfun : (fun x => pairPartial0 φ (x, z.2)) =
      deriv (fun x => φ (x, z.2)) := by
    funext x
    exact pairPartial0_apply φ (x, z.2)
  rw [hfun]
  rw [show iteratedDeriv 2 (fun x => φ (x, z.2)) =
      deriv (deriv (fun x => φ (x, z.2))) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]

private lemma pairPartial1_two_apply (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial1 (pairPartial1 φ) z =
      iteratedDeriv 2 (fun y => φ (z.1, y)) z.2 := by
  rw [pairPartial1_apply]
  have hfun : (fun y => pairPartial1 φ (z.1, y)) =
      deriv (fun y => φ (z.1, y)) := by
    funext y
    exact pairPartial1_apply φ (z.1, y)
  rw [hfun]
  rw [show iteratedDeriv 2 (fun y => φ (z.1, y)) =
      deriv (deriv (fun y => φ (z.1, y))) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]

private lemma pairConjugatedSpatial_apply (β : ℝ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairConjugatedSpatial β φ z =
      iteratedDeriv 2 (fun x => φ (x, z.2)) z.1 +
      iteratedDeriv 2 (fun y => φ (z.1, y)) z.2 +
      ((2 * β : ℝ) : ℂ) * deriv (fun x => φ (x, z.2)) z.1 +
      ((β ^ 2 : ℝ) : ℂ) * φ z := by
  change pairPartial0 (pairPartial0 φ) z + pairPartial1 (pairPartial1 φ) z +
      ((2 * β : ℝ) : ℂ) * pairPartial0 φ z +
      ((β ^ 2 : ℝ) : ℂ) * φ z = _
  rw [pairPartial0_two_apply, pairPartial1_two_apply, pairPartial0_apply]

private def separatedSpacetimeTest (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) : Spacetime2 :=
  fun p => η p.1 * φ p.2

private lemma separatedSpacetimeTest_contDiff (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (separatedSpacetimeTest η φ) := by
  unfold separatedSpacetimeTest
  fun_prop

private lemma separatedSpacetimeTest_hasCompactSupport (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (hη : HasCompactSupport (η : ℝ → ℂ))
    (hφ : HasCompactSupport (φ : ℝ × ℝ → ℂ)) :
    HasCompactSupport (separatedSpacetimeTest η φ) := by
  refine HasCompactSupport.intro
    (K := tsupport (η : ℝ → ℂ) ×ˢ tsupport (φ : ℝ × ℝ → ℂ))
    (hη.isCompact.prod hφ.isCompact) ?_
  intro p hp
  by_contra hn
  apply hp
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hn),
    subset_tsupport _ (right_ne_zero_of_mul hn)⟩

private lemma deriv_separated_time (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × (ℝ × ℝ)) :
    deriv (fun t => separatedSpacetimeTest η φ (t, p.2)) p.1 =
      deriv (η : ℝ → ℂ) p.1 * φ p.2 := by
  change deriv (fun t => η t * φ p.2) p.1 = _
  rw [deriv_mul_const ((η.smooth 1).differentiable (by simp) p.1)]

private lemma conjugatedAdjoint_separated (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × (ℝ × ℝ)) :
    conjugatedAdjointTest β (separatedSpacetimeTest η φ) p =
      (-Complex.I * deriv (η : ℝ → ℂ) p.1) * φ p.2 +
        η p.1 * pairConjugatedSpatial β φ p.2 := by
  have hx : iteratedDeriv 2
      (fun x => separatedSpacetimeTest η φ (p.1, (x, p.2.2))) p.2.1 =
      η p.1 * iteratedDeriv 2 (fun x => φ (x, p.2.2)) p.2.1 := by
    change iteratedDeriv 2 (fun x => η p.1 * φ (x, p.2.2)) p.2.1 = _
    have hcurve : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => (x, p.2.2)) :=
      contDiff_id.prodMk contDiff_const
    exact iteratedDeriv_const_mul _
      (((φ.smooth ⊤).comp hcurve).contDiffAt.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top))
  have hy : iteratedDeriv 2
      (fun y => separatedSpacetimeTest η φ (p.1, (p.2.1, y))) p.2.2 =
      η p.1 * iteratedDeriv 2 (fun y => φ (p.2.1, y)) p.2.2 := by
    change iteratedDeriv 2 (fun y => η p.1 * φ (p.2.1, y)) p.2.2 = _
    have hcurve : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℝ => (p.2.1, y)) :=
      contDiff_const.prodMk contDiff_id
    exact iteratedDeriv_const_mul _
      (((φ.smooth ⊤).comp hcurve).contDiffAt.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top))
  have hdx : deriv
      (fun x => separatedSpacetimeTest η φ (p.1, (x, p.2.2))) p.2.1 =
      η p.1 * deriv (fun x => φ (x, p.2.2)) p.2.1 := by
    change deriv (fun x => η p.1 * φ (x, p.2.2)) p.2.1 = _
    have hcurve : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => (x, p.2.2)) :=
      contDiff_id.prodMk contDiff_const
    exact deriv_const_mul _
      (((φ.smooth 1).comp (hcurve.of_le (by simp))).differentiable
        (by simp) p.2.1)
  unfold conjugatedAdjointTest
  rw [deriv_separated_time, hx, hy, hdx,
    pairConjugatedSpatial_apply]
  unfold separatedSpacetimeTest
  change _ = (-Complex.I * deriv (η : ℝ → ℂ) p.1) * φ p.2 + _
  ring

private lemma section_pairing_eq (F : Spacetime2)
    (hF : AEStronglyMeasurable F (volume.prod (volume.prod volume)))
    (t : ℝ)
    (ht : (carlemanSourceCurve F hF t : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun z => F (t, z))
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    (∫ z, F (t, z) * φ z ∂(volume.prod volume)) =
      bilinearL2Two (carlemanSourceCurve F hF t)
        (φ.toLp 2 (volume.prod volume)) := by
  rw [bilinearL2Two_eq_integral]
  apply integral_congr_ae
  filter_upwards [ht, φ.coeFn_toLp 2 (volume.prod volume)] with z hz hφz
  rw [hz, hφz]

private def separatedSpatialAdjoint (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ × ℝ, ℂ) :=
  (-Complex.I * deriv (η : ℝ → ℂ) t) • φ +
    η t • pairConjugatedSpatial β φ

private lemma separatedSpatialAdjoint_apply (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) (z : ℝ × ℝ) :
    separatedSpatialAdjoint β η φ t z =
      (-Complex.I * deriv (η : ℝ → ℂ) t) * φ z +
        η t * pairConjugatedSpatial β φ z := by
  rfl

private lemma pairSchwartzFourierInv_separatedSpatialAdjoint
    (β : ℝ) (η : 𝓢(ℝ, ℂ)) (φ : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) :
    pairSchwartzFourierInv (separatedSpatialAdjoint β η φ t) =
      (-Complex.I * deriv (η : ℝ → ℂ) t) • pairSchwartzFourierInv φ +
        η t • pairFrequencyConjugatedAdjoint β (pairSchwartzFourierInv φ) := by
  unfold separatedSpatialAdjoint pairConjugatedSpatial
  rw [pairSchwartzFourierInv_add, pairSchwartzFourierInv_smul,
    pairSchwartzFourierInv_smul]
  rw [pairSchwartzFourierInv_conjugatedSpatial]

private theorem weak_frequency_pairing (β : ℝ) (U R : Spacetime2)
    (hweak : IsWeakSchrodinger2D U R)
    (hw : AEStronglyMeasurable (exponentialWeight β U)
      (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable (exponentialWeight β R)
      (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight β U) < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight β R) < ⊤)
    (η : 𝓢(ℝ, ℂ)) (hη : HasCompactSupport (η : ℝ → ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ × ℝ → ℂ)) :
    (∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t))
        ((pairSchwartzFourierInv (separatedSpatialAdjoint β η φ t)).toLp 2
          (volume.prod volume)) ∂volume) =
      ∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t))
        ((η t • pairSchwartzFourierInv φ).toLp 2
          (volume.prod volume)) ∂volume := by
  let Ψ := separatedSpacetimeTest η φ
  have hΨd := separatedSpacetimeTest_contDiff η φ
  have hΨc := separatedSpacetimeTest_hasCompactSupport η φ hη hφ
  obtain ⟨hleftInt, hrightInt, heq⟩ :=
    weak_weighted_equation_data β U R hweak Ψ hΨd hΨc
  rw [integral_prod _ hleftInt, integral_prod _ hrightInt] at heq
  have hwsec := carlemanSolutionCurve_section_ae
    (exponentialWeight β U) hw hwfinite
  have hfsec := carlemanSourceCurve_section_ae
    (exponentialWeight β R) hf hffinite
  calc
    (∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t))
        ((pairSchwartzFourierInv (separatedSpatialAdjoint β η φ t)).toLp 2
          (volume.prod volume)) ∂volume) =
        ∫ t, ∫ z, exponentialWeight β U (t, z) *
          conjugatedAdjointTest β Ψ (t, z) ∂(volume.prod volume) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hwsec] with t ht
      rw [bilinearL2Two_fourierInv_right,
        LinearIsometryEquiv.symm_apply_apply]
      rw [← section_pairing_eq (exponentialWeight β U) hw t ht
        (separatedSpatialAdjoint β η φ t)]
      apply integral_congr_ae
      filter_upwards with z
      rw [conjugatedAdjoint_separated,
        separatedSpatialAdjoint_apply]
    _ = ∫ t, ∫ z, exponentialWeight β R (t, z) * Ψ (t, z)
          ∂(volume.prod volume) ∂volume := heq
    _ = ∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t))
        ((η t • pairSchwartzFourierInv φ).toLp 2
          (volume.prod volume)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hfsec] with t ht
      rw [← pairSchwartzFourierInv_smul,
        bilinearL2Two_fourierInv_right,
        LinearIsometryEquiv.symm_apply_apply]
      rw [← section_pairing_eq (exponentialWeight β R) hf t ht (η t • φ)]
      apply integral_congr_ae
      filter_upwards with z
      rfl

private lemma boundedFrequencyProduct_memLp
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

private def boundedFrequencyMultiplier
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) : SpatialL2Two :=
  MemLp.toLp (fun ξ => m ξ * (f : ℝ × ℝ → ℂ) ξ)
    (boundedFrequencyProduct_memLp m hm C hC f)

private lemma coe_boundedFrequencyMultiplier
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    (boundedFrequencyMultiplier m hm C hC f : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun ξ => m ξ * (f : ℝ × ℝ → ℂ) ξ :=
  MemLp.coeFn_toLp _

private lemma boundedFrequencyMultiplier_add
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f g : SpatialL2Two) :
    boundedFrequencyMultiplier m hm C hC (f + g) =
      boundedFrequencyMultiplier m hm C hC f +
        boundedFrequencyMultiplier m hm C hC g := by
  apply Lp.ext
  filter_upwards [coe_boundedFrequencyMultiplier m hm C hC (f + g),
    coe_boundedFrequencyMultiplier m hm C hC f,
    coe_boundedFrequencyMultiplier m hm C hC g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (boundedFrequencyMultiplier m hm C hC f)
      (boundedFrequencyMultiplier m hm C hC g)]
      with ξ hfg hf hg hadd hout
  rw [hfg, hadd, hout]
  simp only [Pi.add_apply]
  rw [hf, hg]
  ring

private lemma boundedFrequencyMultiplier_smul
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (c : ℂ) (f : SpatialL2Two) :
    boundedFrequencyMultiplier m hm C hC (c • f) =
      c • boundedFrequencyMultiplier m hm C hC f := by
  apply Lp.ext
  filter_upwards [coe_boundedFrequencyMultiplier m hm C hC (c • f),
    coe_boundedFrequencyMultiplier m hm C hC f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c (boundedFrequencyMultiplier m hm C hC f)]
      with ξ hcf hf hsmul hout
  rw [hcf, hsmul, hout]
  simp only [Pi.smul_apply]
  rw [hf]
  ring

private lemma norm_boundedFrequencyMultiplier_le
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    ‖boundedFrequencyMultiplier m hm C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_boundedFrequencyMultiplier m hm C hC f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

private def boundedFrequencyMultiplierCLM
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    SpatialL2Two →L[ℂ] SpatialL2Two :=
  let L : SpatialL2Two →ₗ[ℂ] SpatialL2Two :=
    { toFun := boundedFrequencyMultiplier m hm C hC
      map_add' := boundedFrequencyMultiplier_add m hm C hC
      map_smul' := boundedFrequencyMultiplier_smul m hm C hC }
  L.mkContinuous C (norm_boundedFrequencyMultiplier_le m hm C hC0 hC)

@[simp] private lemma boundedFrequencyMultiplierCLM_apply
    (m : ℝ × ℝ → ℂ) (hm : Measurable m) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : SpatialL2Two) :
    boundedFrequencyMultiplierCLM m hm C hC0 hC f =
      boundedFrequencyMultiplier m hm C hC f := rfl

/-! ## Compact spatial cutoffs in the second-order graph norm -/

private lemma smoothTransition_deriv_hasCompactSupport :
    HasCompactSupport (deriv Real.smoothTransition) := by
  refine HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  by_cases hleft : x < 0
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
      filter_upwards [isOpen_Iio.mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq, deriv_const]
  · have hright : 1 < x := by
      by_contra hn
      exact hx ⟨le_of_not_gt hleft, le_of_not_gt hn⟩
    have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq, deriv_const]

private lemma smoothTransition_iteratedDeriv_two_hasCompactSupport :
    HasCompactSupport (iteratedDeriv 2 Real.smoothTransition) := by
  rw [show iteratedDeriv 2 Real.smoothTransition =
      deriv (deriv Real.smoothTransition) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  exact smoothTransition_deriv_hasCompactSupport.deriv

private lemma exists_smoothTransition_deriv_bounds :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x, ‖deriv Real.smoothTransition x‖ ≤ M) ∧
      ∀ x, ‖iteratedDeriv 2 Real.smoothTransition x‖ ≤ M := by
  have h1c : Continuous (deriv Real.smoothTransition) := by
    simpa only [iteratedDeriv_one] using
      ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).continuous_iteratedDeriv 1
        (by norm_num))
  have h2c : Continuous (iteratedDeriv 2 Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).continuous_iteratedDeriv 2
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨x1, hx1⟩ := h1c.norm.exists_forall_ge_of_hasCompactSupport
    smoothTransition_deriv_hasCompactSupport.norm
  obtain ⟨x2, hx2⟩ := h2c.norm.exists_forall_ge_of_hasCompactSupport
    smoothTransition_iteratedDeriv_two_hasCompactSupport.norm
  refine ⟨max ‖deriv Real.smoothTransition x1‖
      ‖iteratedDeriv 2 Real.smoothTransition x2‖,
    (norm_nonneg _).trans (le_max_left _ _), ?_, ?_⟩
  · intro x
    exact (hx1 x).trans (le_max_left _ _)
  · intro x
    exact (hx2 x).trans (le_max_right _ _)

private def lineCutoff (n : ℕ) (x : ℝ) : ℂ :=
  (Real.smoothTransition ((n : ℝ) + 1 - x) : ℂ) *
    (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ)

private def lineCutoffDeriv (n : ℕ) (x : ℝ) : ℂ :=
  -((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
      (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ) +
    (Real.smoothTransition ((n : ℝ) + 1 - x) : ℂ) *
      ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)

private def lineCutoffSecond (n : ℕ) (x : ℝ) : ℂ :=
  ((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
      (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ) -
    2 * ((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
      ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ) +
    (Real.smoothTransition ((n : ℝ) + 1 - x) : ℂ) *
      ((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)

private lemma lineCutoff_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lineCutoff n) := by
  unfold lineCutoff
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp
      ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
        (contDiff_const.sub contDiff_id))
  · exact Complex.ofRealCLM.contDiff.comp
      ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
        (contDiff_const.add contDiff_id))

private lemma lineCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (lineCutoff n) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) isCompact_Icc ?_
  intro x hx
  by_cases hright : (n : ℝ) + 1 ≤ x
  · simp [lineCutoff, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hright)]
  · have hleft : x ≤ -((n : ℝ) + 1) := le_of_not_ge (fun hx' =>
      hx ⟨hx', le_of_not_ge hright⟩)
    have hz : (n : ℝ) + 1 + x ≤ 0 := by linarith
    simp [lineCutoff, Real.smoothTransition.zero_of_nonpos hz]

private lemma lineCutoff_deriv (n : ℕ) (x : ℝ) :
    deriv (lineCutoff n) x = lineCutoffDeriv n x := by
  have ha : HasDerivAt (fun y : ℝ => Real.smoothTransition ((n : ℝ) + 1 - y))
      (-deriv Real.smoothTransition ((n : ℝ) + 1 - x)) x := by
    simpa using! ((@Real.smoothTransition.contDiff 1).differentiable (by simp)
      ((n : ℝ) + 1 - x)).hasDerivAt.comp x
        ((hasDerivAt_id x).const_sub ((n : ℝ) + 1))
  have hb : HasDerivAt (fun y : ℝ => Real.smoothTransition ((n : ℝ) + 1 + y))
      (deriv Real.smoothTransition ((n : ℝ) + 1 + x)) x := by
    simpa using! ((@Real.smoothTransition.contDiff 1).differentiable (by simp)
      ((n : ℝ) + 1 + x)).hasDerivAt.comp x
        ((hasDerivAt_const x ((n : ℝ) + 1)).add (hasDerivAt_id x))
  have hac := ha.ofReal_comp
  have hbc := hb.ofReal_comp
  change deriv
      ((fun y : ℝ => (Real.smoothTransition ((n : ℝ) + 1 - y) : ℂ)) *
        fun y : ℝ => (Real.smoothTransition ((n : ℝ) + 1 + y) : ℂ)) x = _
  rw [(hac.mul hbc).deriv]
  unfold lineCutoffDeriv
  push_cast
  ring

private lemma lineCutoff_second (n : ℕ) (x : ℝ) :
    iteratedDeriv 2 (lineCutoff n) x = lineCutoffSecond n x := by
  have hcd := lineCutoff_contDiff n
  rw [show iteratedDeriv 2 (lineCutoff n) = deriv (deriv (lineCutoff n)) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  rw [show deriv (lineCutoff n) = lineCutoffDeriv n by
    funext y; exact lineCutoff_deriv n y]
  unfold lineCutoffDeriv lineCutoffSecond
  have hs1diff : Differentiable ℝ (iteratedDeriv 1 Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).differentiable_iteratedDeriv 1
      (by
        change ((1 : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 1))
  have ha1 : HasDerivAt
      (fun y : ℝ => ((deriv Real.smoothTransition ((n : ℝ) + 1 - y) : ℝ) : ℂ))
      (-((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ)) x := by
    have hraw := hs1diff ((n : ℝ) + 1 - x) |>.hasDerivAt.comp x
      ((hasDerivAt_id x).const_sub ((n : ℝ) + 1))
    rw [show iteratedDeriv 2 Real.smoothTransition =
        deriv (iteratedDeriv 1 Real.smoothTransition) by
      simpa using (iteratedDeriv_succ (n := 1) (f := Real.smoothTransition))]
    convert hraw.ofReal_comp using 1 <;>
      simp only [Function.comp_apply, iteratedDeriv_one] <;> push_cast <;> ring
  have hb1 : HasDerivAt
      (fun y : ℝ => ((deriv Real.smoothTransition ((n : ℝ) + 1 + y) : ℝ) : ℂ))
      ((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ) x := by
    have hraw := hs1diff ((n : ℝ) + 1 + x) |>.hasDerivAt.comp x
      ((hasDerivAt_const x ((n : ℝ) + 1)).add (hasDerivAt_id x))
    rw [show iteratedDeriv 2 Real.smoothTransition =
        deriv (iteratedDeriv 1 Real.smoothTransition) by
      simpa using (iteratedDeriv_succ (n := 1) (f := Real.smoothTransition))]
    simpa [iteratedDeriv_one] using! hraw.ofReal_comp
  have ha0 : HasDerivAt
      (fun y : ℝ => (Real.smoothTransition ((n : ℝ) + 1 - y) : ℂ))
      (-((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ)) x := by
    have hraw := ((@Real.smoothTransition.contDiff 1).differentiable (by simp)
      ((n : ℝ) + 1 - x)).hasDerivAt.comp x
        ((hasDerivAt_id x).const_sub ((n : ℝ) + 1))
    simpa using! hraw.ofReal_comp
  have hb0 : HasDerivAt
      (fun y : ℝ => (Real.smoothTransition ((n : ℝ) + 1 + y) : ℂ))
      ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ) x := by
    simpa using! (((@Real.smoothTransition.contDiff 1).differentiable (by simp)
      ((n : ℝ) + 1 + x)).hasDerivAt.comp x
        ((hasDerivAt_const x ((n : ℝ) + 1)).add (hasDerivAt_id x))).ofReal_comp
  change deriv
      (((-fun y : ℝ => ((deriv Real.smoothTransition ((n : ℝ) + 1 - y) : ℝ) : ℂ)) *
          (fun y : ℝ => (Real.smoothTransition ((n : ℝ) + 1 + y) : ℂ))) +
        ((fun y : ℝ => (Real.smoothTransition ((n : ℝ) + 1 - y) : ℂ)) *
          fun y : ℝ => ((deriv Real.smoothTransition ((n : ℝ) + 1 + y) : ℝ) : ℂ))) x = _
  rw [((ha1.neg.mul hb0).add (ha0.mul hb1)).deriv]
  simp only [Pi.neg_apply]
  ring

private lemma smoothTransition_deriv_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 1 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [heq.deriv_eq, deriv_const]

private lemma smoothTransition_second_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    iteratedDeriv 2 Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 1 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [heq.iteratedDeriv_eq 2, iteratedDeriv_const]
  norm_num

private lemma lineCutoff_eventually_eq_one (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, lineCutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxn : |x| < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hleft : 1 ≤ (n : ℝ) + 1 - x := by linarith [le_abs_self x]
  have hright : 1 ≤ (n : ℝ) + 1 + x := by linarith [neg_le_abs x]
  simp [lineCutoff, Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright]

private lemma lineCutoffDeriv_eventually_eq_zero (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, lineCutoffDeriv n x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxn : |x| < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hleft : 1 < (n : ℝ) + 1 - x := by linarith [le_abs_self x]
  have hright : 1 < (n : ℝ) + 1 + x := by linarith [neg_le_abs x]
  simp [lineCutoffDeriv, smoothTransition_deriv_eq_zero_of_one_lt hleft,
    smoothTransition_deriv_eq_zero_of_one_lt hright]

private lemma lineCutoffSecond_eventually_eq_zero (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, lineCutoffSecond n x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxn : |x| < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hleft : 1 < (n : ℝ) + 1 - x := by linarith [le_abs_self x]
  have hright : 1 < (n : ℝ) + 1 + x := by linarith [neg_le_abs x]
  simp [lineCutoffSecond, smoothTransition_deriv_eq_zero_of_one_lt hleft,
    smoothTransition_deriv_eq_zero_of_one_lt hright,
    smoothTransition_second_eq_zero_of_one_lt hleft,
    smoothTransition_second_eq_zero_of_one_lt hright]

private lemma norm_lineCutoff_le_one (n : ℕ) (x : ℝ) :
    ‖lineCutoff n x‖ ≤ 1 := by
  have hs (y : ℝ) : ‖(Real.smoothTransition y : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg y)] using
      Real.smoothTransition.le_one y
  rw [lineCutoff, norm_mul]
  exact mul_le_one₀ (hs _) (norm_nonneg _) (hs _)

private lemma norm_lineCutoffDeriv_le (M : ℝ)
    (hM : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖lineCutoffDeriv n x‖ ≤ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hs (y : ℝ) : ‖(Real.smoothTransition y : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg y)] using
      Real.smoothTransition.le_one y
  have hd (y : ℝ) : ‖((deriv Real.smoothTransition y : ℝ) : ℂ)‖ ≤ M := by
    simpa [Complex.norm_real] using hM y
  unfold lineCutoffDeriv
  calc
    _ ≤ ‖-((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
          (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ)‖ +
        ‖(Real.smoothTransition ((n : ℝ) + 1 - x) : ℂ) *
          ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ M * 1 + 1 * M := by
      apply add_le_add
      · rw [norm_mul, norm_neg]
        exact mul_le_mul (hd _) (hs _) (norm_nonneg _) hM0
      · rw [norm_mul]
        exact mul_le_mul (hs _) (hd _) (norm_nonneg _) (by positivity)
    _ = 2 * M := by ring

private lemma norm_lineCutoffSecond_le (M : ℝ) (hM0 : 0 ≤ M)
    (hM1 : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M)
    (hM2 : ∀ x, ‖iteratedDeriv 2 Real.smoothTransition x‖ ≤ M)
    (n : ℕ) (x : ℝ) :
    ‖lineCutoffSecond n x‖ ≤ 2 * M + 2 * M ^ 2 := by
  have hs (y : ℝ) : ‖(Real.smoothTransition y : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg y)] using
      Real.smoothTransition.le_one y
  have hd (y : ℝ) : ‖((deriv Real.smoothTransition y : ℝ) : ℂ)‖ ≤ M := by
    simpa [Complex.norm_real] using hM1 y
  have hdd (y : ℝ) :
      ‖((iteratedDeriv 2 Real.smoothTransition y : ℝ) : ℂ)‖ ≤ M := by
    simpa [Complex.norm_real] using hM2 y
  unfold lineCutoffSecond
  calc
    _ ≤ ‖((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
          (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ)‖ +
        ‖2 * ((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
          ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)‖ +
        ‖(Real.smoothTransition ((n : ℝ) + 1 - x) : ℂ) *
          ((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)‖ := by
      calc
        _ ≤ ‖((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
              (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ) -
              2 * ((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
                ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)‖ +
            ‖(Real.smoothTransition ((n : ℝ) + 1 - x) : ℂ) *
              ((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          have hsub := norm_sub_le
            (((iteratedDeriv 2 Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
              (Real.smoothTransition ((n : ℝ) + 1 + x) : ℂ))
            (2 * ((deriv Real.smoothTransition ((n : ℝ) + 1 - x) : ℝ) : ℂ) *
              ((deriv Real.smoothTransition ((n : ℝ) + 1 + x) : ℝ) : ℂ))
          nlinarith
    _ ≤ M * 1 + (2 * M * M) + 1 * M := by
      apply add_le_add
      · apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul (hdd _) (hs _) (norm_nonneg _) hM0
        · rw [norm_mul, norm_mul]
          norm_num
          have hp := mul_le_mul (hd ((n : ℝ) + 1 - x))
            (hd ((n : ℝ) + 1 + x)) (norm_nonneg _) hM0
          have hp' : |deriv Real.smoothTransition ((n : ℝ) + 1 - x)| *
              |deriv Real.smoothTransition ((n : ℝ) + 1 + x)| ≤ M * M := by
            simpa [Complex.norm_real] using hp
          nlinarith
      · rw [norm_mul]
        exact mul_le_mul (hs _) (hdd _) (norm_nonneg _) (by positivity)
    _ = 2 * M + 2 * M ^ 2 := by ring

private def pairCutoff (n : ℕ) (z : ℝ × ℝ) : ℂ :=
  lineCutoff n z.1 * lineCutoff n z.2

private def compactSchwartzApproxFun (n : ℕ) (φ : 𝓢(ℝ × ℝ, ℂ))
    (z : ℝ × ℝ) : ℂ := pairCutoff n z * φ z

private lemma compactSchwartzApproxFun_contDiff (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (compactSchwartzApproxFun n φ) := by
  unfold compactSchwartzApproxFun pairCutoff
  exact (((lineCutoff_contDiff n).comp contDiff_fst).mul
    ((lineCutoff_contDiff n).comp contDiff_snd)).mul (φ.smooth ⊤)

private lemma lineCutoff_eq_zero_of_not_mem (n : ℕ) (x : ℝ)
    (hx : x ∉ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :
    lineCutoff n x = 0 := by
  by_cases hright : (n : ℝ) + 1 ≤ x
  · simp [lineCutoff, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hright)]
  · have hleft : x ≤ -((n : ℝ) + 1) := le_of_not_ge (fun hx' =>
      hx ⟨hx', le_of_not_ge hright⟩)
    have hz : (n : ℝ) + 1 + x ≤ 0 := by linarith
    simp [lineCutoff, Real.smoothTransition.zero_of_nonpos hz]

private lemma compactSchwartzApproxFun_hasCompactSupport (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) : HasCompactSupport (compactSchwartzApproxFun n φ) := by
  let K := Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
    Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  refine HasCompactSupport.intro (K := K) (isCompact_Icc.prod isCompact_Icc) ?_
  intro z hz
  by_cases hx : z.1 ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  · have hy : z.2 ∉ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := fun h => hz ⟨hx, h⟩
    rw [compactSchwartzApproxFun, pairCutoff,
      lineCutoff_eq_zero_of_not_mem n z.2 hy]
    simp
  · rw [compactSchwartzApproxFun, pairCutoff,
      lineCutoff_eq_zero_of_not_mem n z.1 hx]
    simp

private def compactSchwartzApprox (n : ℕ) (φ : 𝓢(ℝ × ℝ, ℂ)) :
    𝓢(ℝ × ℝ, ℂ) :=
  (compactSchwartzApproxFun_hasCompactSupport n φ).toSchwartzMap
    (compactSchwartzApproxFun_contDiff n φ)

@[simp] private lemma compactSchwartzApprox_apply (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    compactSchwartzApprox n φ z = pairCutoff n z * φ z := rfl

private lemma compactSchwartzApprox_hasCompactSupport (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    HasCompactSupport (compactSchwartzApprox n φ : ℝ × ℝ → ℂ) :=
  compactSchwartzApproxFun_hasCompactSupport n φ

private lemma pairPartial0_compactSchwartzApprox (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial0 (compactSchwartzApprox n φ) z =
      lineCutoffDeriv n z.1 * lineCutoff n z.2 * φ z +
        pairCutoff n z * pairPartial0 φ z := by
  rw [pairPartial0_apply]
  change deriv (fun x => lineCutoff n x * lineCutoff n z.2 * φ (x, z.2)) z.1 = _
  have hl : DifferentiableAt ℝ (lineCutoff n) z.1 :=
    (lineCutoff_contDiff n).differentiable (by simp) z.1
  have hφ : DifferentiableAt ℝ (fun x : ℝ => φ (x, z.2)) z.1 :=
    ((φ.smooth 1).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) z.1
  rw [show (fun x => lineCutoff n x * lineCutoff n z.2 * φ (x, z.2)) =
      fun x => lineCutoff n x * (lineCutoff n z.2 * φ (x, z.2)) by
        funext x; ring]
  rw [show deriv (fun x => lineCutoff n x *
        (lineCutoff n z.2 * φ (x, z.2))) z.1 =
      deriv (lineCutoff n) z.1 * (lineCutoff n z.2 * φ z) +
        lineCutoff n z.1 *
          (lineCutoff n z.2 * deriv (fun x => φ (x, z.2)) z.1) by
    exact (hl.hasDerivAt.mul (hφ.hasDerivAt.const_mul
      (lineCutoff n z.2))).deriv]
  rw [lineCutoff_deriv, pairPartial0_apply]
  unfold pairCutoff
  ring

private lemma pairPartial1_compactSchwartzApprox (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial1 (compactSchwartzApprox n φ) z =
      lineCutoff n z.1 * lineCutoffDeriv n z.2 * φ z +
        pairCutoff n z * pairPartial1 φ z := by
  rw [pairPartial1_apply]
  change deriv (fun y => lineCutoff n z.1 * lineCutoff n y * φ (z.1, y)) z.2 = _
  have hl : DifferentiableAt ℝ (lineCutoff n) z.2 :=
    (lineCutoff_contDiff n).differentiable (by simp) z.2
  have hφ : DifferentiableAt ℝ (fun y : ℝ => φ (z.1, y)) z.2 :=
    ((φ.smooth 1).comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp) z.2
  rw [show (fun y => lineCutoff n z.1 * lineCutoff n y * φ (z.1, y)) =
      fun y => lineCutoff n z.1 * (lineCutoff n y * φ (z.1, y)) by
        funext y; ring]
  rw [show deriv (fun y => lineCutoff n z.1 *
        (lineCutoff n y * φ (z.1, y))) z.2 =
      lineCutoff n z.1 *
        (deriv (lineCutoff n) z.2 * φ z +
          lineCutoff n z.2 * deriv (fun y => φ (z.1, y)) z.2) by
    exact ((hl.hasDerivAt.mul hφ.hasDerivAt).const_mul
      (lineCutoff n z.1)).deriv]
  rw [lineCutoff_deriv, pairPartial1_apply]
  unfold pairCutoff
  ring

private lemma pairPartial0_two_compactSchwartzApprox (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial0 (pairPartial0 (compactSchwartzApprox n φ)) z =
      lineCutoffSecond n z.1 * lineCutoff n z.2 * φ z +
        2 * lineCutoffDeriv n z.1 * lineCutoff n z.2 * pairPartial0 φ z +
        pairCutoff n z * pairPartial0 (pairPartial0 φ) z := by
  rw [pairPartial0_two_apply]
  rw [show (fun x => compactSchwartzApprox n φ (x, z.2)) =
      fun x => lineCutoff n x * (lineCutoff n z.2 * φ (x, z.2)) by
        funext x
        rw [compactSchwartzApprox_apply]
        unfold pairCutoff
        ring]
  change iteratedDeriv 2
    (fun x => lineCutoff n x * (lineCutoff n z.2 * φ (x, z.2))) z.1 = _
  have hl : ContDiffAt ℝ 2 (lineCutoff n) z.1 :=
    (lineCutoff_contDiff n).contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hφ : ContDiffAt ℝ 2 (fun x : ℝ => φ (x, z.2)) z.1 :=
    ((φ.smooth 2).comp (contDiff_id.prodMk contDiff_const)).contDiffAt
  have hcφ : ContDiffAt ℝ 2
      (fun x : ℝ => lineCutoff n z.2 * φ (x, z.2)) z.1 :=
    (contDiffAt_const.mul hφ)
  rw [show iteratedDeriv 2
      (fun x => lineCutoff n x * (lineCutoff n z.2 * φ (x, z.2))) z.1 =
        iteratedDeriv 2 (lineCutoff n) z.1 *
            (lineCutoff n z.2 * φ z) +
          2 * deriv (lineCutoff n) z.1 *
            deriv (fun x => lineCutoff n z.2 * φ (x, z.2)) z.1 +
          lineCutoff n z.1 * iteratedDeriv 2
            (fun x => lineCutoff n z.2 * φ (x, z.2)) z.1 by
    exact iteratedDeriv_mul_two_formula_local _ _ z.1 hl hcφ]
  rw [lineCutoff_second, lineCutoff_deriv,
    deriv_const_mul _ (hφ.differentiableAt (by norm_num)),
    iteratedDeriv_const_mul _ hφ]
  rw [pairPartial0_apply, pairPartial0_two_apply]
  unfold pairCutoff
  ring

private lemma pairPartial1_two_compactSchwartzApprox (n : ℕ)
    (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial1 (pairPartial1 (compactSchwartzApprox n φ)) z =
      lineCutoff n z.1 * lineCutoffSecond n z.2 * φ z +
        2 * lineCutoff n z.1 * lineCutoffDeriv n z.2 * pairPartial1 φ z +
        pairCutoff n z * pairPartial1 (pairPartial1 φ) z := by
  rw [pairPartial1_two_apply]
  rw [show (fun y => compactSchwartzApprox n φ (z.1, y)) =
      fun y => lineCutoff n z.1 * (lineCutoff n y * φ (z.1, y)) by
        funext y
        rw [compactSchwartzApprox_apply]
        unfold pairCutoff
        ring]
  change iteratedDeriv 2
    (fun y => lineCutoff n z.1 * (lineCutoff n y * φ (z.1, y))) z.2 = _
  have hl : ContDiffAt ℝ 2 (lineCutoff n) z.2 :=
    (lineCutoff_contDiff n).contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hφ : ContDiffAt ℝ 2 (fun y : ℝ => φ (z.1, y)) z.2 :=
    ((φ.smooth 2).comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  have hprod : ContDiffAt ℝ 2
      (fun y : ℝ => lineCutoff n y * φ (z.1, y)) z.2 := hl.mul hφ
  rw [iteratedDeriv_const_mul _ hprod]
  rw [show iteratedDeriv 2 (fun y => lineCutoff n y * φ (z.1, y)) z.2 =
      iteratedDeriv 2 (lineCutoff n) z.2 * φ z +
        2 * deriv (lineCutoff n) z.2 * deriv (fun y => φ (z.1, y)) z.2 +
        lineCutoff n z.2 * iteratedDeriv 2 (fun y => φ (z.1, y)) z.2 by
    exact iteratedDeriv_mul_two_formula_local _ _ z.2 hl hφ]
  rw [lineCutoff_second, lineCutoff_deriv,
    pairPartial1_apply, pairPartial1_two_apply]
  unfold pairCutoff
  ring

private theorem tendsto_eLpNorm_two_mul_schwartz
    (a : ℕ → ℝ × ℝ → ℂ) (C : ℝ) (hC0 : 0 ≤ C)
    (haMeas : ∀ n, Measurable (a n))
    (haBound : ∀ n z, ‖a n z‖ ≤ C)
    (haZero : ∀ z, ∀ᶠ n : ℕ in atTop, a n z = 0)
    (ψ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n => eLpNorm (fun z => a n z * ψ z) 2
      (volume.prod volume)) atTop (𝓝 0) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  let CE : ℝ≥0∞ := ENNReal.ofReal C
  have hCEtop : CE ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint : Tendsto (fun n =>
      ∫⁻ z, ‖a n z * ψ z‖ₑ ^ (2 : ℝ) ∂(volume.prod volume))
      atTop (𝓝 0) := by
    have hDCT : Tendsto (fun n =>
        ∫⁻ z, ‖a n z * ψ z‖ₑ ^ (2 : ℝ) ∂(volume.prod volume))
        atTop (𝓝 (∫⁻ _ : ℝ × ℝ, (0 : ℝ≥0∞) ∂(volume.prod volume))) := by
      refine tendsto_lintegral_filter_of_dominated_convergence
        (f := fun _ => 0)
        (fun z => (CE * ‖ψ z‖ₑ) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
      · filter_upwards with n
        exact ((haMeas n).mul ψ.continuous.measurable).enorm.pow_const 2
      · filter_upwards with n
        filter_upwards with z
        rw [enorm_mul]
        have hnormE : ‖a n z‖ₑ ≤ CE := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (haBound n z)
        exact ENNReal.rpow_le_rpow
          (mul_le_mul_right' hnormE ‖ψ z‖ₑ) (by norm_num)
      · rw [show (fun z => (CE * ‖ψ z‖ₑ) ^ (2 : ℝ)) =
            fun z => CE ^ (2 : ℝ) * ‖ψ z‖ₑ ^ (2 : ℝ) by
          funext z
          exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCEtop)]
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCEtop)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
            (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            (ψ.memLp 2 (volume.prod volume)).eLpNorm_lt_top).ne
      · filter_upwards with z
        have hevent := haZero z
        apply tendsto_const_nhds.congr'
        filter_upwards [hevent] with n hn
        simp [hn]
    simpa using hDCT
  convert hint.ennrpow_const (1 / ENNReal.toReal 2) using 1 <;> norm_num

private lemma pairCutoff_sub_one_bound (n : ℕ) (z : ℝ × ℝ) :
    ‖pairCutoff n z - 1‖ ≤ 2 := by
  calc
    _ ≤ ‖pairCutoff n z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (by
        rw [pairCutoff, norm_mul]
        exact mul_le_one₀ (norm_lineCutoff_le_one n z.1)
          (norm_nonneg _) (norm_lineCutoff_le_one n z.2)) (by norm_num)
    _ = 2 := by norm_num

private lemma pairCutoff_eventually_eq_one (z : ℝ × ℝ) :
    ∀ᶠ n : ℕ in atTop, pairCutoff n z = 1 := by
  filter_upwards [lineCutoff_eventually_eq_one z.1,
    lineCutoff_eventually_eq_one z.2] with n hx hy
  simp [pairCutoff, hx, hy]

private lemma pairCutoff_sub_one_eventually_eq_zero (z : ℝ × ℝ) :
    ∀ᶠ n : ℕ in atTop, pairCutoff n z - 1 = 0 := by
  filter_upwards [pairCutoff_eventually_eq_one z] with n hn
  rw [hn, sub_self]

private lemma pairCutoff_measurable (n : ℕ) : Measurable (pairCutoff n) := by
  exact (((lineCutoff_contDiff n).continuous.comp continuous_fst).mul
    ((lineCutoff_contDiff n).continuous.comp continuous_snd)).measurable

private lemma pairCutoff_sub_one_measurable (n : ℕ) :
    Measurable (fun z => pairCutoff n z - 1) :=
  (pairCutoff_measurable n).sub measurable_const

private lemma cutoffDeriv0_bound (M : ℝ)
    (hM : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M)
    (n : ℕ) (z : ℝ × ℝ) :
    ‖lineCutoffDeriv n z.1 * lineCutoff n z.2‖ ≤ 2 * M := by
  rw [norm_mul]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc
    _ ≤ (2 * M) * 1 := mul_le_mul (norm_lineCutoffDeriv_le M hM n z.1)
      (norm_lineCutoff_le_one n z.2) (norm_nonneg _)
      (mul_nonneg (by norm_num) hM0)
    _ = 2 * M := by ring

private lemma cutoffDeriv1_bound (M : ℝ)
    (hM : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M)
    (n : ℕ) (z : ℝ × ℝ) :
    ‖lineCutoff n z.1 * lineCutoffDeriv n z.2‖ ≤ 2 * M := by
  rw [norm_mul]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc
    _ ≤ 1 * (2 * M) := mul_le_mul (norm_lineCutoff_le_one n z.1)
      (norm_lineCutoffDeriv_le M hM n z.2) (norm_nonneg _) (by positivity)
    _ = 2 * M := by ring

private lemma cutoffDeriv0_eventually_eq_zero (z : ℝ × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      lineCutoffDeriv n z.1 * lineCutoff n z.2 = 0 := by
  filter_upwards [lineCutoffDeriv_eventually_eq_zero z.1] with n hn
  simp [hn]

private lemma cutoffDeriv1_eventually_eq_zero (z : ℝ × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      lineCutoff n z.1 * lineCutoffDeriv n z.2 = 0 := by
  filter_upwards [lineCutoffDeriv_eventually_eq_zero z.2] with n hn
  simp [hn]

private lemma cutoffDeriv0_measurable (n : ℕ) :
    Measurable (fun z : ℝ × ℝ =>
      lineCutoffDeriv n z.1 * lineCutoff n z.2) := by
  have hd : Continuous (lineCutoffDeriv n) := by
    rw [show lineCutoffDeriv n = deriv (lineCutoff n) by
      funext x; exact (lineCutoff_deriv n x).symm]
    simpa only [iteratedDeriv_one] using
      (lineCutoff_contDiff n).continuous_iteratedDeriv 1 (by norm_num)
  exact ((hd.comp continuous_fst).mul
    ((lineCutoff_contDiff n).continuous.comp continuous_snd)).measurable

private lemma cutoffDeriv1_measurable (n : ℕ) :
    Measurable (fun z : ℝ × ℝ =>
      lineCutoff n z.1 * lineCutoffDeriv n z.2) := by
  have hd : Continuous (lineCutoffDeriv n) := by
    rw [show lineCutoffDeriv n = deriv (lineCutoff n) by
      funext x; exact (lineCutoff_deriv n x).symm]
    simpa only [iteratedDeriv_one] using
      (lineCutoff_contDiff n).continuous_iteratedDeriv 1 (by norm_num)
  exact (((lineCutoff_contDiff n).continuous.comp continuous_fst).mul
    (hd.comp continuous_snd)).measurable

private lemma cutoffSecond0_bound (M : ℝ) (hM0 : 0 ≤ M)
    (hM1 : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M)
    (hM2 : ∀ x, ‖iteratedDeriv 2 Real.smoothTransition x‖ ≤ M)
    (n : ℕ) (z : ℝ × ℝ) :
    ‖lineCutoffSecond n z.1 * lineCutoff n z.2‖ ≤ 2 * M + 2 * M ^ 2 := by
  rw [norm_mul]
  have hB0 : 0 ≤ 2 * M + 2 * M ^ 2 := by positivity
  calc
    _ ≤ (2 * M + 2 * M ^ 2) * 1 := mul_le_mul
      (norm_lineCutoffSecond_le M hM0 hM1 hM2 n z.1)
      (norm_lineCutoff_le_one n z.2) (norm_nonneg _) hB0
    _ = _ := by ring

private lemma cutoffSecond1_bound (M : ℝ) (hM0 : 0 ≤ M)
    (hM1 : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M)
    (hM2 : ∀ x, ‖iteratedDeriv 2 Real.smoothTransition x‖ ≤ M)
    (n : ℕ) (z : ℝ × ℝ) :
    ‖lineCutoff n z.1 * lineCutoffSecond n z.2‖ ≤ 2 * M + 2 * M ^ 2 := by
  rw [norm_mul]
  calc
    _ ≤ 1 * (2 * M + 2 * M ^ 2) := mul_le_mul
      (norm_lineCutoff_le_one n z.1)
      (norm_lineCutoffSecond_le M hM0 hM1 hM2 n z.2)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

private lemma cutoffSecond0_eventually_eq_zero (z : ℝ × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      lineCutoffSecond n z.1 * lineCutoff n z.2 = 0 := by
  filter_upwards [lineCutoffSecond_eventually_eq_zero z.1] with n hn
  simp [hn]

private lemma cutoffSecond1_eventually_eq_zero (z : ℝ × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      lineCutoff n z.1 * lineCutoffSecond n z.2 = 0 := by
  filter_upwards [lineCutoffSecond_eventually_eq_zero z.2] with n hn
  simp [hn]

private lemma lineCutoffSecond_continuous (n : ℕ) :
    Continuous (lineCutoffSecond n) := by
  rw [show lineCutoffSecond n = iteratedDeriv 2 (lineCutoff n) by
    funext x; exact (lineCutoff_second n x).symm]
  exact (lineCutoff_contDiff n).continuous_iteratedDeriv 2 (by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)

private lemma cutoffSecond0_measurable (n : ℕ) :
    Measurable (fun z : ℝ × ℝ =>
      lineCutoffSecond n z.1 * lineCutoff n z.2) :=
  (((lineCutoffSecond_continuous n).comp continuous_fst).mul
    ((lineCutoff_contDiff n).continuous.comp continuous_snd)).measurable

private lemma cutoffSecond1_measurable (n : ℕ) :
    Measurable (fun z : ℝ × ℝ =>
      lineCutoff n z.1 * lineCutoffSecond n z.2) :=
  (((lineCutoff_contDiff n).continuous.comp continuous_fst).mul
    ((lineCutoffSecond_continuous n).comp continuous_snd)).measurable

private theorem tendsto_eLpNorm_two_add
    (f g : ℕ → ℝ × ℝ → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.prod volume))
    (hg : ∀ n, AEStronglyMeasurable (g n) (volume.prod volume))
    (hft : Tendsto (fun n => eLpNorm (f n) 2 (volume.prod volume))
      atTop (𝓝 0))
    (hgt : Tendsto (fun n => eLpNorm (g n) 2 (volume.prod volume))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z => f n z + g n z) 2
      (volume.prod volume)) atTop (𝓝 0) := by
  have hbound : ∀ n,
      eLpNorm (fun z => f n z + g n z) 2 (volume.prod volume) ≤
        eLpNorm (f n) 2 (volume.prod volume) +
          eLpNorm (g n) 2 (volume.prod volume) := fun n =>
    eLpNorm_add_le (hf n) (hg n) (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hft.add hgt) (fun _ => bot_le) hbound

private theorem tendsto_schwartz_toLp_of_eLpNorm_sub
    (ψn : ℕ → 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ × ℝ, ℂ))
    (h : Tendsto (fun n => eLpNorm (fun z => ψn n z - ψ z) 2
      (volume.prod volume)) atTop (𝓝 0)) :
    Tendsto (fun n => (ψn n).toLp 2 (volume.prod volume)) atTop
      (𝓝 (ψ.toLp 2 (volume.prod volume))) := by
  apply Lp.tendsto_Lp_of_tendsto_eLpNorm (ψ : ℝ × ℝ → ℂ)
    (ψ.memLp 2 (volume.prod volume))
  have heq (n : ℕ) :
      eLpNorm (fun z =>
          ((ψn n).toLp 2 (volume.prod volume) : ℝ × ℝ → ℂ) z - ψ z)
        2 (volume.prod volume) =
        eLpNorm (fun z => ψn n z - ψ z) 2 (volume.prod volume) := by
    apply eLpNorm_congr_ae
    filter_upwards [(ψn n).coeFn_toLp 2 (volume.prod volume)] with z hz
    rw [hz]
  have hfun : (fun n => eLpNorm
      ((fun z => ((ψn n).toLp 2 (volume.prod volume) : ℝ × ℝ → ℂ) z) -
        (ψ : ℝ × ℝ → ℂ)) 2 (volume.prod volume)) =
      fun n => eLpNorm (fun z => ψn n z - ψ z) 2
        (volume.prod volume) := by
    funext n
    exact heq n
  rw [hfun]
  exact h

private theorem compactSchwartzApprox_tendsto_toLp
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n => (compactSchwartzApprox n φ).toLp 2 (volume.prod volume))
      atTop (𝓝 (φ.toLp 2 (volume.prod volume))) := by
  apply tendsto_schwartz_toLp_of_eLpNorm_sub
  have h := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => pairCutoff n z - 1) 2 (by norm_num)
    pairCutoff_sub_one_measurable pairCutoff_sub_one_bound
    pairCutoff_sub_one_eventually_eq_zero φ
  apply h.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with z
  rw [compactSchwartzApprox_apply]
  ring

private theorem pairPartial0_compactSchwartzApprox_tendsto_toLp
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n => (pairPartial0 (compactSchwartzApprox n φ)).toLp 2
      (volume.prod volume)) atTop
      (𝓝 ((pairPartial0 φ).toLp 2 (volume.prod volume))) := by
  apply tendsto_schwartz_toLp_of_eLpNorm_sub
  obtain ⟨M, hM0, hM1, hM2⟩ := exists_smoothTransition_deriv_bounds
  let f : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (lineCutoffDeriv n z.1 * lineCutoff n z.2) * φ z
  let g : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (pairCutoff n z - 1) * pairPartial0 φ z
  have hf : Tendsto (fun n => eLpNorm (f n) 2 (volume.prod volume))
      atTop (𝓝 0) := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => lineCutoffDeriv n z.1 * lineCutoff n z.2) (2 * M)
    (mul_nonneg (by norm_num) hM0) cutoffDeriv0_measurable
    (cutoffDeriv0_bound M hM1) cutoffDeriv0_eventually_eq_zero φ
  have hg : Tendsto (fun n => eLpNorm (g n) 2 (volume.prod volume))
      atTop (𝓝 0) := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => pairCutoff n z - 1) 2 (by norm_num)
    pairCutoff_sub_one_measurable pairCutoff_sub_one_bound
    pairCutoff_sub_one_eventually_eq_zero (pairPartial0 φ)
  have hsum := tendsto_eLpNorm_two_add f g
    (fun n => ((cutoffDeriv0_measurable n).mul φ.continuous.measurable).aestronglyMeasurable)
    (fun n => ((pairCutoff_sub_one_measurable n).mul
      (pairPartial0 φ).continuous.measurable).aestronglyMeasurable) hf hg
  apply hsum.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with z
  rw [pairPartial0_compactSchwartzApprox]
  dsimp [f, g]
  ring

private theorem pairPartial1_compactSchwartzApprox_tendsto_toLp
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n => (pairPartial1 (compactSchwartzApprox n φ)).toLp 2
      (volume.prod volume)) atTop
      (𝓝 ((pairPartial1 φ).toLp 2 (volume.prod volume))) := by
  apply tendsto_schwartz_toLp_of_eLpNorm_sub
  obtain ⟨M, hM0, hM1, hM2⟩ := exists_smoothTransition_deriv_bounds
  let f : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (lineCutoff n z.1 * lineCutoffDeriv n z.2) * φ z
  let g : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (pairCutoff n z - 1) * pairPartial1 φ z
  have hf := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => lineCutoff n z.1 * lineCutoffDeriv n z.2) (2 * M)
    (mul_nonneg (by norm_num) hM0) cutoffDeriv1_measurable
    (cutoffDeriv1_bound M hM1) cutoffDeriv1_eventually_eq_zero φ
  have hg := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => pairCutoff n z - 1) 2 (by norm_num)
    pairCutoff_sub_one_measurable pairCutoff_sub_one_bound
    pairCutoff_sub_one_eventually_eq_zero (pairPartial1 φ)
  have hsum := tendsto_eLpNorm_two_add f g
    (fun n => ((cutoffDeriv1_measurable n).mul φ.continuous.measurable).aestronglyMeasurable)
    (fun n => ((pairCutoff_sub_one_measurable n).mul
      (pairPartial1 φ).continuous.measurable).aestronglyMeasurable) hf hg
  apply hsum.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with z
  rw [pairPartial1_compactSchwartzApprox]
  dsimp [f, g]
  ring

private theorem pairPartial0_two_compactSchwartzApprox_tendsto_toLp
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n =>
      (pairPartial0 (pairPartial0 (compactSchwartzApprox n φ))).toLp 2
        (volume.prod volume)) atTop
      (𝓝 ((pairPartial0 (pairPartial0 φ)).toLp 2 (volume.prod volume))) := by
  apply tendsto_schwartz_toLp_of_eLpNorm_sub
  obtain ⟨M, hM0, hM1, hM2⟩ := exists_smoothTransition_deriv_bounds
  let a : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (lineCutoffSecond n z.1 * lineCutoff n z.2) * φ z
  let b : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (2 * (lineCutoffDeriv n z.1 * lineCutoff n z.2)) * pairPartial0 φ z
  let c : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (pairCutoff n z - 1) * pairPartial0 (pairPartial0 φ) z
  have ha := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => lineCutoffSecond n z.1 * lineCutoff n z.2)
    (2 * M + 2 * M ^ 2) (by positivity) cutoffSecond0_measurable
    (cutoffSecond0_bound M hM0 hM1 hM2)
    cutoffSecond0_eventually_eq_zero φ
  have hbmeas (n : ℕ) : Measurable (fun z : ℝ × ℝ =>
      2 * (lineCutoffDeriv n z.1 * lineCutoff n z.2)) :=
    measurable_const.mul (cutoffDeriv0_measurable n)
  have hbbound (n : ℕ) (z : ℝ × ℝ) :
      ‖(2 : ℂ) * (lineCutoffDeriv n z.1 * lineCutoff n z.2)‖ ≤ 4 * M := by
    rw [norm_mul]
    norm_num
    have hc : ‖lineCutoffDeriv n z.1‖ * ‖lineCutoff n z.2‖ ≤ 2 * M := by
      simpa only [norm_mul] using cutoffDeriv0_bound M hM1 n z
    calc
      2 * (‖lineCutoffDeriv n z.1‖ * ‖lineCutoff n z.2‖) ≤
          2 * (2 * M) := mul_le_mul_of_nonneg_left
            hc (by norm_num)
      _ = 4 * M := by ring
  have hbzero (z : ℝ × ℝ) : ∀ᶠ n : ℕ in atTop,
      (2 : ℂ) * (lineCutoffDeriv n z.1 * lineCutoff n z.2) = 0 := by
    filter_upwards [cutoffDeriv0_eventually_eq_zero z] with n hn
    simp [hn]
  have hb := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => 2 * (lineCutoffDeriv n z.1 * lineCutoff n z.2))
    (4 * M) (mul_nonneg (by norm_num) hM0) hbmeas hbbound hbzero
    (pairPartial0 φ)
  have hc := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => pairCutoff n z - 1) 2 (by norm_num)
    pairCutoff_sub_one_measurable pairCutoff_sub_one_bound
    pairCutoff_sub_one_eventually_eq_zero (pairPartial0 (pairPartial0 φ))
  have hameas (n : ℕ) : AEStronglyMeasurable (a n) (volume.prod volume) :=
    ((cutoffSecond0_measurable n).mul φ.continuous.measurable).aestronglyMeasurable
  have hbMeas (n : ℕ) : AEStronglyMeasurable (b n) (volume.prod volume) :=
    ((hbmeas n).mul (pairPartial0 φ).continuous.measurable).aestronglyMeasurable
  have hcmeas (n : ℕ) : AEStronglyMeasurable (c n) (volume.prod volume) :=
    ((pairCutoff_sub_one_measurable n).mul
      (pairPartial0 (pairPartial0 φ)).continuous.measurable).aestronglyMeasurable
  have hab := tendsto_eLpNorm_two_add a b hameas hbMeas ha hb
  let ab : ℕ → ℝ × ℝ → ℂ := fun n z => a n z + b n z
  have habmeas (n : ℕ) : AEStronglyMeasurable (ab n) (volume.prod volume) :=
    (hameas n).add (hbMeas n)
  have hab' : Tendsto (fun n => eLpNorm (ab n) 2 (volume.prod volume))
      atTop (𝓝 0) := by simpa [ab] using hab
  have hsum := tendsto_eLpNorm_two_add ab c habmeas hcmeas hab' hc
  apply hsum.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with z
  rw [pairPartial0_two_compactSchwartzApprox]
  dsimp [ab, a, b, c]
  ring

private theorem pairPartial1_two_compactSchwartzApprox_tendsto_toLp
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n =>
      (pairPartial1 (pairPartial1 (compactSchwartzApprox n φ))).toLp 2
        (volume.prod volume)) atTop
      (𝓝 ((pairPartial1 (pairPartial1 φ)).toLp 2 (volume.prod volume))) := by
  apply tendsto_schwartz_toLp_of_eLpNorm_sub
  obtain ⟨M, hM0, hM1, hM2⟩ := exists_smoothTransition_deriv_bounds
  let a : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (lineCutoff n z.1 * lineCutoffSecond n z.2) * φ z
  let b : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (2 * (lineCutoff n z.1 * lineCutoffDeriv n z.2)) * pairPartial1 φ z
  let c : ℕ → ℝ × ℝ → ℂ := fun n z =>
    (pairCutoff n z - 1) * pairPartial1 (pairPartial1 φ) z
  have ha := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => lineCutoff n z.1 * lineCutoffSecond n z.2)
    (2 * M + 2 * M ^ 2) (by positivity) cutoffSecond1_measurable
    (cutoffSecond1_bound M hM0 hM1 hM2)
    cutoffSecond1_eventually_eq_zero φ
  have hbmeas (n : ℕ) : Measurable (fun z : ℝ × ℝ =>
      2 * (lineCutoff n z.1 * lineCutoffDeriv n z.2)) :=
    measurable_const.mul (cutoffDeriv1_measurable n)
  have hbbound (n : ℕ) (z : ℝ × ℝ) :
      ‖(2 : ℂ) * (lineCutoff n z.1 * lineCutoffDeriv n z.2)‖ ≤ 4 * M := by
    rw [norm_mul]
    norm_num
    have hc : ‖lineCutoff n z.1‖ * ‖lineCutoffDeriv n z.2‖ ≤ 2 * M := by
      simpa only [norm_mul] using cutoffDeriv1_bound M hM1 n z
    calc
      2 * (‖lineCutoff n z.1‖ * ‖lineCutoffDeriv n z.2‖) ≤
          2 * (2 * M) := mul_le_mul_of_nonneg_left
            hc (by norm_num)
      _ = 4 * M := by ring
  have hbzero (z : ℝ × ℝ) : ∀ᶠ n : ℕ in atTop,
      (2 : ℂ) * (lineCutoff n z.1 * lineCutoffDeriv n z.2) = 0 := by
    filter_upwards [cutoffDeriv1_eventually_eq_zero z] with n hn
    simp [hn]
  have hb := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => 2 * (lineCutoff n z.1 * lineCutoffDeriv n z.2))
    (4 * M) (mul_nonneg (by norm_num) hM0) hbmeas hbbound hbzero
    (pairPartial1 φ)
  have hc := tendsto_eLpNorm_two_mul_schwartz
    (fun n z => pairCutoff n z - 1) 2 (by norm_num)
    pairCutoff_sub_one_measurable pairCutoff_sub_one_bound
    pairCutoff_sub_one_eventually_eq_zero (pairPartial1 (pairPartial1 φ))
  have hameas (n : ℕ) : AEStronglyMeasurable (a n) (volume.prod volume) :=
    ((cutoffSecond1_measurable n).mul φ.continuous.measurable).aestronglyMeasurable
  have hbMeas (n : ℕ) : AEStronglyMeasurable (b n) (volume.prod volume) :=
    ((hbmeas n).mul (pairPartial1 φ).continuous.measurable).aestronglyMeasurable
  have hcmeas (n : ℕ) : AEStronglyMeasurable (c n) (volume.prod volume) :=
    ((pairCutoff_sub_one_measurable n).mul
      (pairPartial1 (pairPartial1 φ)).continuous.measurable).aestronglyMeasurable
  have hab := tendsto_eLpNorm_two_add a b hameas hbMeas ha hb
  let ab : ℕ → ℝ × ℝ → ℂ := fun n z => a n z + b n z
  have habmeas (n : ℕ) : AEStronglyMeasurable (ab n) (volume.prod volume) :=
    (hameas n).add (hbMeas n)
  have hab' : Tendsto (fun n => eLpNorm (ab n) 2 (volume.prod volume))
      atTop (𝓝 0) := by simpa [ab] using hab
  have hsum := tendsto_eLpNorm_two_add ab c habmeas hcmeas hab' hc
  apply hsum.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with z
  rw [pairPartial1_two_compactSchwartzApprox]
  dsimp [ab, a, b, c]
  ring

private theorem pairConjugatedSpatial_compactSchwartzApprox_tendsto_toLp
    (β : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun n =>
      (pairConjugatedSpatial β (compactSchwartzApprox n φ)).toLp 2
        (volume.prod volume)) atTop
      (𝓝 ((pairConjugatedSpatial β φ).toLp 2 (volume.prod volume))) := by
  let T : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] SpatialL2Two :=
    SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume.prod volume)
  have h00 := pairPartial0_two_compactSchwartzApprox_tendsto_toLp φ
  have h11 := pairPartial1_two_compactSchwartzApprox_tendsto_toLp φ
  have h0 := pairPartial0_compactSchwartzApprox_tendsto_toLp φ
  have hbase := compactSchwartzApprox_tendsto_toLp φ
  have hsum := ((h00.add h11).add
    (h0.const_smul (((2 * β : ℝ) : ℂ)))).add
      (hbase.const_smul (((β ^ 2 : ℝ) : ℂ)))
  apply hsum.congr'
  filter_upwards with n
  change _ = T (pairConjugatedSpatial β (compactSchwartzApprox n φ))
  rw [pairConjugatedSpatial, map_add, map_add, map_add, map_smul, map_smul]
  rfl

private def frequencyAdjointProbe (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) : SpatialL2Two :=
  fourierL2Two.symm
    ((-Complex.I * deriv (η : ℝ → ℂ) t) •
        φ.toLp 2 (volume.prod volume) +
      η t • (pairConjugatedSpatial β φ).toLp 2 (volume.prod volume))

private def frequencyRightProbe (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) : SpatialL2Two :=
  η t • fourierL2Two.symm (φ.toLp 2 (volume.prod volume))

private lemma weak_frequency_pairing_compact_simplified_right
    (η : 𝓢(ℝ, ℂ)) (φ : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) :
    ((η t • pairSchwartzFourierInv φ).toLp 2 (volume.prod volume)) =
      frequencyRightProbe η φ t := by
  let T : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] SpatialL2Two :=
    SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume.prod volume)
  unfold frequencyRightProbe
  change T (η t • pairSchwartzFourierInv φ) = _
  rw [map_smul]
  change η t • (pairSchwartzFourierInv φ).toLp 2 (volume.prod volume) = _
  rw [fourierL2Two_symm_toLp]

private theorem weak_frequency_pairing_compact_simplified'
    (β : ℝ) (U R : Spacetime2)
    (hweak : IsWeakSchrodinger2D U R)
    (hw : AEStronglyMeasurable (exponentialWeight β U)
      (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable (exponentialWeight β R)
      (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight β U) < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight β R) < ⊤)
    (η : 𝓢(ℝ, ℂ)) (hη : HasCompactSupport (η : ℝ → ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ × ℝ → ℂ)) :
    (∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t))
        (frequencyAdjointProbe β η φ t) ∂volume) =
      ∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t))
        (frequencyRightProbe η φ t) ∂volume := by
  have heq := weak_frequency_pairing β U R hweak hw hf hwfinite hffinite
    η hη φ hφ
  calc
    _ = ∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t))
        ((pairSchwartzFourierInv (separatedSpatialAdjoint β η φ t)).toLp 2
          (volume.prod volume)) ∂volume := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      unfold frequencyAdjointProbe
      rw [show (-Complex.I * deriv (η : ℝ → ℂ) t) •
              φ.toLp 2 (volume.prod volume) +
            η t • (pairConjugatedSpatial β φ).toLp 2 (volume.prod volume) =
          (separatedSpatialAdjoint β η φ t).toLp 2 (volume.prod volume) by
        let T : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] SpatialL2Two :=
          SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume.prod volume)
        change _ = T (separatedSpatialAdjoint β η φ t)
        rw [separatedSpatialAdjoint, map_add, map_smul, map_smul]
        rfl]
      exact fourierL2Two_symm_toLp (separatedSpatialAdjoint β η φ t)
    _ = _ := heq.trans (by
      apply integral_congr_ae
      filter_upwards with t
      rw [weak_frequency_pairing_compact_simplified_right])

private lemma frequencyAdjointProbe_continuous (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) : Continuous (frequencyAdjointProbe β η φ) := by
  have hηd : Continuous (deriv (η : ℝ → ℂ)) := by
    simpa only [iteratedDeriv_one] using
      (η.smooth ⊤).continuous_iteratedDeriv 1 (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  unfold frequencyAdjointProbe
  fun_prop

private lemma frequencyRightProbe_continuous (η : 𝓢(ℝ, ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) : Continuous (frequencyRightProbe η φ) := by
  unfold frequencyRightProbe
  fun_prop

private theorem weak_frequency_pairing_all
    (β : ℝ) (U R : Spacetime2)
    (hweak : IsWeakSchrodinger2D U R)
    (hw : AEStronglyMeasurable (exponentialWeight β U)
      (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable (exponentialWeight β R)
      (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight β U) < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight β R) < ⊤)
    (η : 𝓢(ℝ, ℂ)) (hη : HasCompactSupport (η : ℝ → ℂ))
    (φ : 𝓢(ℝ × ℝ, ℂ)) :
    (∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t))
        (frequencyAdjointProbe β η φ t) ∂volume) =
      ∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t))
        (frequencyRightProbe η φ t) ∂volume := by
  let φn : ℕ → 𝓢(ℝ × ℝ, ℂ) := fun n => compactSchwartzApprox n φ
  let Y : ℝ → SpatialL2Two := fun t =>
    fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t)
  let G : ℝ → SpatialL2Two := fun t =>
    fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t)
  have hφn (n : ℕ) : HasCompactSupport (φn n : ℝ × ℝ → ℂ) :=
    compactSchwartzApprox_hasCompactSupport n φ
  have heqn (n : ℕ) :
      (∫ t, bilinearL2Two (Y t) (frequencyAdjointProbe β η (φn n) t) ∂volume) =
        ∫ t, bilinearL2Two (G t) (frequencyRightProbe η (φn n) t) ∂volume :=
    weak_frequency_pairing_compact_simplified' β U R hweak hw hf hwfinite
      hffinite η hη (φn n) (hφn n)
  have hYstrong : StronglyMeasurable Y :=
    fourierL2Two.continuous.comp_stronglyMeasurable
      (carlemanSourceCurve_stronglyMeasurable (exponentialWeight β U) hw)
  have hGint : Integrable G := by
    exact (fourierL2Two.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp
      (carlemanSourceCurve_integrable (exponentialWeight β R) hf hffinite)
  let W : ℝ := (scalarMixedENorm volume (volume.prod volume) ⊤ 2
    (exponentialWeight β U)).toReal
  have hYbound : ∀ᵐ t ∂volume, ‖Y t‖ ≤ W := by
    filter_upwards [enorm_carlemanSolutionCurve_le
      (exponentialWeight β U) hw hwfinite] with t ht
    have htop : scalarMixedENorm volume (volume.prod volume) ⊤ 2
        (exponentialWeight β U) ≠ ⊤ := hwfinite.ne
    have ht' : ‖Y t‖ₑ ≤ scalarMixedENorm volume (volume.prod volume) ⊤ 2
        (exponentialWeight β U) := by
      simpa only [Y, LinearIsometryEquiv.enorm_map] using ht
    have hreal := ENNReal.toReal_mono htop ht'
    rw [toReal_enorm] at hreal
    exact hreal
  have hηint : Integrable (η : ℝ → ℂ) := η.integrable
  have hηdcont : Continuous (deriv (η : ℝ → ℂ)) := by
    simpa only [iteratedDeriv_one] using
      (η.smooth ⊤).continuous_iteratedDeriv 1 (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hηdint : Integrable (deriv (η : ℝ → ℂ)) :=
    hηdcont.integrable_of_hasCompactSupport hη.deriv
  have hφto := compactSchwartzApprox_tendsto_toLp φ
  have hAto := pairConjugatedSpatial_compactSchwartzApprox_tendsto_toLp β φ
  let K0 : ℝ := ‖φ.toLp 2 (volume.prod volume)‖ + 1
  let K1 : ℝ := ‖(pairConjugatedSpatial β φ).toLp 2 (volume.prod volume)‖ + 1
  have hφbound : ∀ᶠ n : ℕ in atTop,
      ‖(φn n).toLp 2 (volume.prod volume)‖ ≤ K0 := by
    have hn := (tendsto_order.1 hφto.norm).2 K0 (by simp [K0])
    exact hn.mono fun n hn => hn.le
  have hAbound : ∀ᶠ n : ℕ in atTop,
      ‖(pairConjugatedSpatial β (φn n)).toLp 2 (volume.prod volume)‖ ≤ K1 := by
    have hn := (tendsto_order.1 hAto.norm).2 K1 (by simp [K1])
    exact hn.mono fun n hn => hn.le
  have hleft : Tendsto (fun n =>
      ∫ t, bilinearL2Two (Y t) (frequencyAdjointProbe β η (φn n) t) ∂volume)
      atTop (𝓝 (∫ t, bilinearL2Two (Y t)
        (frequencyAdjointProbe β η φ t) ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => W * (‖deriv (η : ℝ → ℂ) t‖ * K0 + ‖η t‖ * K1)) ?_ ?_ ?_ ?_
    · filter_upwards with n
      exact bilinearL2Two_aestronglyMeasurable
        hYstrong.aestronglyMeasurable
        (frequencyAdjointProbe_continuous β η (φn n)).aestronglyMeasurable
    · filter_upwards [hφbound, hAbound] with n hn0 hn1
      filter_upwards [hYbound] with t hYt
      calc
        ‖bilinearL2Two (Y t) (frequencyAdjointProbe β η (φn n) t)‖ ≤
            ‖Y t‖ * ‖frequencyAdjointProbe β η (φn n) t‖ :=
          norm_bilinearL2Two_le _ _
        _ ≤ W * (‖deriv (η : ℝ → ℂ) t‖ * K0 + ‖η t‖ * K1) := by
          apply mul_le_mul hYt
          · unfold frequencyAdjointProbe
            rw [LinearIsometryEquiv.norm_map]
            calc
              _ ≤ ‖(-Complex.I * deriv (η : ℝ → ℂ) t) •
                    (φn n).toLp 2 (volume.prod volume)‖ +
                  ‖η t • (pairConjugatedSpatial β (φn n)).toLp 2
                    (volume.prod volume)‖ := norm_add_le _ _
              _ ≤ ‖deriv (η : ℝ → ℂ) t‖ * K0 + ‖η t‖ * K1 := by
                simp only [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul]
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hn0 (norm_nonneg _))
                  (mul_le_mul_of_nonneg_left hn1 (norm_nonneg _))
          · positivity
          · exact (norm_nonneg _).trans hYt
      
    · exact ((hηdint.norm.mul_const K0).add
        (hηint.norm.mul_const K1)).const_mul W
    · filter_upwards with t
      have hprobe : Tendsto (fun n => frequencyAdjointProbe β η (φn n) t)
          atTop (𝓝 (frequencyAdjointProbe β η φ t)) := by
        unfold frequencyAdjointProbe
        exact fourierL2Two.symm.continuous.continuousAt.tendsto.comp
          ((hφto.const_smul (-Complex.I * deriv (η : ℝ → ℂ) t)).add
            (hAto.const_smul (η t)))
      exact tendsto_bilinearL2Two
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => Y t) atTop (𝓝 (Y t))) hprobe
  have hright : Tendsto (fun n =>
      ∫ t, bilinearL2Two (G t) (frequencyRightProbe η (φn n) t) ∂volume)
      atTop (𝓝 (∫ t, bilinearL2Two (G t)
        (frequencyRightProbe η φ t) ∂volume)) := by
    let Eη : ℝ := SchwartzMap.seminorm ℂ 0 0 η
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => K0 * Eη * ‖G t‖) ?_ ?_ ?_ ?_
    · filter_upwards with n
      exact bilinearL2Two_aestronglyMeasurable hGint.aestronglyMeasurable
        (frequencyRightProbe_continuous η (φn n)).aestronglyMeasurable
    · filter_upwards [hφbound] with n hn0
      filter_upwards with t
      calc
        ‖bilinearL2Two (G t) (frequencyRightProbe η (φn n) t)‖ ≤
            ‖G t‖ * ‖frequencyRightProbe η (φn n) t‖ :=
          norm_bilinearL2Two_le _ _
        _ ≤ ‖G t‖ * (‖η t‖ * K0) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          unfold frequencyRightProbe
          rw [norm_smul, LinearIsometryEquiv.norm_map]
          exact mul_le_mul_of_nonneg_left hn0 (norm_nonneg _)
        _ ≤ K0 * Eη * ‖G t‖ := by
          have hηnorm : ‖η t‖ ≤ Eη := SchwartzMap.norm_le_seminorm ℂ η t
          have hK0 : 0 ≤ K0 := by positivity
          calc
            ‖G t‖ * (‖η t‖ * K0) ≤ ‖G t‖ * (Eη * K0) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hηnorm hK0) (norm_nonneg _)
            _ = K0 * Eη * ‖G t‖ := by ring
    · exact hGint.norm.const_mul (K0 * Eη)
    · filter_upwards with t
      have hprobe : Tendsto (fun n => frequencyRightProbe η (φn n) t)
          atTop (𝓝 (frequencyRightProbe η φ t)) := by
        unfold frequencyRightProbe
        exact (fourierL2Two.symm.continuous.continuousAt.tendsto.comp hφto).const_smul (η t)
      exact tendsto_bilinearL2Two
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => G t) atTop (𝓝 (G t))) hprobe
  apply tendsto_nhds_unique hleft
  exact hright.congr' (by
    filter_upwards with n
    exact (heqn n).symm)

private def frequencyODEProbe (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (q : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) : SpatialL2Two :=
  (-Complex.I * deriv (η : ℝ → ℂ) t) • q.toLp 2 (volume.prod volume) +
    η t • (pairFrequencyConjugatedAdjoint β q).toLp 2 (volume.prod volume)

private def frequencyODERightProbe (η : 𝓢(ℝ, ℂ))
    (q : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) : SpatialL2Two :=
  η t • q.toLp 2 (volume.prod volume)

private lemma frequencyAdjointProbe_fourier (β : ℝ) (η : 𝓢(ℝ, ℂ))
    (q : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) :
    frequencyAdjointProbe β η (pairSchwartzFourier q) t =
      frequencyODEProbe β η q t := by
  unfold frequencyAdjointProbe frequencyODEProbe
  rw [show pairConjugatedSpatial β (pairSchwartzFourier q) =
      pairSchwartzFourier (pairFrequencyConjugatedAdjoint β q) by
    exact pairConjugatedSpatial_pairSchwartzFourier β q]
  rw [← fourierL2Two_toLp, ← fourierL2Two_toLp]
  rw [map_add, map_smul, map_smul,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

private lemma frequencyRightProbe_fourier (η : 𝓢(ℝ, ℂ))
    (q : 𝓢(ℝ × ℝ, ℂ)) (t : ℝ) :
    frequencyRightProbe η (pairSchwartzFourier q) t =
      frequencyODERightProbe η q t := by
  unfold frequencyRightProbe frequencyODERightProbe
  rw [← fourierL2Two_toLp, LinearIsometryEquiv.symm_apply_apply]

private theorem weak_frequency_ODE_pairing
    (β : ℝ) (U R : Spacetime2)
    (hweak : IsWeakSchrodinger2D U R)
    (hw : AEStronglyMeasurable (exponentialWeight β U)
      (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable (exponentialWeight β R)
      (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight β U) < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight β R) < ⊤)
    (η : 𝓢(ℝ, ℂ)) (hη : HasCompactSupport (η : ℝ → ℂ))
    (q : 𝓢(ℝ × ℝ, ℂ)) :
    (∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t))
        (frequencyODEProbe β η q t) ∂volume) =
      ∫ t, bilinearL2Two
        (fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t))
        (frequencyODERightProbe η q t) ∂volume := by
  have h := weak_frequency_pairing_all β U R hweak hw hf hwfinite hffinite
    η hη (pairSchwartzFourier q)
  simpa only [frequencyAdjointProbe_fourier, frequencyRightProbe_fourier] using h

/-! ## Smooth frequency branches for the vector-valued ODE estimate -/

private def carlemanFrequencyCoefficient (β : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  (((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) -
    Complex.I * ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ))

private def carlemanFrequencyGenerator (β : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  Complex.I * carlemanFrequencyCoefficient β ξ

private lemma carlemanFrequencyGenerator_contDiff (β : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (carlemanFrequencyGenerator β) := by
  unfold carlemanFrequencyGenerator carlemanFrequencyCoefficient
  apply contDiff_const.mul
  apply ContDiff.sub
  · exact Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul
        ((contDiff_fst.pow 2).add (contDiff_snd.pow 2))))
  · exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_fst))

private lemma carlemanFrequencyGenerator_re (β : ℝ) (ξ : ℝ × ℝ) :
    (carlemanFrequencyGenerator β ξ).re = 4 * Real.pi * β * ξ.1 := by
  rw [carlemanFrequencyGenerator, Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  rw [carlemanFrequencyCoefficient]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
    zero_sub, neg_neg, zero_add]

private def negativeInnerCutoff (n : ℕ) (x : ℝ) : ℂ :=
  (Real.smoothTransition (-((n : ℝ) + 1) * x - 1) : ℂ)

private def negativeOuterCutoff (n : ℕ) (x : ℝ) : ℂ :=
  (Real.smoothTransition (-((n : ℝ) + 1) * x) : ℂ)

private def positiveInnerCutoff (n : ℕ) (x : ℝ) : ℂ :=
  (Real.smoothTransition (((n : ℝ) + 1) * x - 1) : ℂ)

private def positiveOuterCutoff (n : ℕ) (x : ℝ) : ℂ :=
  (Real.smoothTransition (((n : ℝ) + 1) * x) : ℂ)

private def negativeBranchCutoffFun (n : ℕ) (ξ : ℝ × ℝ) : ℂ :=
  pairCutoff n ξ * negativeInnerCutoff n ξ.1

private def positiveBranchCutoffFun (n : ℕ) (ξ : ℝ × ℝ) : ℂ :=
  pairCutoff n ξ * positiveInnerCutoff n ξ.1

private def negativeBranchOuterFun (n : ℕ) (ξ : ℝ × ℝ) : ℂ :=
  pairCutoff (n + 1) ξ * negativeOuterCutoff n ξ.1

private def positiveBranchOuterFun (n : ℕ) (ξ : ℝ × ℝ) : ℂ :=
  pairCutoff (n + 1) ξ * positiveOuterCutoff n ξ.1

private lemma negativeBranchCutoffFun_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (negativeBranchCutoffFun n) := by
  unfold negativeBranchCutoffFun pairCutoff negativeInnerCutoff
  exact (((lineCutoff_contDiff n).comp contDiff_fst).mul
    ((lineCutoff_contDiff n).comp contDiff_snd)).mul
      (Complex.ofRealCLM.contDiff.comp
        ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
          ((contDiff_const.mul contDiff_fst).sub contDiff_const)))

private lemma positiveBranchCutoffFun_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (positiveBranchCutoffFun n) := by
  unfold positiveBranchCutoffFun pairCutoff positiveInnerCutoff
  exact (((lineCutoff_contDiff n).comp contDiff_fst).mul
    ((lineCutoff_contDiff n).comp contDiff_snd)).mul
      (Complex.ofRealCLM.contDiff.comp
        ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
          ((contDiff_const.mul contDiff_fst).sub contDiff_const)))

private lemma negativeBranchOuterFun_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (negativeBranchOuterFun n) := by
  unfold negativeBranchOuterFun pairCutoff negativeOuterCutoff
  exact (((lineCutoff_contDiff (n + 1)).comp contDiff_fst).mul
    ((lineCutoff_contDiff (n + 1)).comp contDiff_snd)).mul
      (Complex.ofRealCLM.contDiff.comp
        ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
          (contDiff_const.mul contDiff_fst)))

private lemma positiveBranchOuterFun_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (positiveBranchOuterFun n) := by
  unfold positiveBranchOuterFun pairCutoff positiveOuterCutoff
  exact (((lineCutoff_contDiff (n + 1)).comp contDiff_fst).mul
    ((lineCutoff_contDiff (n + 1)).comp contDiff_snd)).mul
      (Complex.ofRealCLM.contDiff.comp
        ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
          (contDiff_const.mul contDiff_fst)))

private lemma pairCutoff_hasCompactSupport_local (n : ℕ) :
    HasCompactSupport (pairCutoff n) := by
  let K := Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
    Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  refine HasCompactSupport.intro (K := K) (isCompact_Icc.prod isCompact_Icc) ?_
  intro ξ hξ
  by_cases hx : ξ.1 ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  · have hy : ξ.2 ∉ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
      fun hy => hξ ⟨hx, hy⟩
    simp [pairCutoff, lineCutoff_eq_zero_of_not_mem n ξ.2 hy]
  · simp [pairCutoff, lineCutoff_eq_zero_of_not_mem n ξ.1 hx]

private lemma negativeBranchCutoffFun_hasCompactSupport (n : ℕ) :
    HasCompactSupport (negativeBranchCutoffFun n) := by
  rw [show negativeBranchCutoffFun n =
      pairCutoff n * fun ξ => negativeInnerCutoff n ξ.1 by rfl]
  exact (pairCutoff_hasCompactSupport_local n).mul_right

private lemma positiveBranchCutoffFun_hasCompactSupport (n : ℕ) :
    HasCompactSupport (positiveBranchCutoffFun n) := by
  rw [show positiveBranchCutoffFun n =
      pairCutoff n * fun ξ => positiveInnerCutoff n ξ.1 by rfl]
  exact (pairCutoff_hasCompactSupport_local n).mul_right

private lemma negativeBranchOuterFun_hasCompactSupport (n : ℕ) :
    HasCompactSupport (negativeBranchOuterFun n) := by
  rw [show negativeBranchOuterFun n =
      pairCutoff (n + 1) * fun ξ => negativeOuterCutoff n ξ.1 by rfl]
  exact (pairCutoff_hasCompactSupport_local (n + 1)).mul_right

private lemma positiveBranchOuterFun_hasCompactSupport (n : ℕ) :
    HasCompactSupport (positiveBranchOuterFun n) := by
  rw [show positiveBranchOuterFun n =
      pairCutoff (n + 1) * fun ξ => positiveOuterCutoff n ξ.1 by rfl]
  exact (pairCutoff_hasCompactSupport_local (n + 1)).mul_right

private def negativeBranchCutoff (n : ℕ) : 𝓢(ℝ × ℝ, ℂ) :=
  (negativeBranchCutoffFun_hasCompactSupport n).toSchwartzMap
    (negativeBranchCutoffFun_contDiff n)

private def positiveBranchCutoff (n : ℕ) : 𝓢(ℝ × ℝ, ℂ) :=
  (positiveBranchCutoffFun_hasCompactSupport n).toSchwartzMap
    (positiveBranchCutoffFun_contDiff n)

private def negativeBranchOuter (n : ℕ) : 𝓢(ℝ × ℝ, ℂ) :=
  (negativeBranchOuterFun_hasCompactSupport n).toSchwartzMap
    (negativeBranchOuterFun_contDiff n)

private def positiveBranchOuter (n : ℕ) : 𝓢(ℝ × ℝ, ℂ) :=
  (positiveBranchOuterFun_hasCompactSupport n).toSchwartzMap
    (positiveBranchOuterFun_contDiff n)

private lemma lineCutoff_succ_mul (n : ℕ) (x : ℝ) :
    lineCutoff (n + 1) x * lineCutoff n x = lineCutoff n x := by
  by_cases hr : (n : ℝ) + 1 ≤ x
  · have hz := Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr)
    simp [lineCutoff, hz]
  · by_cases hl : x ≤ -((n : ℝ) + 1)
    · have hz : Real.smoothTransition ((n : ℝ) + 1 + x) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [lineCutoff, hz]
    · have ha : 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 - x := by
        push_cast
        linarith
      have hb : 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 + x := by
        push_cast
        linarith
      rw [lineCutoff, Real.smoothTransition.one_of_one_le ha,
        Real.smoothTransition.one_of_one_le hb]
      simp

private lemma pairCutoff_succ_mul (n : ℕ) (ξ : ℝ × ℝ) :
    pairCutoff (n + 1) ξ * pairCutoff n ξ = pairCutoff n ξ := by
  unfold pairCutoff
  calc
    lineCutoff (n + 1) ξ.1 * lineCutoff (n + 1) ξ.2 *
        (lineCutoff n ξ.1 * lineCutoff n ξ.2) =
        (lineCutoff (n + 1) ξ.1 * lineCutoff n ξ.1) *
          (lineCutoff (n + 1) ξ.2 * lineCutoff n ξ.2) := by ring
    _ = lineCutoff n ξ.1 * lineCutoff n ξ.2 := by
      rw [lineCutoff_succ_mul, lineCutoff_succ_mul]

private lemma negativeOuter_mul_inner (n : ℕ) (x : ℝ) :
    negativeOuterCutoff n x * negativeInnerCutoff n x =
      negativeInnerCutoff n x := by
  by_cases h : -((n : ℝ) + 1) * x - 1 ≤ 0
  · have hz := Real.smoothTransition.zero_of_nonpos h
    change ((Real.smoothTransition (-((n : ℝ) + 1) * x) : ℝ) : ℂ) *
      ((Real.smoothTransition (-((n : ℝ) + 1) * x - 1) : ℝ) : ℂ) =
        ((Real.smoothTransition (-((n : ℝ) + 1) * x - 1) : ℝ) : ℂ)
    rw [hz]
    simp
  · have ho : 1 ≤ -((n : ℝ) + 1) * x := by linarith
    change ((Real.smoothTransition (-((n : ℝ) + 1) * x) : ℝ) : ℂ) *
      ((Real.smoothTransition (-((n : ℝ) + 1) * x - 1) : ℝ) : ℂ) =
        ((Real.smoothTransition (-((n : ℝ) + 1) * x - 1) : ℝ) : ℂ)
    rw [Real.smoothTransition.one_of_one_le ho]
    simp

private lemma positiveOuter_mul_inner (n : ℕ) (x : ℝ) :
    positiveOuterCutoff n x * positiveInnerCutoff n x =
      positiveInnerCutoff n x := by
  by_cases h : ((n : ℝ) + 1) * x - 1 ≤ 0
  · have hz := Real.smoothTransition.zero_of_nonpos h
    simp [positiveOuterCutoff, positiveInnerCutoff, hz]
  · have ho : 1 ≤ ((n : ℝ) + 1) * x := by linarith
    simp [positiveOuterCutoff, positiveInnerCutoff,
      Real.smoothTransition.one_of_one_le ho]

private lemma negativeBranchOuter_mul_cutoff (n : ℕ) (ξ : ℝ × ℝ) :
    negativeBranchOuter n ξ * negativeBranchCutoff n ξ =
      negativeBranchCutoff n ξ := by
  change negativeBranchOuterFun n ξ * negativeBranchCutoffFun n ξ = _
  unfold negativeBranchOuterFun negativeBranchCutoffFun
  change pairCutoff (n + 1) ξ * negativeOuterCutoff n ξ.1 *
      (pairCutoff n ξ * negativeInnerCutoff n ξ.1) =
    pairCutoff n ξ * negativeInnerCutoff n ξ.1
  calc
    _ = (pairCutoff (n + 1) ξ * pairCutoff n ξ) *
        (negativeOuterCutoff n ξ.1 * negativeInnerCutoff n ξ.1) := by ring
    _ = _ := by rw [pairCutoff_succ_mul, negativeOuter_mul_inner]

private lemma positiveBranchOuter_mul_cutoff (n : ℕ) (ξ : ℝ × ℝ) :
    positiveBranchOuter n ξ * positiveBranchCutoff n ξ =
      positiveBranchCutoff n ξ := by
  change positiveBranchOuterFun n ξ * positiveBranchCutoffFun n ξ = _
  unfold positiveBranchOuterFun positiveBranchCutoffFun
  change pairCutoff (n + 1) ξ * positiveOuterCutoff n ξ.1 *
      (pairCutoff n ξ * positiveInnerCutoff n ξ.1) =
    pairCutoff n ξ * positiveInnerCutoff n ξ.1
  calc
    _ = (pairCutoff (n + 1) ξ * pairCutoff n ξ) *
        (positiveOuterCutoff n ξ.1 * positiveInnerCutoff n ξ.1) := by ring
    _ = _ := by rw [pairCutoff_succ_mul, positiveOuter_mul_inner]

private def negativeBranchGeneratorFun (β : ℝ) (n : ℕ) (ξ : ℝ × ℝ) : ℂ :=
  carlemanFrequencyGenerator β ξ * negativeBranchOuter n ξ

private def positiveBranchGeneratorFun (β : ℝ) (n : ℕ) (ξ : ℝ × ℝ) : ℂ :=
  carlemanFrequencyGenerator β ξ * positiveBranchOuter n ξ

private lemma negativeBranchGeneratorFun_contDiff (β : ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (negativeBranchGeneratorFun β n) := by
  exact (carlemanFrequencyGenerator_contDiff β).mul
    ((negativeBranchOuter n).smooth ⊤)

private lemma positiveBranchGeneratorFun_contDiff (β : ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (positiveBranchGeneratorFun β n) := by
  exact (carlemanFrequencyGenerator_contDiff β).mul
    ((positiveBranchOuter n).smooth ⊤)

private lemma negativeBranchGeneratorFun_hasCompactSupport (β : ℝ) (n : ℕ) :
    HasCompactSupport (negativeBranchGeneratorFun β n) := by
  rw [show negativeBranchGeneratorFun β n =
      carlemanFrequencyGenerator β * negativeBranchOuterFun n by rfl]
  exact (negativeBranchOuterFun_hasCompactSupport n).mul_left

private lemma positiveBranchGeneratorFun_hasCompactSupport (β : ℝ) (n : ℕ) :
    HasCompactSupport (positiveBranchGeneratorFun β n) := by
  rw [show positiveBranchGeneratorFun β n =
      carlemanFrequencyGenerator β * positiveBranchOuterFun n by rfl]
  exact (positiveBranchOuterFun_hasCompactSupport n).mul_left

private def negativeBranchGenerator (β : ℝ) (n : ℕ) : 𝓢(ℝ × ℝ, ℂ) :=
  (negativeBranchGeneratorFun_hasCompactSupport β n).toSchwartzMap
    (negativeBranchGeneratorFun_contDiff β n)

private def positiveBranchGenerator (β : ℝ) (n : ℕ) : 𝓢(ℝ × ℝ, ℂ) :=
  (positiveBranchGeneratorFun_hasCompactSupport β n).toSchwartzMap
    (positiveBranchGeneratorFun_contDiff β n)

private def negativeGeneratorBound (β : ℝ) (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (negativeBranchGenerator β n)

private def positiveGeneratorBound (β : ℝ) (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (positiveBranchGenerator β n)

private lemma negativeGeneratorBound_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ negativeGeneratorBound β n := apply_nonneg _ _

private lemma positiveGeneratorBound_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ positiveGeneratorBound β n := apply_nonneg _ _

private lemma norm_negativeBranchGenerator_le (β : ℝ) (n : ℕ) (ξ : ℝ × ℝ) :
    ‖negativeBranchGenerator β n ξ‖ ≤ negativeGeneratorBound β n :=
  SchwartzMap.norm_le_seminorm ℂ _ _

private lemma norm_positiveBranchGenerator_le (β : ℝ) (n : ℕ) (ξ : ℝ × ℝ) :
    ‖positiveBranchGenerator β n ξ‖ ≤ positiveGeneratorBound β n :=
  SchwartzMap.norm_le_seminorm ℂ _ _

private lemma norm_pairCutoff_le_one (n : ℕ) (ξ : ℝ × ℝ) :
    ‖pairCutoff n ξ‖ ≤ 1 := by
  rw [pairCutoff, norm_mul]
  exact mul_le_one₀ (norm_lineCutoff_le_one n ξ.1) (norm_nonneg _)
    (norm_lineCutoff_le_one n ξ.2)

private lemma norm_negativeBranchCutoff_le_one (n : ℕ) (ξ : ℝ × ℝ) :
    ‖negativeBranchCutoff n ξ‖ ≤ 1 := by
  change ‖pairCutoff n ξ * negativeInnerCutoff n ξ.1‖ ≤ 1
  rw [norm_mul]
  apply mul_le_one₀ (norm_pairCutoff_le_one n ξ) (norm_nonneg _)
  simpa [negativeInnerCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)] using
      Real.smoothTransition.le_one (-((n : ℝ) + 1) * ξ.1 - 1)

private lemma norm_positiveBranchCutoff_le_one (n : ℕ) (ξ : ℝ × ℝ) :
    ‖positiveBranchCutoff n ξ‖ ≤ 1 := by
  change ‖pairCutoff n ξ * positiveInnerCutoff n ξ.1‖ ≤ 1
  rw [norm_mul]
  apply mul_le_one₀ (norm_pairCutoff_le_one n ξ) (norm_nonneg _)
  simpa [positiveInnerCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)] using
      Real.smoothTransition.le_one (((n : ℝ) + 1) * ξ.1 - 1)

private lemma negativeBranchOuter_im (n : ℕ) (ξ : ℝ × ℝ) :
    (negativeBranchOuter n ξ).im = 0 := by
  change (negativeBranchOuterFun n ξ).im = 0
  unfold negativeBranchOuterFun negativeOuterCutoff pairCutoff lineCutoff
  simp

private lemma positiveBranchOuter_im (n : ℕ) (ξ : ℝ × ℝ) :
    (positiveBranchOuter n ξ).im = 0 := by
  change (positiveBranchOuterFun n ξ).im = 0
  unfold positiveBranchOuterFun positiveOuterCutoff pairCutoff lineCutoff
  simp

private lemma negativeBranchOuter_re_nonneg (n : ℕ) (ξ : ℝ × ℝ) :
    0 ≤ (negativeBranchOuter n ξ).re := by
  change 0 ≤ (negativeBranchOuterFun n ξ).re
  unfold negativeBranchOuterFun negativeOuterCutoff pairCutoff lineCutoff
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
      (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)))
    (Real.smoothTransition.nonneg _)

private lemma positiveBranchOuter_re_nonneg (n : ℕ) (ξ : ℝ × ℝ) :
    0 ≤ (positiveBranchOuter n ξ).re := by
  change 0 ≤ (positiveBranchOuterFun n ξ).re
  unfold positiveBranchOuterFun positiveOuterCutoff pairCutoff lineCutoff
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
      (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)))
    (Real.smoothTransition.nonneg _)

private lemma negativeBranchGenerator_re_nonpos (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (ξ : ℝ × ℝ) : (negativeBranchGenerator β n ξ).re ≤ 0 := by
  by_cases hx : ξ.1 ≤ 0
  · change (carlemanFrequencyGenerator β ξ * negativeBranchOuter n ξ).re ≤ 0
    rw [Complex.mul_re, negativeBranchOuter_im, mul_zero, sub_zero,
      carlemanFrequencyGenerator_re]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx)
      (negativeBranchOuter_re_nonneg n ξ)
  · have hxpos : 0 < ξ.1 := lt_of_not_ge hx
    have hz : negativeOuterCutoff n ξ.1 = 0 := by
      unfold negativeOuterCutoff
      rw [Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (by positivity : 0 ≤ (n : ℝ) + 1)) hxpos.le)]
      rfl
    change (carlemanFrequencyGenerator β ξ * negativeBranchOuterFun n ξ).re ≤ 0
    simp [negativeBranchOuterFun, hz]

private lemma positiveBranchGenerator_re_nonneg (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (ξ : ℝ × ℝ) : 0 ≤ (positiveBranchGenerator β n ξ).re := by
  by_cases hx : 0 ≤ ξ.1
  · change 0 ≤ (carlemanFrequencyGenerator β ξ * positiveBranchOuter n ξ).re
    rw [Complex.mul_re, positiveBranchOuter_im, mul_zero, sub_zero,
      carlemanFrequencyGenerator_re]
    exact mul_nonneg (mul_nonneg (by positivity) hx)
      (positiveBranchOuter_re_nonneg n ξ)
  · have hxneg : ξ.1 < 0 := lt_of_not_ge hx
    have hz : positiveOuterCutoff n ξ.1 = 0 := by
      unfold positiveOuterCutoff
      rw [Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos
          (by positivity : 0 ≤ (n : ℝ) + 1) hxneg.le)]
      rfl
    change 0 ≤ (carlemanFrequencyGenerator β ξ * positiveBranchOuterFun n ξ).re
    simp [positiveBranchOuterFun, hz]

private def negativeCutoffOperator (n : ℕ) : SpatialL2Two →L[ℂ] SpatialL2Two :=
  l2FrequencyMultiplierCLM (negativeBranchCutoff n)
    (negativeBranchCutoff n).continuous.measurable 1 zero_le_one
    (norm_negativeBranchCutoff_le_one n)

private def positiveCutoffOperator (n : ℕ) : SpatialL2Two →L[ℂ] SpatialL2Two :=
  l2FrequencyMultiplierCLM (positiveBranchCutoff n)
    (positiveBranchCutoff n).continuous.measurable 1 zero_le_one
    (norm_positiveBranchCutoff_le_one n)

private def negativeGeneratorOperator (β : ℝ) (n : ℕ) :
    SpatialL2Two →L[ℂ] SpatialL2Two :=
  l2FrequencyMultiplierCLM (negativeBranchGenerator β n)
    (negativeBranchGenerator β n).continuous.measurable
    (negativeGeneratorBound β n) (negativeGeneratorBound_nonneg β n)
    (norm_negativeBranchGenerator_le β n)

private def positiveGeneratorOperator (β : ℝ) (n : ℕ) :
    SpatialL2Two →L[ℂ] SpatialL2Two :=
  l2FrequencyMultiplierCLM (positiveBranchGenerator β n)
    (positiveBranchGenerator β n).continuous.measurable
    (positiveGeneratorBound β n) (positiveGeneratorBound_nonneg β n)
    (norm_positiveBranchGenerator_le β n)

private def schwartzProduct (s q : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ s q

@[simp] private lemma schwartzProduct_apply (s q : 𝓢(ℝ × ℝ, ℂ))
    (ξ : ℝ × ℝ) : schwartzProduct s q ξ = s ξ * q ξ := by
  rw [schwartzProduct, SchwartzMap.smulLeftCLM_apply_apply]
  · exact smul_eq_mul _ _
  · exact s.hasTemperateGrowth

private lemma bilinear_multiplier_schwartz_swap
    (s : 𝓢(ℝ × ℝ, ℂ)) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖s ξ‖ ≤ C) (f : SpatialL2Two)
    (q : 𝓢(ℝ × ℝ, ℂ)) :
    bilinearL2Two
        (l2FrequencyMultiplierCLM s s.continuous.measurable C hC0 hC f)
        (q.toLp 2 (volume.prod volume)) =
      bilinearL2Two f ((schwartzProduct s q).toLp 2 (volume.prod volume)) := by
  rw [bilinearL2Two_eq_integral, bilinearL2Two_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_l2FrequencyMultiplier s s.continuous.measurable C hC f,
    q.coeFn_toLp 2 (volume.prod volume),
    (schwartzProduct s q).coeFn_toLp 2 (volume.prod volume)] with ξ hs hq hsq
  simp only [l2FrequencyMultiplierCLM_apply]
  rw [hs, hq, hsq, schwartzProduct_apply]
  change (s ξ * (f : ℝ × ℝ → ℂ) ξ) * q ξ =
    (f : ℝ × ℝ → ℂ) ξ * (s ξ * q ξ)
  ring

private lemma negative_branch_symbol_identity (β : ℝ) (n : ℕ)
    (q : 𝓢(ℝ × ℝ, ℂ)) :
    schwartzProduct (negativeBranchCutoff n)
        (schwartzProduct (negativeBranchGenerator β n) q) =
      Complex.I • pairFrequencyConjugatedAdjoint β
        (schwartzProduct (negativeBranchCutoff n) q) := by
  ext ξ
  simp only [schwartzProduct_apply, smul_apply, smul_eq_mul]
  rw [pairFrequencyConjugatedAdjoint_apply]
  rw [show negativeBranchGenerator β n ξ =
    carlemanFrequencyGenerator β ξ * negativeBranchOuter n ξ by rfl]
  rw [schwartzProduct_apply]
  change negativeBranchCutoff n ξ *
      (carlemanFrequencyGenerator β ξ * negativeBranchOuter n ξ * q ξ) =
    Complex.I * (carlemanFrequencyCoefficient β ξ *
      (negativeBranchCutoff n ξ * q ξ))
  rw [carlemanFrequencyGenerator]
  have hcut : negativeBranchCutoff n ξ * negativeBranchOuter n ξ =
      negativeBranchCutoff n ξ := by
    rw [mul_comm, negativeBranchOuter_mul_cutoff]
  calc
    negativeBranchCutoff n ξ *
        (Complex.I * carlemanFrequencyCoefficient β ξ *
          negativeBranchOuter n ξ * q ξ) =
        Complex.I * carlemanFrequencyCoefficient β ξ *
          (negativeBranchCutoff n ξ * negativeBranchOuter n ξ) * q ξ := by ring
    _ = _ := by rw [hcut]; ring

private lemma positive_branch_symbol_identity (β : ℝ) (n : ℕ)
    (q : 𝓢(ℝ × ℝ, ℂ)) :
    schwartzProduct (positiveBranchCutoff n)
        (schwartzProduct (positiveBranchGenerator β n) q) =
      Complex.I • pairFrequencyConjugatedAdjoint β
        (schwartzProduct (positiveBranchCutoff n) q) := by
  ext ξ
  simp only [schwartzProduct_apply, smul_apply, smul_eq_mul]
  rw [pairFrequencyConjugatedAdjoint_apply]
  rw [show positiveBranchGenerator β n ξ =
    carlemanFrequencyGenerator β ξ * positiveBranchOuter n ξ by rfl]
  rw [schwartzProduct_apply]
  change positiveBranchCutoff n ξ *
      (carlemanFrequencyGenerator β ξ * positiveBranchOuter n ξ * q ξ) =
    Complex.I * (carlemanFrequencyCoefficient β ξ *
      (positiveBranchCutoff n ξ * q ξ))
  rw [carlemanFrequencyGenerator]
  have hcut : positiveBranchCutoff n ξ * positiveBranchOuter n ξ =
      positiveBranchCutoff n ξ := by
    rw [mul_comm, positiveBranchOuter_mul_cutoff]
  calc
    positiveBranchCutoff n ξ *
        (Complex.I * carlemanFrequencyCoefficient β ξ *
          positiveBranchOuter n ξ * q ξ) =
        Complex.I * carlemanFrequencyCoefficient β ξ *
          (positiveBranchCutoff n ξ * positiveBranchOuter n ξ) * q ξ := by ring
    _ = _ := by rw [hcut]; ring

private lemma bilinearL2Two_sub_left_local
    (f₁ f₂ q : SpatialL2Two) :
    bilinearL2Two (f₁ - f₂) q =
      bilinearL2Two f₁ q - bilinearL2Two f₂ q := by
  rw [sub_eq_add_neg, bilinearL2Two_add_left]
  have hneg : bilinearL2Two (-f₂) q = -bilinearL2Two f₂ q := by
    rw [show -f₂ = (-1 : ℂ) • f₂ by simp, bilinearL2Two_smul_left]
    simp
  rw [hneg, sub_eq_add_neg]

private theorem localized_weak_vector_ode
    (β : ℝ) (Y G : ℝ → SpatialL2Two)
    (hpair : ∀ (η : 𝓢(ℝ, ℂ)), HasCompactSupport (η : ℝ → ℂ) →
      ∀ q : 𝓢(ℝ × ℝ, ℂ),
        (∫ t, bilinearL2Two (Y t) (frequencyODEProbe β η q t) ∂volume) =
          ∫ t, bilinearL2Two (G t) (frequencyODERightProbe η q t) ∂volume)
    (hYloc : LocallyIntegrable Y volume) (hGint : Integrable G volume)
    (χ m : 𝓢(ℝ × ℝ, ℂ)) (Cχ Cm : ℝ)
    (hCχ0 : 0 ≤ Cχ) (hCm0 : 0 ≤ Cm)
    (hCχ : ∀ ξ, ‖χ ξ‖ ≤ Cχ) (hCm : ∀ ξ, ‖m ξ‖ ≤ Cm)
    (hsymbol : ∀ q : 𝓢(ℝ × ℝ, ℂ),
      schwartzProduct χ (schwartzProduct m q) =
        Complex.I • pairFrequencyConjugatedAdjoint β
          (schwartzProduct χ q)) :
    IsWeakVectorODE
      (l2FrequencyMultiplierCLM m m.continuous.measurable Cm hCm0 hCm)
      (fun t => l2FrequencyMultiplierCLM χ χ.continuous.measurable
        Cχ hCχ0 hCχ (Y t))
      (fun t => (-Complex.I) •
        l2FrequencyMultiplierCLM χ χ.continuous.measurable
          Cχ hCχ0 hCχ (G t)) := by
  let Mχ := l2FrequencyMultiplierCLM χ χ.continuous.measurable
    Cχ hCχ0 hCχ
  let A := l2FrequencyMultiplierCLM m m.continuous.measurable
    Cm hCm0 hCm
  let y : ℝ → SpatialL2Two := fun t => Mχ (Y t)
  let g : ℝ → SpatialL2Two := fun t => (-Complex.I) • Mχ (G t)
  have hy : LocallyIntegrable y volume := by
    intro K
    exact Mχ.integrableAtFilter_comp (hYloc K)
  have hAy : LocallyIntegrable (fun t => A (y t)) volume := by
    intro K
    exact A.integrableAtFilter_comp (hy K)
  have hgBase : Integrable (fun t => Mχ (G t)) volume :=
    Mχ.integrable_comp hGint
  have hg : Integrable g volume := by
    have h := hgBase.smul (-Complex.I)
    apply h.congr
    filter_upwards with t
    rfl
  intro η hη
  have hηdcont : Continuous (deriv (η : ℝ → ℂ)) := by
    simpa only [iteratedDeriv_one] using
      (η.smooth ⊤).continuous_iteratedDeriv 1 (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hηdcomp : HasCompactSupport (deriv (η : ℝ → ℂ)) := hη.deriv
  have hintD : Integrable (fun t =>
      (-deriv (η : ℝ → ℂ) t) • y t) volume := by
    exact hy.integrable_smul_left_of_hasCompactSupport
      hηdcont.neg hηdcomp.neg
  have hintA : Integrable (fun t => η t • A (y t)) volume :=
    hAy.integrable_smul_left_of_hasCompactSupport η.continuous hη
  have hintL : Integrable (fun t =>
      (-deriv (η : ℝ → ℂ) t) • y t - η t • A (y t)) volume :=
    hintD.sub hintA
  have hintR : Integrable (fun t => η t • g t) volume :=
    hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport η.continuous hη
  have hscalar (q : 𝓢(ℝ × ℝ, ℂ)) :
      (∫ t, bilinearL2Two
          ((-deriv (η : ℝ → ℂ) t) • y t - η t • A (y t))
          (q.toLp 2 (volume.prod volume)) ∂volume) =
        ∫ t, bilinearL2Two (η t • g t)
          (q.toLp 2 (volume.prod volume)) ∂volume := by
    have hBy (t : ℝ) :
        bilinearL2Two (y t) (q.toLp 2 (volume.prod volume)) =
          bilinearL2Two (Y t)
            ((schwartzProduct χ q).toLp 2 (volume.prod volume)) := by
      exact bilinear_multiplier_schwartz_swap χ Cχ hCχ0 hCχ (Y t) q
    have hBA (t : ℝ) :
        bilinearL2Two (A (y t)) (q.toLp 2 (volume.prod volume)) =
          Complex.I * bilinearL2Two (Y t)
            ((pairFrequencyConjugatedAdjoint β
              (schwartzProduct χ q)).toLp 2 (volume.prod volume)) := by
      calc
        bilinearL2Two (A (y t)) (q.toLp 2 (volume.prod volume)) =
            bilinearL2Two (y t)
              ((schwartzProduct m q).toLp 2 (volume.prod volume)) :=
          bilinear_multiplier_schwartz_swap m Cm hCm0 hCm (y t) q
        _ = bilinearL2Two (Y t)
              ((schwartzProduct χ (schwartzProduct m q)).toLp 2
                (volume.prod volume)) :=
          bilinear_multiplier_schwartz_swap χ Cχ hCχ0 hCχ (Y t)
            (schwartzProduct m q)
        _ = bilinearL2Two (Y t)
              ((Complex.I • pairFrequencyConjugatedAdjoint β
                (schwartzProduct χ q)).toLp 2 (volume.prod volume)) := by
          rw [hsymbol q]
        _ = _ := by
          let T : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] SpatialL2Two :=
            SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume.prod volume)
          change bilinearL2Two (Y t)
              (T (Complex.I • pairFrequencyConjugatedAdjoint β
                (schwartzProduct χ q))) = _
          rw [map_smul, bilinearL2Two_smul_right]
          rfl
    have hBg (t : ℝ) :
        bilinearL2Two (g t) (q.toLp 2 (volume.prod volume)) =
          (-Complex.I) * bilinearL2Two (G t)
            ((schwartzProduct χ q).toLp 2 (volume.prod volume)) := by
      rw [show g t = (-Complex.I) • Mχ (G t) by rfl,
        bilinearL2Two_smul_left]
      rw [bilinear_multiplier_schwartz_swap χ Cχ hCχ0 hCχ (G t) q]
    have hpde := hpair η hη (schwartzProduct χ q)
    calc
      (∫ t, bilinearL2Two
          ((-deriv (η : ℝ → ℂ) t) • y t - η t • A (y t))
          (q.toLp 2 (volume.prod volume)) ∂volume) =
          (-Complex.I) * (∫ t, bilinearL2Two (Y t)
            (frequencyODEProbe β η (schwartzProduct χ q) t) ∂volume) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        rw [bilinearL2Two_sub_left_local, bilinearL2Two_smul_left,
          bilinearL2Two_smul_left, hBy t, hBA t]
        unfold frequencyODEProbe
        rw [bilinearL2Two_add_right, bilinearL2Two_smul_right,
          bilinearL2Two_smul_right]
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = (-Complex.I) * (∫ t, bilinearL2Two (G t)
            (frequencyODERightProbe η (schwartzProduct χ q) t) ∂volume) := by
        rw [hpde]
      _ = ∫ t, bilinearL2Two (η t • g t)
            (q.toLp 2 (volume.prod volume)) ∂volume := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        unfold frequencyODERightProbe
        rw [bilinearL2Two_smul_right, bilinearL2Two_smul_left, hBg t]
        ring
  apply sub_eq_zero.mp
  apply eq_zero_of_bilinear_schwartz
  intro q
  change bilinearL2TwoLeftCLM (q.toLp 2 (volume.prod volume))
      ((∫ t, (-deriv (η : ℝ → ℂ) t) • y t - η t • A (y t)) -
        ∫ t, η t • g t) = 0
  rw [map_sub, ← (bilinearL2TwoLeftCLM
    (q.toLp 2 (volume.prod volume))).integral_comp_comm hintL,
    ← (bilinearL2TwoLeftCLM
    (q.toLp 2 (volume.prod volume))).integral_comp_comm hintR]
  exact sub_eq_zero.mpr (hscalar q)

private lemma branchCutoff_sum_eventually_one (ξ : ℝ × ℝ) (hξ : ξ.1 ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      negativeBranchCutoff n ξ + positiveBranchCutoff n ξ = 1 := by
  have hp := pairCutoff_eventually_eq_one ξ
  rcases lt_or_gt_of_ne hξ with hx | hx
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 / (-ξ.1))
    filter_upwards [hp, eventually_ge_atTop N] with n hpair hn
    have hxneg : 0 < -ξ.1 := neg_pos.mpr hx
    have hnreal : (2 / (-ξ.1) : ℝ) < n := hN.trans_le (by exact_mod_cast hn)
    have hinner : 1 ≤ -((n : ℝ) + 1) * ξ.1 - 1 := by
      have hmul : 2 < (n : ℝ) * (-ξ.1) := by
        rw [div_lt_iff₀ hxneg] at hnreal
        exact hnreal
      nlinarith
    have hposzero : ((n : ℝ) + 1) * ξ.1 - 1 ≤ 0 := by
      have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    change pairCutoff n ξ *
        (Real.smoothTransition (-((n : ℝ) + 1) * ξ.1 - 1) : ℂ) +
      pairCutoff n ξ *
        (Real.smoothTransition (((n : ℝ) + 1) * ξ.1 - 1) : ℂ) = 1
    rw [hpair, Real.smoothTransition.one_of_one_le hinner,
      Real.smoothTransition.zero_of_nonpos hposzero]
    simp
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 / ξ.1)
    filter_upwards [hp, eventually_ge_atTop N] with n hpair hn
    have hnreal : (2 / ξ.1 : ℝ) < n := hN.trans_le (by exact_mod_cast hn)
    have hinner : 1 ≤ ((n : ℝ) + 1) * ξ.1 - 1 := by
      have hmul : 2 < (n : ℝ) * ξ.1 := by
        rw [div_lt_iff₀ hx] at hnreal
        exact hnreal
      nlinarith
    have hnegzero : -((n : ℝ) + 1) * ξ.1 - 1 ≤ 0 := by
      have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    change pairCutoff n ξ *
        (Real.smoothTransition (-((n : ℝ) + 1) * ξ.1 - 1) : ℂ) +
      pairCutoff n ξ *
        (Real.smoothTransition (((n : ℝ) + 1) * ξ.1 - 1) : ℂ) = 1
    rw [hpair, Real.smoothTransition.zero_of_nonpos hnegzero,
      Real.smoothTransition.one_of_one_le hinner]
    simp

private lemma pair_first_ne_zero_ae :
    ∀ᵐ ξ : ℝ × ℝ ∂volume.prod volume, ξ.1 ≠ 0 := by
  rw [Measure.ae_prod_iff_ae_ae (by
    exact (measurableSet_singleton (0 : ℝ)).compl.preimage measurable_fst)]
  filter_upwards [Measure.ae_ne volume 0] with x hx
  filter_upwards with y
  exact hx

private theorem tendsto_eLpNorm_two_mul_Lp
    (a : ℕ → ℝ × ℝ → ℂ) (C : ℝ) (hC0 : 0 ≤ C)
    (haMeas : ∀ n, Measurable (a n))
    (haBound : ∀ n ξ, ‖a n ξ‖ ≤ C)
    (haZero : ∀ᵐ ξ ∂volume.prod volume,
      ∀ᶠ n : ℕ in atTop, a n ξ = 0)
    (f : SpatialL2Two) :
    Tendsto (fun n => eLpNorm (fun ξ => a n ξ * (f : ℝ × ℝ → ℂ) ξ) 2
      (volume.prod volume)) atTop (𝓝 0) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  let CE : ℝ≥0∞ := ENNReal.ofReal C
  have hCEtop : CE ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint : Tendsto (fun n =>
      ∫⁻ ξ, ‖a n ξ * (f : ℝ × ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)
        ∂(volume.prod volume)) atTop (𝓝 0) := by
    have hDCT : Tendsto (fun n =>
        ∫⁻ ξ, ‖a n ξ * (f : ℝ × ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)
          ∂(volume.prod volume)) atTop
        (𝓝 (∫⁻ _ : ℝ × ℝ, (0 : ℝ≥0∞) ∂(volume.prod volume))) := by
      refine tendsto_lintegral_filter_of_dominated_convergence'
        (f := fun _ => 0)
        (fun ξ => (CE * ‖(f : ℝ × ℝ → ℂ) ξ‖ₑ) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
      · filter_upwards with n
        exact ((haMeas n).aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable f)).enorm.pow_const 2
      · filter_upwards with n
        filter_upwards with ξ
        rw [enorm_mul]
        have hnormE : ‖a n ξ‖ₑ ≤ CE := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (haBound n ξ)
        exact ENNReal.rpow_le_rpow
          (mul_le_mul_right' hnormE _) (by norm_num)
      · rw [show (fun ξ => (CE * ‖(f : ℝ × ℝ → ℂ) ξ‖ₑ) ^ (2 : ℝ)) =
            fun ξ => CE ^ (2 : ℝ) * ‖(f : ℝ × ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) by
          funext ξ
          exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCEtop)]
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCEtop)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
            (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            (Lp.memLp f).eLpNorm_lt_top).ne
      · filter_upwards [haZero] with ξ hξ
        apply tendsto_const_nhds.congr'
        filter_upwards [hξ] with n hn
        simp [hn]
    simpa using hDCT
  convert hint.ennrpow_const (1 / ENNReal.toReal 2) using 1 <;> norm_num

private theorem branchCutoffOperators_tendsto (f : SpatialL2Two) :
    Tendsto (fun n =>
      negativeCutoffOperator n f + positiveCutoffOperator n f)
      atTop (𝓝 f) := by
  conv_rhs => rw [← Lp.toLp_coeFn f (Lp.memLp f)]
  apply Lp.tendsto_Lp_of_tendsto_eLpNorm (f : ℝ × ℝ → ℂ) (Lp.memLp f)
  have hDCT := tendsto_eLpNorm_two_mul_Lp
    (fun n ξ => negativeBranchCutoff n ξ + positiveBranchCutoff n ξ - 1)
    3 (by norm_num)
    (fun n => ((negativeBranchCutoff n).continuous.measurable.add
      (positiveBranchCutoff n).continuous.measurable).sub measurable_const)
    (fun n ξ => by
      calc
        ‖negativeBranchCutoff n ξ + positiveBranchCutoff n ξ - 1‖ ≤
            ‖negativeBranchCutoff n ξ‖ + ‖positiveBranchCutoff n ξ‖ + 1 := by
          exact (norm_sub_le _ _).trans
            (add_le_add (norm_add_le _ _) (by norm_num))
        _ ≤ 1 + 1 + 1 := by
          gcongr
          · exact norm_negativeBranchCutoff_le_one n ξ
          · exact norm_positiveBranchCutoff_le_one n ξ
        _ = 3 := by norm_num)
    (pair_first_ne_zero_ae.mono fun ξ hξ => by
      filter_upwards [branchCutoff_sum_eventually_one ξ hξ] with n hn
      rw [hn, sub_self])
    f
  apply hDCT.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [
      Lp.coeFn_add (negativeCutoffOperator n f) (positiveCutoffOperator n f),
      coe_l2FrequencyMultiplier (negativeBranchCutoff n)
        (negativeBranchCutoff n).continuous.measurable 1
        (norm_negativeBranchCutoff_le_one n) f,
      coe_l2FrequencyMultiplier (positiveBranchCutoff n)
        (positiveBranchCutoff n).continuous.measurable 1
        (norm_positiveBranchCutoff_le_one n) f] with ξ hadd hneg hpos
  rw [Pi.sub_apply, hadd]
  simp only [Pi.add_apply]
  unfold negativeCutoffOperator positiveCutoffOperator
  simp only [l2FrequencyMultiplierCLM_apply]
  rw [hneg, hpos]
  ring

private theorem frequency_solution_ae_bound
    (β : ℝ) (hβ : 0 < β) (U R : Spacetime2)
    (hsupp : HasBoundedTimeSupport U)
    (hweak : IsWeakSchrodinger2D U R)
    (hw : AEStronglyMeasurable (exponentialWeight β U)
      (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable (exponentialWeight β R)
      (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight β U) < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight β R) < ⊤) :
    let Y : ℝ → SpatialL2Two := fun t =>
      fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t)
    let G : ℝ → SpatialL2Two := fun t =>
      fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t)
    ∀ᵐ t ∂volume, ‖Y t‖ ≤ 2 * ∫ s, ‖G s‖ := by
  let Y : ℝ → SpatialL2Two := fun t =>
    fourierL2Two (carlemanSourceCurve (exponentialWeight β U) hw t)
  let G : ℝ → SpatialL2Two := fun t =>
    fourierL2Two (carlemanSourceCurve (exponentialWeight β R) hf t)
  have hYstrong : StronglyMeasurable Y :=
    fourierL2Two.continuous.comp_stronglyMeasurable
      (carlemanSourceCurve_stronglyMeasurable (exponentialWeight β U) hw)
  have hGint : Integrable G := by
    exact (fourierL2Two.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp
      (carlemanSourceCurve_integrable (exponentialWeight β R) hf hffinite)
  let W : ℝ := (scalarMixedENorm volume (volume.prod volume) ⊤ 2
    (exponentialWeight β U)).toReal
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hYbound : ∀ᵐ t ∂volume, ‖Y t‖ ≤ W := by
    filter_upwards [enorm_carlemanSolutionCurve_le
      (exponentialWeight β U) hw hwfinite] with t ht
    have htop : scalarMixedENorm volume (volume.prod volume) ⊤ 2
        (exponentialWeight β U) ≠ ⊤ := hwfinite.ne
    have ht' : ‖Y t‖ₑ ≤ scalarMixedENorm volume (volume.prod volume) ⊤ 2
        (exponentialWeight β U) := by
      simpa only [Y, LinearIsometryEquiv.enorm_map] using ht
    have hreal := ENNReal.toReal_mono htop ht'
    rw [toReal_enorm] at hreal
    exact hreal
  have hYloc : LocallyIntegrable Y volume := by
    apply (locallyIntegrable_const W).mono hYstrong.aestronglyMeasurable
    filter_upwards [hYbound] with t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg hW0] using ht
  obtain ⟨a, b, hab, hsuppU⟩ := hsupp
  have hsuppW : ∀ᵐ p ∂(volume.prod (volume.prod volume)),
      p.1 ∉ Set.Icc a b → exponentialWeight β U p = 0 := by
    filter_upwards [hsuppU] with p hp ht
    rw [exponentialWeight, hp ht, mul_zero]
  have hsuppSlices := Measure.ae_ae_of_ae_prod hsuppW
  have hsections := carlemanSolutionCurve_section_ae
    (exponentialWeight β U) hw hwfinite
  have hsuppY : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → Y t = 0 := by
    filter_upwards [hsuppSlices, hsections] with t hs ht hout
    have hcurve : carlemanSourceCurve (exponentialWeight β U) hw t = 0 := by
      apply Lp.ext
      filter_upwards [ht, hs] with ξ hsec hzero
      rw [hsec, hzero hout]
      simp
    simp [Y, hcurve]
  have hpair : ∀ (η : 𝓢(ℝ, ℂ)), HasCompactSupport (η : ℝ → ℂ) →
      ∀ q : 𝓢(ℝ × ℝ, ℂ),
        (∫ t, bilinearL2Two (Y t) (frequencyODEProbe β η q t) ∂volume) =
          ∫ t, bilinearL2Two (G t) (frequencyODERightProbe η q t) ∂volume := by
    intro η hη q
    exact weak_frequency_ODE_pairing β U R hweak hw hf hwfinite hffinite η hη q
  have hnegWeak (n : ℕ) :
      IsWeakVectorODE (negativeGeneratorOperator β n)
        (fun t => negativeCutoffOperator n (Y t))
        (fun t => (-Complex.I) • negativeCutoffOperator n (G t)) := by
    exact localized_weak_vector_ode β Y G hpair hYloc hGint
      (negativeBranchCutoff n) (negativeBranchGenerator β n)
      1 (negativeGeneratorBound β n) zero_le_one
      (negativeGeneratorBound_nonneg β n)
      (norm_negativeBranchCutoff_le_one n)
      (norm_negativeBranchGenerator_le β n)
      (negative_branch_symbol_identity β n)
  have hposWeak (n : ℕ) :
      IsWeakVectorODE (positiveGeneratorOperator β n)
        (fun t => positiveCutoffOperator n (Y t))
        (fun t => (-Complex.I) • positiveCutoffOperator n (G t)) := by
    exact localized_weak_vector_ode β Y G hpair hYloc hGint
      (positiveBranchCutoff n) (positiveBranchGenerator β n)
      1 (positiveGeneratorBound β n) zero_le_one
      (positiveGeneratorBound_nonneg β n)
      (norm_positiveBranchCutoff_le_one n)
      (norm_positiveBranchGenerator_le β n)
      (positive_branch_symbol_identity β n)
  have hnegLoc (n : ℕ) :
      LocallyIntegrable (fun t => negativeCutoffOperator n (Y t)) volume := by
    intro K
    exact (negativeCutoffOperator n).integrableAtFilter_comp (hYloc K)
  have hposLoc (n : ℕ) :
      LocallyIntegrable (fun t => positiveCutoffOperator n (Y t)) volume := by
    intro K
    exact (positiveCutoffOperator n).integrableAtFilter_comp (hYloc K)
  have hnegGint (n : ℕ) :
      Integrable (fun t => (-Complex.I) • negativeCutoffOperator n (G t)) volume := by
    have hb := (negativeCutoffOperator n).integrable_comp hGint
    apply (hb.smul (-Complex.I)).congr
    filter_upwards with t
    rfl
  have hposGint (n : ℕ) :
      Integrable (fun t => (-Complex.I) • positiveCutoffOperator n (G t)) volume := by
    have hb := (positiveCutoffOperator n).integrable_comp hGint
    apply (hb.smul (-Complex.I)).congr
    filter_upwards with t
    rfl
  have hnegSupp (n : ℕ) :
      ∀ᵐ t ∂volume, t ∉ Set.Icc a b →
        negativeCutoffOperator n (Y t) = 0 := by
    filter_upwards [hsuppY] with t ht hout
    rw [ht hout, map_zero]
  have hposSupp (n : ℕ) :
      ∀ᵐ t ∂volume, t ∉ Set.Icc a b →
        positiveCutoffOperator n (Y t) = 0 := by
    filter_upwards [hsuppY] with t ht hout
    rw [ht hout, map_zero]
  have hneg (n : ℕ) : ∀ᵐ t ∂volume,
      ‖negativeCutoffOperator n (Y t)‖ ≤ ∫ s, ‖G s‖ := by
    let m := negativeBranchGenerator β n
    let C := negativeGeneratorBound β n
    let S : ℝ → SpatialL2Two →L[ℝ] SpatialL2Two := fun τ =>
      (l2ExpMultiplier m m.continuous.measurable C
        (negativeGeneratorBound_nonneg β n)
        (norm_negativeBranchGenerator_le β n) τ).restrictScalars ℝ
    have hraw := weakVectorODE_ae_norm_le_forward
      (negativeGeneratorOperator β n) S
      (fun τ => l2ExpMultiplierReal_hasDerivAt m m.continuous.measurable C
        (negativeGeneratorBound_nonneg β n)
        (norm_negativeBranchGenerator_le β n) τ)
      (by
        unfold S
        rw [l2ExpMultiplier_zero]
        rfl)
      (fun τ => l2ExpMultiplier_commutes m m.continuous.measurable C
        (negativeGeneratorBound_nonneg β n)
        (norm_negativeBranchGenerator_le β n) τ)
      (fun τ hτ x => l2ExpMultiplier_norm_le_one m m.continuous.measurable C
        (negativeGeneratorBound_nonneg β n)
        (norm_negativeBranchGenerator_le β n) τ
        (fun ξ => mul_nonpos_of_nonpos_of_nonneg
          (negativeBranchGenerator_re_nonpos β hβ n ξ) hτ) x)
      (fun t => negativeCutoffOperator n (Y t))
      (fun t => (-Complex.I) • negativeCutoffOperator n (G t))
      a b (hnegLoc n) (hnegGint n) (hnegSupp n) (hnegWeak n)
    filter_upwards [hraw] with t ht
    refine ht.trans ?_
    apply integral_mono_ae (hnegGint n).norm hGint.norm
    filter_upwards with s
    change ‖(-Complex.I) • negativeCutoffOperator n (G s)‖ ≤ ‖G s‖
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    unfold negativeCutoffOperator
    simpa only [l2FrequencyMultiplierCLM_apply, one_mul] using norm_l2FrequencyMultiplier_le
      (negativeBranchCutoff n) (negativeBranchCutoff n).continuous.measurable
      1 zero_le_one (norm_negativeBranchCutoff_le_one n) (G s)
  have hpos (n : ℕ) : ∀ᵐ t ∂volume,
      ‖positiveCutoffOperator n (Y t)‖ ≤ ∫ s, ‖G s‖ := by
    let m := positiveBranchGenerator β n
    let C := positiveGeneratorBound β n
    let S : ℝ → SpatialL2Two →L[ℝ] SpatialL2Two := fun τ =>
      (l2ExpMultiplier m m.continuous.measurable C
        (positiveGeneratorBound_nonneg β n)
        (norm_positiveBranchGenerator_le β n) τ).restrictScalars ℝ
    have hraw := weakVectorODE_ae_norm_le_backward
      (positiveGeneratorOperator β n) S
      (fun τ => l2ExpMultiplierReal_hasDerivAt m m.continuous.measurable C
        (positiveGeneratorBound_nonneg β n)
        (norm_positiveBranchGenerator_le β n) τ)
      (by
        unfold S
        rw [l2ExpMultiplier_zero]
        rfl)
      (fun τ => l2ExpMultiplier_commutes m m.continuous.measurable C
        (positiveGeneratorBound_nonneg β n)
        (norm_positiveBranchGenerator_le β n) τ)
      (fun τ hτ x => l2ExpMultiplier_norm_le_one m m.continuous.measurable C
        (positiveGeneratorBound_nonneg β n)
        (norm_positiveBranchGenerator_le β n) τ
        (fun ξ => mul_nonpos_of_nonneg_of_nonpos
          (positiveBranchGenerator_re_nonneg β hβ n ξ) hτ) x)
      (fun t => positiveCutoffOperator n (Y t))
      (fun t => (-Complex.I) • positiveCutoffOperator n (G t))
      a b (hposLoc n) (hposGint n) (hposSupp n) (hposWeak n)
    filter_upwards [hraw] with t ht
    refine ht.trans ?_
    apply integral_mono_ae (hposGint n).norm hGint.norm
    filter_upwards with s
    change ‖(-Complex.I) • positiveCutoffOperator n (G s)‖ ≤ ‖G s‖
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    unfold positiveCutoffOperator
    simpa only [l2FrequencyMultiplierCLM_apply, one_mul] using norm_l2FrequencyMultiplier_le
      (positiveBranchCutoff n) (positiveBranchCutoff n).continuous.measurable
      1 zero_le_one (norm_positiveBranchCutoff_le_one n) (G s)
  have hnegAll : ∀ᵐ t ∂volume, ∀ n,
      ‖negativeCutoffOperator n (Y t)‖ ≤ ∫ s, ‖G s‖ :=
    ae_all_iff.mpr hneg
  have hposAll : ∀ᵐ t ∂volume, ∀ n,
      ‖positiveCutoffOperator n (Y t)‖ ≤ ∫ s, ‖G s‖ :=
    ae_all_iff.mpr hpos
  filter_upwards [hnegAll, hposAll] with t hnt hpt
  exact le_of_tendsto (branchCutoffOperators_tendsto (Y t)).norm
    (Eventually.of_forall fun n => by
      calc
        ‖negativeCutoffOperator n (Y t) + positiveCutoffOperator n (Y t)‖ ≤
            ‖negativeCutoffOperator n (Y t)‖ +
              ‖positiveCutoffOperator n (Y t)‖ := norm_add_le _ _
        _ ≤ (∫ s, ‖G s‖) + ∫ s, ‖G s‖ := add_le_add (hnt n) (hpt n)
        _ = 2 * ∫ s, ‖G s‖ := by ring)

private theorem ofReal_integral_norm_fourier_source
    (f : Spacetime2)
    (hf : AEStronglyMeasurable f (volume.prod (volume.prod volume)))
    (hfinite : scalarMixedENorm volume (volume.prod volume) 1 2 f < ⊤) :
    ENNReal.ofReal (∫ t,
        ‖fourierL2Two (carlemanSourceCurve f hf t)‖) =
      scalarMixedENorm volume (volume.prod volume) 1 2 f := by
  have hcurve := carlemanSourceCurve_integrable f hf hfinite
  have hfreq : Integrable
      (fun t => fourierL2Two (carlemanSourceCurve f hf t)) :=
    (fourierL2Two.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hcurve
  rw [ofReal_integral_norm_eq_lintegral_enorm hfreq]
  have hnorm : (∫⁻ t,
      ‖fourierL2Two (carlemanSourceCurve f hf t)‖ₑ ∂volume) =
      ∫⁻ t, ‖carlemanSourceCurve f hf t‖ₑ ∂volume := by
    apply lintegral_congr
    intro t
    rw [LinearIsometryEquiv.enorm_map]
  rw [hnorm, lintegral_congr_ae
    (enorm_carlemanSourceCurve_ae f hf hfinite)]
  rw [scalarMixedENorm, eLpNorm_one_eq_lintegral_enorm]
  simp only [enorm_eq_self]

private theorem carleman_mixed_estimate
    (beta : ℝ) (hbeta : 0 < beta) (U R : Spacetime2)
    (hsupp : HasBoundedTimeSupport U)
    (hweak : IsWeakSchrodinger2D U R)
    (hw : AEStronglyMeasurable (exponentialWeight beta U)
      (volume.prod (volume.prod volume)))
    (hf : AEStronglyMeasurable (exponentialWeight beta R)
      (volume.prod (volume.prod volume)))
    (hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight beta U) < ⊤)
    (hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight beta R) < ⊤) :
    scalarMixedENorm volume (volume.prod volume) ⊤ 2
        (exponentialWeight beta U) ≤
      2 * scalarMixedENorm volume (volume.prod volume) 1 2
        (exponentialWeight beta R) := by
  let w := exponentialWeight beta U
  let f := exponentialWeight beta R
  let B := scalarMixedENorm volume (volume.prod volume) 1 2 f
  have hfreq := frequency_solution_ae_bound beta hbeta U R hsupp hweak
    hw hf hwfinite hffinite
  have hpoint : ∀ᵐ t ∂volume,
      ‖carlemanSourceCurve w hw t‖ₑ ≤ 2 * B := by
    filter_upwards [hfreq] with t ht
    rw [← ofReal_norm]
    have hreal : ‖carlemanSourceCurve w hw t‖ ≤
        2 * ∫ s, ‖fourierL2Two (carlemanSourceCurve f hf s)‖ := by
      calc
        ‖carlemanSourceCurve w hw t‖ =
            ‖fourierL2Two (carlemanSourceCurve w hw t)‖ := by
          rw [LinearIsometryEquiv.norm_map]
        _ ≤ 2 * ∫ s, ‖fourierL2Two (carlemanSourceCurve f hf s)‖ := ht
    calc
      ENNReal.ofReal ‖carlemanSourceCurve w hw t‖ ≤
          ENNReal.ofReal
            (2 * ∫ s, ‖fourierL2Two (carlemanSourceCurve f hf s)‖) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 2 * ENNReal.ofReal
          (∫ s, ‖fourierL2Two (carlemanSourceCurve f hf s)‖) := by
        rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        norm_num
      _ = 2 * B := by
        rw [ofReal_integral_norm_fourier_source f hf hffinite]
  have hsection : ∀ᵐ t ∂volume,
      sectionENorm (volume.prod volume) 2 w t ≤ 2 * B := by
    filter_upwards [enorm_carlemanSolutionCurve_ae w hw hwfinite, hpoint]
      with t hnorm ht
    rwa [hnorm] at ht
  rw [scalarMixedENorm, eLpNorm_exponent_top,
    eLpNormEssSup_eq_essSup_enorm]
  simp only [enorm_eq_self]
  exact essSup_le_of_ae_le (2 * B) hsection

/-- The graph-closed Carleman estimate, obtained from the two frequency
semigroups.  The numerical constant `2` comes from the positive and negative
first-frequency branches. -/
theorem carleman_closure :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (beta H : ℝ), 0 < beta →
      ∀ (U R : Spacetime2),
      HasBoundedTimeSupport U → VanishesAbove H U →
      IsWeakSchrodinger2D U R →
      carlemanXprimeNorm Set.univ (exponentialWeight beta U) < ⊤ →
      carlemanXNorm Set.univ (exponentialWeight beta R) < ⊤ →
      carlemanXprimeNorm Set.univ (exponentialWeight beta U) ≤
        C * carlemanXNorm Set.univ (exponentialWeight beta R) := by
  refine ⟨2, by norm_num, ?_⟩
  intro beta H hbeta U R hsupp _ hweak hUfinite hRfinite
  have hwRestr : AEStronglyMeasurable (exponentialWeight beta U)
      ((volume.restrict Set.univ).prod (volume.prod volume)) := by
    by_contra hn
    rw [carlemanXprimeNorm, if_neg hn] at hUfinite
    exact (lt_irrefl ⊤ hUfinite)
  have hfRestr : AEStronglyMeasurable (exponentialWeight beta R)
      ((volume.restrict Set.univ).prod (volume.prod volume)) := by
    by_contra hn
    rw [carlemanXNorm, if_neg hn] at hRfinite
    exact (lt_irrefl ⊤ hRfinite)
  have hw : AEStronglyMeasurable (exponentialWeight beta U)
      (volume.prod (volume.prod volume)) := by
    simpa only [Measure.restrict_univ] using hwRestr
  have hf : AEStronglyMeasurable (exponentialWeight beta R)
      (volume.prod (volume.prod volume)) := by
    simpa only [Measure.restrict_univ] using hfRestr
  have hwfinite : scalarMixedENorm volume (volume.prod volume) ⊤ 2
      (exponentialWeight beta U) < ⊤ := by
    rw [carlemanXprimeNorm, if_pos hwRestr] at hUfinite
    simpa only [Measure.restrict_univ] using hUfinite
  have hffinite : scalarMixedENorm volume (volume.prod volume) 1 2
      (exponentialWeight beta R) < ⊤ := by
    rw [carlemanXNorm, if_pos hfRestr] at hRfinite
    simpa only [Measure.restrict_univ] using hRfinite
  rw [carlemanXprimeNorm, if_pos hwRestr,
    carlemanXNorm, if_pos hfRestr]
  simp only [Measure.restrict_univ]
  exact carleman_mixed_estimate beta hbeta U R hsupp hweak hw hf
    hwfinite hffinite

theorem exponential_separation :
  ∃ epsilonStar : ℝ≥0∞, 0 < epsilonStar ∧
    ∀ (H : ℝ) (U V R : Spacetime2),
    HasBoundedTimeSupport U → VanishesAbove H U →
    IsWeakSchrodinger2D U (fun p => V p * U p + R p) →
    (∀ beta : ℝ, 0 < beta →
      carlemanXprimeNorm Set.univ (exponentialWeight beta U) < ⊤) →
    carlemanYNorm Set.univ V ≤ epsilonStar →
    Tendsto (fun beta : ℝ =>
      carlemanXNorm Set.univ (exponentialWeight beta R)) atTop (nhds 0) →
    ∀ᵐ p ∂(volume.prod (volume.prod volume)), 0 < p.2.1 → U p = 0 :=
  exponential_separation_of_carleman_closure carleman_closure

end CubicNLSPhaseRetrieval
