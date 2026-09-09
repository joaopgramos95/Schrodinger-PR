import Lean_Code.WronskianExterior
import Lean_Code.CarlemanFourier2D

/-!
# The free two-particle Schrödinger group

This is the two-dimensional analogue of `freeProp`, expressed on the pair
model `ℝ × ℝ`.  It is used to transport the absolutely-continuous exterior
curve from the interaction picture back to the physical weak equation.
-/

open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The multiplier for `exp (it(∂ₓ²+∂ᵧ²))`. -/
def twoSchrodingerSymbol (t : ℝ) (xi : ℝ × ℝ) : ℂ :=
  Complex.exp (((-(4 * Real.pi ^ 2 * t * (xi.1 ^ 2 + xi.2 ^ 2)) : ℝ) : ℂ) *
    Complex.I)

lemma norm_twoSchrodingerSymbol (t : ℝ) (xi : ℝ × ℝ) :
    ‖twoSchrodingerSymbol t xi‖ = 1 := by
  unfold twoSchrodingerSymbol
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_twoSchrodingerSymbol (t : ℝ) :
    Continuous (twoSchrodingerSymbol t) := by
  unfold twoSchrodingerSymbol
  fun_prop

/-- Multiplication by the two-particle free symbol on `L²(ℝ²)`. -/
def twoMultSymbol (t : ℝ) (g : TwoParticleL2) : TwoParticleL2 :=
  MemLp.toLp (fun xi => twoSchrodingerSymbol t xi * (g : ℝ × ℝ → ℂ) xi) (by
    have hm : AEStronglyMeasurable
        (fun xi => twoSchrodingerSymbol t xi * (g : ℝ × ℝ → ℂ) xi)
        (volume.prod volume) :=
      (continuous_twoSchrodingerSymbol t).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable g)
    refine ((Lp.memLp g).norm).mono' hm ?_
    filter_upwards with xi
    rw [norm_mul, norm_twoSchrodingerSymbol, one_mul])

lemma coe_twoMultSymbol (t : ℝ) (g : TwoParticleL2) :
    (twoMultSymbol t g : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun xi => twoSchrodingerSymbol t xi * (g : ℝ × ℝ → ℂ) xi := by
  exact MemLp.coeFn_toLp _

/-- The free two-particle propagator. -/
def twoFreeProp (t : ℝ) (f : TwoParticleL2) : TwoParticleL2 :=
  fourierL2Two.symm (twoMultSymbol t (fourierL2Two f))

lemma fourier_twoFreeProp (t : ℝ) (f : TwoParticleL2) :
    (fourierL2Two (twoFreeProp t f) : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun xi => twoSchrodingerSymbol t xi *
        (fourierL2Two f : ℝ × ℝ → ℂ) xi := by
  unfold twoFreeProp
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact coe_twoMultSymbol t (fourierL2Two f)

lemma norm_twoMultSymbol (t : ℝ) (g : TwoParticleL2) :
    ‖twoMultSymbol t g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [coe_twoMultSymbol t g] with xi hxi
  rw [hxi, norm_mul, norm_twoSchrodingerSymbol, one_mul]

lemma norm_twoFreeProp (t : ℝ) (f : TwoParticleL2) :
    ‖twoFreeProp t f‖ = ‖f‖ := by
  unfold twoFreeProp
  rw [LinearIsometryEquiv.norm_map, norm_twoMultSymbol,
    LinearIsometryEquiv.norm_map]

lemma twoMultSymbol_add (t : ℝ) (f g : TwoParticleL2) :
    twoMultSymbol t (f + g) = twoMultSymbol t f + twoMultSymbol t g := by
  apply Lp.ext
  filter_upwards [coe_twoMultSymbol t (f + g), coe_twoMultSymbol t f,
    coe_twoMultSymbol t g, Lp.coeFn_add f g,
    Lp.coeFn_add (twoMultSymbol t f) (twoMultSymbol t g)]
      with xi hfg hf hg hadd hout
  rw [hfg, hadd, hout]
  simp only [Pi.add_apply]
  rw [hf, hg]
  ring

lemma twoMultSymbol_smul (c : ℂ) (t : ℝ) (f : TwoParticleL2) :
    twoMultSymbol t (c • f) = c • twoMultSymbol t f := by
  apply Lp.ext
  filter_upwards [coe_twoMultSymbol t (c • f), coe_twoMultSymbol t f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (twoMultSymbol t f)]
      with xi hcf hf hsmul hout
  rw [hcf, hsmul, hout]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hf]
  ring

lemma twoFreeProp_add (t : ℝ) (f g : TwoParticleL2) :
    twoFreeProp t (f + g) = twoFreeProp t f + twoFreeProp t g := by
  unfold twoFreeProp
  rw [map_add, twoMultSymbol_add, map_add]

lemma twoFreeProp_smul (c : ℂ) (t : ℝ) (f : TwoParticleL2) :
    twoFreeProp t (c • f) = c • twoFreeProp t f := by
  unfold twoFreeProp
  rw [map_smul, twoMultSymbol_smul, map_smul]

lemma twoFreeProp_sub (t : ℝ) (f g : TwoParticleL2) :
    twoFreeProp t (f - g) = twoFreeProp t f - twoFreeProp t g := by
  rw [sub_eq_add_neg, twoFreeProp_add, ← neg_one_smul ℂ g,
    twoFreeProp_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

private lemma twoSchrodingerSymbol_mul (s t : ℝ) (xi : ℝ × ℝ) :
    twoSchrodingerSymbol t xi * twoSchrodingerSymbol s xi =
      twoSchrodingerSymbol (t + s) xi := by
  rw [twoSchrodingerSymbol, twoSchrodingerSymbol, twoSchrodingerSymbol,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma twoFreeProp_group (s t : ℝ) (f : TwoParticleL2) :
    twoFreeProp t (twoFreeProp s f) = twoFreeProp (t + s) f := by
  apply fourierL2Two.injective
  apply Lp.ext
  filter_upwards [fourier_twoFreeProp t (twoFreeProp s f),
    fourier_twoFreeProp s f, fourier_twoFreeProp (t + s) f]
      with xi hts hs hsum
  rw [hts, hs, hsum, ← mul_assoc, twoSchrodingerSymbol_mul]

lemma twoFreeProp_zero (f : TwoParticleL2) : twoFreeProp 0 f = f := by
  apply fourierL2Two.injective
  apply Lp.ext
  filter_upwards [fourier_twoFreeProp 0 f] with xi hxi
  rw [hxi]
  simp [twoSchrodingerSymbol]

/-- The two-particle free group as a linear isometric equivalence. -/
def twoFreePropLIE (t : ℝ) : TwoParticleL2 ≃ₗᵢ[ℂ] TwoParticleL2 where
  toFun := twoFreeProp t
  invFun := twoFreeProp (-t)
  map_add' := twoFreeProp_add t
  map_smul' := fun c f => twoFreeProp_smul c t f
  left_inv f := by
    rw [twoFreeProp_group]
    simpa using twoFreeProp_zero f
  right_inv f := by
    rw [twoFreeProp_group]
    simpa using twoFreeProp_zero f
  norm_map' := norm_twoFreeProp t

@[simp] lemma twoFreePropLIE_apply (t : ℝ) (f : TwoParticleL2) :
    twoFreePropLIE t f = twoFreeProp t f := rfl

@[simp] lemma twoFreePropLIE_symm_apply (t : ℝ) (f : TwoParticleL2) :
    (twoFreePropLIE t).symm f = twoFreeProp (-t) f := rfl

private lemma continuous_twoMultSymbol (g : TwoParticleL2) :
    Continuous (fun t => twoMultSymbol t g) := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let r : ℝ → (ℝ × ℝ) → ℂ := fun t xi =>
    (twoSchrodingerSymbol t xi - twoSchrodingerSymbol t0 xi) *
      (g : ℝ × ℝ → ℂ) xi
  have hraw (t : ℝ) :
      eLpNorm ((twoMultSymbol t g : ℝ × ℝ → ℂ) -
          (twoMultSymbol t0 g : ℝ × ℝ → ℂ)) 2 (volume.prod volume) =
        eLpNorm (r t) 2 (volume.prod volume) := by
    apply eLpNorm_congr_ae
    filter_upwards [coe_twoMultSymbol t g, coe_twoMultSymbol t0 g]
      with xi ht ht0
    simp only [Pi.sub_apply, ht, ht0]
    dsimp [r]
    ring
  simp_rw [hraw]
  have hmeas : ∀ t : ℝ,
      AEMeasurable (fun xi => ‖r t xi‖ₑ ^ (2 : ℝ)) (volume.prod volume) := by
    intro t
    apply AEMeasurable.pow_const
    apply AEStronglyMeasurable.enorm
    exact ((continuous_twoSchrodingerSymbol t).aestronglyMeasurable.sub
      (continuous_twoSchrodingerSymbol t0).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable g)
  have hbound : ∀ t : ℝ, ∀ᵐ xi : ℝ × ℝ ∂(volume.prod volume),
      ‖r t xi‖ₑ ^ (2 : ℝ) ≤
        4 * ‖(g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
    intro t
    filter_upwards with xi
    have hs : ‖twoSchrodingerSymbol t xi - twoSchrodingerSymbol t0 xi‖ ≤ 2 := by
      calc
        _ ≤ ‖twoSchrodingerSymbol t xi‖ + ‖twoSchrodingerSymbol t0 xi‖ :=
          norm_sub_le _ _
        _ = 2 := by
          rw [norm_twoSchrodingerSymbol, norm_twoSchrodingerSymbol]
          norm_num
    dsimp [r]
    rw [enorm_mul]
    have hse : ‖twoSchrodingerSymbol t xi - twoSchrodingerSymbol t0 xi‖ₑ ≤ 2 := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)
    calc
      (‖twoSchrodingerSymbol t xi - twoSchrodingerSymbol t0 xi‖ₑ *
          ‖(g : ℝ × ℝ → ℂ) xi‖ₑ) ^ (2 : ℝ) =
          ‖twoSchrodingerSymbol t xi - twoSchrodingerSymbol t0 xi‖ₑ ^ (2 : ℝ) *
            ‖(g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ (2 : ℝ≥0∞) ^ (2 : ℝ) *
          ‖(g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by gcongr
      _ = 4 * ‖(g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by norm_num
  have hfin : (∫⁻ xi : ℝ × ℝ,
      4 * ‖(g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) ∂(volume.prod volume)) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp g).2).ne
  have hpoint : ∀ xi : ℝ × ℝ,
      Tendsto (fun t => ‖r t xi‖ₑ ^ (2 : ℝ)) (𝓝 t0) (𝓝 0) := by
    intro xi
    have hr : Tendsto (fun t => r t xi) (𝓝 t0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => r t xi) t0 := by
        dsimp [r, twoSchrodingerSymbol]
        fun_prop
      simpa [r] using hc.tendsto
    convert
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
        hr.enorm using 1 <;>
      simp [Function.comp_def]
  have hint := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := volume.prod volume) (l := 𝓝 t0)
    (F := fun t xi => ‖r t xi‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
    (fun xi => 4 * ‖(g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ))
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound)
    hfin (Filter.Eventually.of_forall hpoint)
  simp only [lintegral_zero] at hint
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_ofNat, one_div]
  convert
    (ENNReal.continuous_rpow_const
      (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hint using 1 <;>
    simp [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]

theorem continuous_twoFreeProp (f : TwoParticleL2) :
    Continuous (fun t => twoFreeProp t f) := by
  exact fourierL2Two.symm.continuous.comp (continuous_twoMultSymbol (fourierL2Two f))

theorem continuous_twoFreeProp_joint :
    Continuous (fun p : ℝ × TwoParticleL2 => twoFreeProp p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hdata : Tendsto (fun q : ℝ × TwoParticleL2 => twoFreeProp q.1 (q.2 - p.2))
      (𝓝 p) (𝓝 0) := by
    have hsub : Continuous (fun q : ℝ × TwoParticleL2 => q.2 - p.2) :=
      continuous_snd.sub continuous_const
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht : Tendsto (fun q : ℝ × TwoParticleL2 => ‖q.2 - p.2‖)
        (𝓝 p) (𝓝 ‖p.2 - p.2‖) := hsub.norm.continuousAt
    simpa only [sub_zero, norm_twoFreeProp, sub_self, norm_zero] using ht
  have htime : Tendsto (fun q : ℝ × TwoParticleL2 => twoFreeProp q.1 p.2)
      (𝓝 p) (𝓝 (twoFreeProp p.1 p.2)) :=
    ((continuous_twoFreeProp p.2).comp continuous_fst).continuousAt
  change Tendsto (fun q : ℝ × TwoParticleL2 => twoFreeProp q.1 q.2)
    (𝓝 p) (𝓝 (twoFreeProp p.1 p.2))
  convert hdata.add htime using 1
  · funext q
    rw [← twoFreeProp_add]
    congr 1
    abel
  · simp

lemma pairToEuclidean_inner (z xi : ℝ × ℝ) :
    inner ℝ (pairToEuclidean z) (pairToEuclidean xi) =
      z.1 * xi.1 + z.2 * xi.2 := by
  rw [PiLp.inner_apply]
  simp [pairToEuclidean, Fin.sum_univ_two]
  ring

lemma inner_pairToEuclidean (z : E2) (xi : ℝ × ℝ) :
    inner ℝ z (pairToEuclidean xi) =
      (euclideanToPair z).1 * xi.1 + (euclideanToPair z).2 * xi.2 := by
  rw [show z = pairToEuclidean (euclideanToPair z) by simp]
  exact pairToEuclidean_inner (euclideanToPair z) xi

/-- Pair-coordinate formula for the two-dimensional Schwartz Fourier transform. -/
lemma pairSchwartzFourier_apply_eq_integral (f : 𝓢(ℝ × ℝ, ℂ))
    (xi : ℝ × ℝ) :
    pairSchwartzFourier f xi =
      ∫ z : ℝ × ℝ,
        Complex.exp (((-2 * Real.pi * (z.1 * xi.1 + z.2 * xi.2) : ℝ) : ℂ) *
          Complex.I) * f z ∂(volume.prod volume) := by
  rw [pairSchwartzFourier]
  change (𝓕 (pairSchwartzToEuclidean f)) (pairToEuclidean xi) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [smul_eq_mul]
  have hchange := euclideanToPair_measurePreserving.integral_comp
    euclideanPairCLE.toHomeomorph.measurableEmbedding
    (fun z : ℝ × ℝ =>
      Complex.exp (((-2 * Real.pi * (z.1 * xi.1 + z.2 * xi.2) : ℝ) : ℂ) *
        Complex.I) * f z)
  rw [← hchange]
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_pairToEuclidean]
  rfl

def compactSchwartzProduct (f g : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  (show HasCompactSupport (fun z : ℝ × ℝ => f z.1 * g z.2) by
    refine HasCompactSupport.intro
      (K := tsupport (f : ℝ → ℂ) ×ˢ tsupport (g : ℝ → ℂ))
      (hf.isCompact.prod hg.isCompact) ?_
    intro z hz
    simp only [Set.mem_prod, not_and_or] at hz
    rcases hz with hzf | hzg
    · have : f z.1 = 0 := by
        by_contra hn
        exact hzf (subset_tsupport _ hn)
      rw [this, zero_mul]
    · have : g z.2 = 0 := by
        by_contra hn
        exact hzg (subset_tsupport _ hn)
      rw [this, mul_zero]).toSchwartzMap (by fun_prop)

@[simp] lemma compactSchwartzProduct_apply (f g : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) (z : ℝ × ℝ) :
    compactSchwartzProduct f g hf hg z = f z.1 * g z.2 := rfl

lemma pairSchwartzFourier_compactProduct_apply (f g : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) (xi : ℝ × ℝ) :
    pairSchwartzFourier (compactSchwartzProduct f g hf hg) xi =
      (𝓕 f) xi.1 * (𝓕 g) xi.2 := by
  rw [pairSchwartzFourier_apply_eq_integral]
  let A : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * (x * xi.1) : ℝ) : ℂ) * Complex.I) * f x
  let B : ℝ → ℂ := fun y =>
    Complex.exp (((-2 * Real.pi * (y * xi.2) : ℝ) : ℂ) * Complex.I) * g y
  have hA : Integrable A volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [A]; fun_prop
    · exact hf.mul_left
  have hB : Integrable B volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [B]; fun_prop
    · exact hg.mul_left
  rw [show (fun z : ℝ × ℝ =>
      Complex.exp (((-2 * Real.pi *
        (z.1 * xi.1 + z.2 * xi.2) : ℝ) : ℂ) * Complex.I) *
          compactSchwartzProduct f g hf hg z) =
      fun z => A z.1 * B z.2 by
    funext z
    simp only [compactSchwartzProduct_apply, A, B]
    rw [show Complex.exp (((-2 * Real.pi *
        (z.1 * xi.1 + z.2 * xi.2) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-2 * Real.pi * (z.1 * xi.1) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-2 * Real.pi * (z.2 * xi.2) : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring]
    ring]
  rw [integral_prod_mul A B]
  change (∫ x, Complex.exp (((-2 * Real.pi * (x * xi.1) : ℝ) : ℂ) *
      Complex.I) * f x) *
    (∫ y, Complex.exp (((-2 * Real.pi * (y * xi.2) : ℝ) : ℂ) *
      Complex.I) * g y) = _
  have hfFourier : (𝓕 f) xi.1 = ∫ x,
      Complex.exp (((-2 * Real.pi * (x * xi.1) : ℝ) : ℂ) * Complex.I) * f x := by
    change (𝓕 (f : ℝ → ℂ)) xi.1 = _
    rw [Real.fourier_eq']
    simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
    congr 1
    funext x
    congr 1
    push_cast
    ring_nf
  have hgFourier : (𝓕 g) xi.2 = ∫ y,
      Complex.exp (((-2 * Real.pi * (y * xi.2) : ℝ) : ℂ) * Complex.I) * g y := by
    change (𝓕 (g : ℝ → ℂ)) xi.2 = _
    rw [Real.fourier_eq']
    simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
    congr 1
    funext y
    congr 1
    push_cast
    ring_nf
  rw [hfFourier, hgFourier]

lemma compactSchwartzProduct_toLp (f g : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    (compactSchwartzProduct f g hf hg).toLp 2 (volume.prod volume) =
      tensorProductL2 (f.toLp 2 volume) (g.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(compactSchwartzProduct f g hf hg).coeFn_toLp 2
      (volume.prod volume), coe_tensorProductL2 (f.toLp 2 volume) (g.toLp 2 volume),
    Measure.quasiMeasurePreserving_fst.ae (f.coeFn_toLp 2 volume),
    Measure.quasiMeasurePreserving_snd.ae (g.coeFn_toLp 2 volume)]
      with z hout htensor hflp hglp
  rw [hout, htensor, compactSchwartzProduct_apply, hflp, hglp]

lemma fourierL2Two_tensor_compactSchwartz (f g : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    fourierL2Two (tensorProductL2 (f.toLp 2 volume) (g.toLp 2 volume)) =
      tensorProductL2 (fourierL2 (f.toLp 2 volume))
        (fourierL2 (g.toLp 2 volume)) := by
  rw [← compactSchwartzProduct_toLp f g hf hg, fourierL2Two_toLp]
  have hff : (fourierL2 (f.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun xi => (𝓕 f) xi := by
    have heq : fourierL2 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume := by
      exact SchwartzMap.toLp_fourier_eq f
    rw [heq]
    exact (𝓕 f).coeFn_toLp 2 volume
  have hgf : (fourierL2 (g.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun xi => (𝓕 g) xi := by
    have heq : fourierL2 (g.toLp 2 volume) = (𝓕 g).toLp 2 volume := by
      exact SchwartzMap.toLp_fourier_eq g
    rw [heq]
    exact (𝓕 g).coeFn_toLp 2 volume
  apply Lp.ext
  filter_upwards [(pairSchwartzFourier
      (compactSchwartzProduct f g hf hg)).coeFn_toLp 2 (volume.prod volume),
    coe_tensorProductL2 (fourierL2 (f.toLp 2 volume))
      (fourierL2 (g.toLp 2 volume)),
    Measure.quasiMeasurePreserving_fst.ae hff,
    Measure.quasiMeasurePreserving_snd.ae hgf]
      with xi hout htensor hff' hgf'
  rw [hout, htensor, pairSchwartzFourier_compactProduct_apply,
    hff', hgf']

lemma exists_compactSchwartz_dist_lt (f : L2) {eps : ℝ} (heps : 0 < eps) :
    ∃ q : 𝓢(ℝ, ℂ), HasCompactSupport (q : ℝ → ℂ) ∧
      dist (q.toLp 2 volume) f < eps := by
  obtain ⟨g, hgc, hgd, hbound⟩ :=
    MemLp.exist_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp f)
      (show 0 < eps / 2 by positivity)
  let q : 𝓢(ℝ, ℂ) := hgc.toSchwartzMap hgd
  refine ⟨q, hgc, ?_⟩
  rw [dist_comm, Lp.dist_def]
  have hae : ((f : ℝ → ℂ) - (q.toLp 2 volume : ℝ → ℂ)) =ᵐ[volume]
      (f : ℝ → ℂ) - g := by
    filter_upwards [q.coeFn_toLp 2 volume] with x hx
    simp only [Pi.sub_apply]
    rw [hx]
    rfl
  rw [eLpNorm_congr_ae hae]
  calc
    (eLpNorm ((f : ℝ → ℂ) - g) 2 volume).toReal ≤
        (ENNReal.ofReal (eps / 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = eps / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < eps := by linarith

set_option maxHeartbeats 1000000 in
/-- The two-dimensional Fourier transform respects elementary `L²` tensors. -/
theorem fourierL2Two_tensor (f g : L2) :
    fourierL2Two (tensorProductL2 f g) =
      tensorProductL2 (fourierL2 f) (fourierL2 g) := by
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have heps (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have hfex (n : ℕ) : ∃ q : 𝓢(ℝ, ℂ),
      HasCompactSupport (q : ℝ → ℂ) ∧ dist (q.toLp 2 volume) f < eps n :=
    exists_compactSchwartz_dist_lt f (heps n)
  have hgex (n : ℕ) : ∃ q : 𝓢(ℝ, ℂ),
      HasCompactSupport (q : ℝ → ℂ) ∧ dist (q.toLp 2 volume) g < eps n :=
    exists_compactSchwartz_dist_lt g (heps n)
  let fn : ℕ → 𝓢(ℝ, ℂ) := fun n => Classical.choose (hfex n)
  let gn : ℕ → 𝓢(ℝ, ℂ) := fun n => Classical.choose (hgex n)
  have hfc (n : ℕ) : HasCompactSupport (fn n : ℝ → ℂ) :=
    (Classical.choose_spec (hfex n)).1
  have hgc (n : ℕ) : HasCompactSupport (gn n : ℝ → ℂ) :=
    (Classical.choose_spec (hgex n)).1
  have hfd (n : ℕ) : dist ((fn n).toLp 2 volume) f < eps n :=
    (Classical.choose_spec (hfex n)).2
  have hgd (n : ℕ) : dist ((gn n).toLp 2 volume) g < eps n :=
    (Classical.choose_spec (hgex n)).2
  have hepsto : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hfto : Tendsto (fun n => (fn n).toLp 2 volume) atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => (hfd n).le) hepsto
  have hgto : Tendsto (fun n => (gn n).toLp 2 volume) atTop (𝓝 g) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => (hgd n).le) hepsto
  have hleft : Tendsto (fun n => fourierL2Two
      (tensorProductL2 ((fn n).toLp 2 volume) ((gn n).toLp 2 volume)))
      atTop (𝓝 (fourierL2Two (tensorProductL2 f g))) := by
    exact fourierL2Two.continuous.continuousAt.tendsto.comp
      (tensorProductCLM.continuous₂.continuousAt.tendsto.comp
        (hfto.prodMk_nhds hgto))
  have hright : Tendsto (fun n => tensorProductL2
      (fourierL2 ((fn n).toLp 2 volume))
      (fourierL2 ((gn n).toLp 2 volume))) atTop
      (𝓝 (tensorProductL2 (fourierL2 f) (fourierL2 g))) := by
    exact tensorProductCLM.continuous₂.continuousAt.tendsto.comp
      ((fourierL2.continuous.continuousAt.tendsto.comp hfto).prodMk_nhds
        (fourierL2.continuous.continuousAt.tendsto.comp hgto))
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with n
  exact (fourierL2Two_tensor_compactSchwartz
    (fn n) (gn n) (hfc n) (hgc n)).symm

/-- The two-particle free group is the tensor product of the one-particle
free groups on elementary tensors. -/
theorem twoFreeProp_tensor (t : ℝ) (f g : L2) :
    twoFreeProp t (tensorProductL2 f g) =
      tensorProductL2 (freeProp t f) (freeProp t g) := by
  have hbase : ∀ᵐ xi : ℝ × ℝ,
      (fourierL2Two (tensorProductL2 f g) : ℝ × ℝ → ℂ) xi =
        (fourierL2 f : ℝ → ℂ) xi.1 * (fourierL2 g : ℝ → ℂ) xi.2 := by
    rw [fourierL2Two_tensor]
    exact coe_tensorProductL2 (fourierL2 f) (fourierL2 g)
  apply fourierL2Two.injective
  rw [fourierL2Two_tensor]
  apply Lp.ext
  filter_upwards [fourier_twoFreeProp t (tensorProductL2 f g),
    coe_tensorProductL2 (fourierL2 (freeProp t f))
      (fourierL2 (freeProp t g)),
    Measure.quasiMeasurePreserving_fst.ae (fourier_freeProp t f),
    Measure.quasiMeasurePreserving_snd.ae (fourier_freeProp t g),
    hbase]
      with xi hleft hright hff hfg htensor
  rw [hleft, hright, hff, hfg, htensor]
  have hsymbol : twoSchrodingerSymbol t xi =
      schrodingerSymbol t xi.1 * schrodingerSymbol t xi.2 := by
    unfold twoSchrodingerSymbol schrodingerSymbol
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsymbol]
  ring

/-! ## The generator on compactly supported smooth spatial tests -/

/-- The spatial Laplacian on the pair model. -/
def pairLaplacian (f : SchwartzMap (ℝ × ℝ) ℂ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  pairPartial0 (pairPartial0 f) + pairPartial1 (pairPartial1 f)

private theorem pairSchwartzFourier_pairPartial0
    (f : SchwartzMap (ℝ × ℝ) ℂ) :
    pairSchwartzFourier (pairPartial0 f) =
      -pairFrequencyDeriv0 (pairSchwartzFourier f) := by
  unfold pairSchwartzFourier pairPartial0 pairFrequencyDeriv0
  rw [pairSchwartzToEuclidean_toPair]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  rw [pairSchwartzToEuclidean_toPair]
  ext x
  simp only [euclideanSchwartzToPair,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smul_apply, neg_apply, smul_eq_mul]
  ring

private theorem pairSchwartzFourier_pairPartial1
    (f : SchwartzMap (ℝ × ℝ) ℂ) :
    pairSchwartzFourier (pairPartial1 f) =
      -pairFrequencyDeriv1 (pairSchwartzFourier f) := by
  unfold pairSchwartzFourier pairPartial1 pairFrequencyDeriv1
  rw [pairSchwartzToEuclidean_toPair]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  rw [pairSchwartzToEuclidean_toPair]
  ext x
  simp only [euclideanSchwartzToPair,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smul_apply, neg_apply, smul_eq_mul]
  ring

private theorem pairSchwartzFourier_laplacian_apply
    (f : SchwartzMap (ℝ × ℝ) ℂ) (xi : ℝ × ℝ) :
    pairSchwartzFourier (pairLaplacian f) xi =
      ((-(4 * Real.pi ^ 2 * (xi.1 ^ 2 + xi.2 ^ 2)) : ℝ) : ℂ) *
        pairSchwartzFourier f xi := by
  unfold pairLaplacian
  rw [show pairSchwartzFourier
      (pairPartial0 (pairPartial0 f) + pairPartial1 (pairPartial1 f)) =
      pairSchwartzFourier (pairPartial0 (pairPartial0 f)) +
        pairSchwartzFourier (pairPartial1 (pairPartial1 f)) by
    unfold pairSchwartzFourier
    simp]
  rw [pairSchwartzFourier_pairPartial0, pairSchwartzFourier_pairPartial0,
    pairSchwartzFourier_pairPartial1, pairSchwartzFourier_pairPartial1]
  simp only [add_apply, neg_apply]
  rw [pairFrequencyDeriv0_apply]
  simp only [neg_apply]
  rw [pairFrequencyDeriv0_apply, pairFrequencyDeriv1_apply]
  simp only [neg_apply]
  rw [pairFrequencyDeriv1_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

def twoSchrodingerFrequency (xi : ℝ × ℝ) : ℝ :=
  4 * Real.pi ^ 2 * (xi.1 ^ 2 + xi.2 ^ 2)

def twoSchrodingerGenerator (xi : ℝ × ℝ) : ℂ :=
  ((-twoSchrodingerFrequency xi : ℝ) : ℂ) * Complex.I

private lemma twoSchrodingerFrequency_nonneg (xi : ℝ × ℝ) :
    0 ≤ twoSchrodingerFrequency xi := by
  dsimp [twoSchrodingerFrequency]
  positivity

private lemma norm_twoSchrodingerGenerator (xi : ℝ × ℝ) :
    ‖twoSchrodingerGenerator xi‖ = twoSchrodingerFrequency xi := by
  rw [twoSchrodingerGenerator, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (twoSchrodingerFrequency_nonneg xi)]

private lemma twoSchrodingerSymbol_eq_generator_exp (t : ℝ) (xi : ℝ × ℝ) :
    twoSchrodingerSymbol t xi =
      Complex.exp ((t : ℂ) * twoSchrodingerGenerator xi) := by
  rw [twoSchrodingerSymbol, twoSchrodingerGenerator, twoSchrodingerFrequency]
  congr 1
  push_cast
  ring

private lemma hasDerivAt_twoSchrodingerSymbol (t : ℝ) (xi : ℝ × ℝ) :
    HasDerivAt (fun s => twoSchrodingerSymbol s xi)
      (twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi) t := by
  simp_rw [twoSchrodingerSymbol_eq_generator_exp]
  have hlin : HasDerivAt
      (fun s : ℝ => (s : ℂ) * twoSchrodingerGenerator xi)
      (twoSchrodingerGenerator xi) t := by
    simpa using Complex.ofRealCLM.hasDerivAt.mul_const
      (twoSchrodingerGenerator xi)
  simpa [mul_comm] using hlin.cexp

private lemma norm_twoSchrodingerSymbol_slope_le
    (t : ℝ) (xi : ℝ × ℝ) (h : ℝ) (hh : h ≠ 0) :
    ‖((h : ℂ)⁻¹) *
        (twoSchrodingerSymbol (t + h) xi - twoSchrodingerSymbol t xi)‖ ≤
      twoSchrodingerFrequency xi := by
  have hgroup : twoSchrodingerSymbol (t + h) xi =
      twoSchrodingerSymbol t xi * twoSchrodingerSymbol h xi := by
    rw [mul_comm, twoSchrodingerSymbol_mul t h xi, add_comm]
  have hosc : twoSchrodingerSymbol h xi =
      Complex.exp (Complex.I *
        ((-twoSchrodingerFrequency xi * h : ℝ) : ℂ)) := by
    rw [twoSchrodingerSymbol_eq_generator_exp, twoSchrodingerGenerator]
    congr 1
    push_cast
    ring
  rw [hgroup]
  have hfactor : twoSchrodingerSymbol t xi * twoSchrodingerSymbol h xi -
      twoSchrodingerSymbol t xi =
        twoSchrodingerSymbol t xi * (twoSchrodingerSymbol h xi - 1) := by
    ring
  rw [hfactor, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, norm_twoSchrodingerSymbol, one_mul, hosc]
  have htrig := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := -twoSchrodingerFrequency xi * h)
  calc
    |h|⁻¹ * ‖Complex.exp (Complex.I *
          ((-twoSchrodingerFrequency xi * h : ℝ) : ℂ)) - 1‖ ≤
        |h|⁻¹ * ‖-twoSchrodingerFrequency xi * h‖ :=
      mul_le_mul_of_nonneg_left htrig (inv_nonneg.mpr (abs_nonneg h))
    _ = twoSchrodingerFrequency xi := by
      rw [Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg (twoSchrodingerFrequency_nonneg xi)]
      field_simp [abs_ne_zero.mpr hh]

lemma continuous_twoSchrodingerGenerator :
    Continuous twoSchrodingerGenerator := by
  unfold twoSchrodingerGenerator twoSchrodingerFrequency
  fun_prop

lemma twoGenerator_symbol_mul_memLp (g : TwoParticleL2)
    (hgen : MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi * (g : ℝ × ℝ → ℂ) xi) 2
      (volume.prod volume)) (t : ℝ) :
    MemLp (fun xi : ℝ × ℝ => twoSchrodingerGenerator xi *
      twoSchrodingerSymbol t xi * (g : ℝ × ℝ → ℂ) xi) 2
      (volume.prod volume) := by
  refine ⟨((continuous_twoSchrodingerGenerator.aestronglyMeasurable.mul
    (continuous_twoSchrodingerSymbol t).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g)), ?_⟩
  have heq : eLpNorm (fun xi : ℝ × ℝ =>
        twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi *
          (g : ℝ × ℝ → ℂ) xi) 2 (volume.prod volume) =
      eLpNorm (fun xi : ℝ × ℝ =>
        twoSchrodingerGenerator xi * (g : ℝ × ℝ → ℂ) xi) 2
        (volume.prod volume) := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with xi
    simp only [norm_mul, norm_twoSchrodingerSymbol, mul_one]
  rw [heq]
  exact hgen.2

lemma hasDerivAt_twoMultSymbol (g : TwoParticleL2)
    (hgen : MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi * (g : ℝ × ℝ → ℂ) xi) 2
      (volume.prod volume)) (t : ℝ) :
    HasDerivAt (fun s => twoMultSymbol s g)
      ((twoGenerator_symbol_mul_memLp g hgen t).toLp
        (fun xi : ℝ × ℝ => twoSchrodingerGenerator xi *
          twoSchrodingerSymbol t xi * (g : ℝ × ℝ → ℂ) xi)) t := by
  let dg : ℝ × ℝ → ℂ := fun xi =>
    twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi *
      (g : ℝ × ℝ → ℂ) xi
  have hdg : MemLp dg 2 (volume.prod volume) :=
    twoGenerator_symbol_mul_memLp g hgen t
  change HasDerivAt (fun s => twoMultSymbol s g) (hdg.toLp dg) t
  rw [hasDerivAt_iff_tendsto_slope_zero,
    Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let r : ℝ → (ℝ × ℝ) → ℂ := fun h xi =>
    ((h : ℂ)⁻¹) *
        (twoSchrodingerSymbol (t + h) xi - twoSchrodingerSymbol t xi) *
        (g : ℝ × ℝ → ℂ) xi - dg xi
  have hraw (h : ℝ) :
      eLpNorm
          ((↑(h⁻¹ • (twoMultSymbol (t + h) g - twoMultSymbol t g)) :
              ℝ × ℝ → ℂ) -
            (↑(hdg.toLp dg) : ℝ × ℝ → ℂ)) 2
              (volume.prod volume) =
        eLpNorm (r h) 2 (volume.prod volume) := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (twoMultSymbol (t + h) g) (twoMultSymbol t g),
      Lp.coeFn_smul h⁻¹ (twoMultSymbol (t + h) g - twoMultSymbol t g),
      coe_twoMultSymbol (t + h) g, coe_twoMultSymbol t g, hdg.coeFn_toLp]
        with xi hsub hsmul hth ht0 hd
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
  have hmeas : ∀ h : ℝ,
      AEMeasurable (fun xi => ‖r h xi‖ₑ ^ (2 : ℝ))
        (volume.prod volume) := by
    intro h
    apply AEMeasurable.pow_const
    apply AEStronglyMeasurable.enorm
    have hs : AEStronglyMeasurable
        (fun xi : ℝ × ℝ => (h : ℂ)⁻¹ *
          (twoSchrodingerSymbol (t + h) xi - twoSchrodingerSymbol t xi))
        (volume.prod volume) :=
      ((continuous_twoSchrodingerSymbol (t + h)).aestronglyMeasurable.sub
        (continuous_twoSchrodingerSymbol t).aestronglyMeasurable).const_mul
          ((h : ℂ)⁻¹)
    exact (hs.mul (Lp.aestronglyMeasurable g)).sub hdg.1
  have hbound : ∀ᶠ h : ℝ in nhdsWithin 0 {0}ᶜ,
      ∀ᵐ xi : ℝ × ℝ ∂(volume.prod volume),
        ‖r h xi‖ₑ ^ (2 : ℝ) ≤
          4 * ‖twoSchrodingerGenerator xi *
            (g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    filter_upwards with xi
    have hslope := norm_twoSchrodingerSymbol_slope_le t xi h hh0
    have hrnorm : ‖r h xi‖ ≤
        2 * ‖twoSchrodingerGenerator xi *
          (g : ℝ × ℝ → ℂ) xi‖ := by
      dsimp [r, dg]
      calc
        ‖((h : ℂ)⁻¹ *
              (twoSchrodingerSymbol (t + h) xi -
                twoSchrodingerSymbol t xi) *
              (g : ℝ × ℝ → ℂ) xi -
            twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi *
              (g : ℝ × ℝ → ℂ) xi)‖ ≤
            ‖((h : ℂ)⁻¹ *
              (twoSchrodingerSymbol (t + h) xi -
                twoSchrodingerSymbol t xi) *
              (g : ℝ × ℝ → ℂ) xi)‖ +
            ‖twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi *
              (g : ℝ × ℝ → ℂ) xi‖ := norm_sub_le _ _
        _ ≤ twoSchrodingerFrequency xi *
              ‖(g : ℝ × ℝ → ℂ) xi‖ +
            twoSchrodingerFrequency xi *
              ‖(g : ℝ × ℝ → ℂ) xi‖ := by
          gcongr
          · simpa [norm_mul] using
              mul_le_mul_of_nonneg_right hslope
                (norm_nonneg ((g : ℝ × ℝ → ℂ) xi))
          · rw [norm_mul, norm_mul, norm_twoSchrodingerGenerator,
              norm_twoSchrodingerSymbol, mul_one]
        _ = 2 * ‖twoSchrodingerGenerator xi *
              (g : ℝ × ℝ → ℂ) xi‖ := by
          rw [norm_mul, norm_twoSchrodingerGenerator]
          ring
    have hre : ‖r h xi‖ₑ ≤
        2 * ‖twoSchrodingerGenerator xi *
          (g : ℝ × ℝ → ℂ) xi‖ₑ := by
      simpa [← ofReal_norm,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using
          ENNReal.ofReal_le_ofReal hrnorm
    calc
      ‖r h xi‖ₑ ^ (2 : ℝ) ≤
          (2 * ‖twoSchrodingerGenerator xi *
            (g : ℝ × ℝ → ℂ) xi‖ₑ) ^ (2 : ℝ) := by gcongr
      _ = 4 * ‖twoSchrodingerGenerator xi *
            (g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  have hfin : (∫⁻ xi : ℝ × ℝ,
      4 * ‖twoSchrodingerGenerator xi *
        (g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ)
        ∂(volume.prod volume)) ≠ ⊤ := by
    rw [lintegral_const_mul' 4 _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hgen.2).ne
  have hpoint : ∀ xi : ℝ × ℝ,
      Tendsto (fun h => ‖r h xi‖ₑ ^ (2 : ℝ))
        (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
    intro xi
    have hs := (hasDerivAt_twoSchrodingerSymbol t xi).tendsto_slope_zero
    have hr : Tendsto (fun h => r h xi) (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
      have hm := hs.mul_const ((g : ℝ × ℝ → ℂ) xi)
      have hz := hm.sub_const (dg xi)
      convert hz using 1 <;> simp [r, dg, mul_assoc]
    convert
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
        hr.enorm using 1 <;>
      simp [Function.comp_def]
  have hint := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := volume.prod volume) (l := nhdsWithin 0 {0}ᶜ)
    (F := fun h xi => ‖r h xi‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
    (fun xi => 4 * ‖twoSchrodingerGenerator xi *
      (g : ℝ × ℝ → ℂ) xi‖ₑ ^ (2 : ℝ))
    (Filter.Eventually.of_forall hmeas) hbound hfin
    (Filter.Eventually.of_forall hpoint)
  simp only [lintegral_zero] at hint
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_ofNat, one_div]
  convert
    (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp
      hint using 1 <;>
    simp [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]

private lemma coe_fourierL2Two_schwartz
    (q : SchwartzMap (ℝ × ℝ) ℂ) :
    (fourierL2Two (q.toLp 2 (volume.prod volume)) : ℝ × ℝ → ℂ)
      =ᵐ[volume.prod volume] fun xi => pairSchwartzFourier q xi := by
  rw [fourierL2Two_toLp]
  exact (pairSchwartzFourier q).coeFn_toLp 2 (volume.prod volume)

private lemma pairSchwartz_twoGenerator_memLp
    (q : SchwartzMap (ℝ × ℝ) ℂ) :
    MemLp (fun xi : ℝ × ℝ => twoSchrodingerGenerator xi *
      (fourierL2Two (q.toLp 2 (volume.prod volume)) : ℝ × ℝ → ℂ) xi)
      2 (volume.prod volume) := by
  let w := pairFrequencyConjugatedAdjoint 0 (pairSchwartzFourier q)
  have hw : MemLp (w : ℝ × ℝ → ℂ) 2 (volume.prod volume) :=
    w.memLp 2 (volume.prod volume)
  have hraw : MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi * pairSchwartzFourier q xi) 2
      (volume.prod volume) := by
    refine hw.congr_norm
      (continuous_twoSchrodingerGenerator.aestronglyMeasurable.mul
        (pairSchwartzFourier q).continuous.aestronglyMeasurable) ?_
    filter_upwards with xi
    rw [pairFrequencyConjugatedAdjoint_apply]
    dsimp [w, twoSchrodingerGenerator, twoSchrodingerFrequency]
    norm_num
  refine hraw.congr_norm
    (continuous_twoSchrodingerGenerator.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable
        (fourierL2Two (q.toLp 2 (volume.prod volume))))) ?_
  filter_upwards [coe_fourierL2Two_schwartz q] with xi hxi
  rw [hxi]

/-- The two-particle free group differentiates on smooth compactly supported
spatial tests with generator `i(∂₁²+∂₂²)`. -/
theorem twoFreeProp_schwartz_derivative
    (q : SchwartzMap (ℝ × ℝ) ℂ) (t : ℝ) :
    HasDerivAt
      (fun s => twoFreeProp s (q.toLp 2 (volume.prod volume)))
      (Complex.I • twoFreeProp t
        ((pairLaplacian q).toLp 2 (volume.prod volume))) t := by
  let g : TwoParticleL2 :=
    fourierL2Two (q.toLp 2 (volume.prod volume))
  let dq : ℝ × ℝ → ℂ := fun xi =>
    twoSchrodingerGenerator xi * twoSchrodingerSymbol t xi *
      (g : ℝ × ℝ → ℂ) xi
  have hgen : MemLp (fun xi : ℝ × ℝ =>
      twoSchrodingerGenerator xi * (g : ℝ × ℝ → ℂ) xi) 2
      (volume.prod volume) := pairSchwartz_twoGenerator_memLp q
  have hdq : MemLp dq 2 (volume.prod volume) :=
    twoGenerator_symbol_mul_memLp g hgen t
  have hm : HasDerivAt (fun s => twoMultSymbol s g) (hdq.toLp dq) t := by
    simpa [dq] using hasDerivAt_twoMultSymbol g hgen t
  let U : TwoParticleL2 ≃L[ℂ] TwoParticleL2 :=
    fourierL2Two.symm.toContinuousLinearEquiv
  let UR : TwoParticleL2 →L[ℝ] TwoParticleL2 :=
    (U.restrictScalars ℝ).toContinuousLinearMap
  have hcomp := UR.hasFDerivAt.comp_hasDerivAt t hm
  have hfree : HasDerivAt
      (fun s => twoFreeProp s (q.toLp 2 (volume.prod volume)))
      (fourierL2Two.symm (hdq.toLp dq)) t := by
    simpa [twoFreeProp, g, U, UR, Function.comp_def] using hcomp
  have htarget : fourierL2Two.symm (hdq.toLp dq) =
      Complex.I • twoFreeProp t
        ((pairLaplacian q).toLp 2 (volume.prod volume)) := by
    apply fourierL2Two.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul]
    apply Lp.ext
    filter_upwards [hdq.coeFn_toLp,
      Lp.coeFn_smul Complex.I
        (fourierL2Two
          (twoFreeProp t ((pairLaplacian q).toLp 2 (volume.prod volume)))),
      fourier_twoFreeProp t
        ((pairLaplacian q).toLp 2 (volume.prod volume)),
      coe_fourierL2Two_schwartz (pairLaplacian q),
      coe_fourierL2Two_schwartz q]
        with xi hd hsmul hfree' hlap hq
    rw [hd, hsmul]
    simp only [Pi.smul_apply]
    rw [hfree', hlap]
    dsimp [dq]
    rw [hq, pairSchwartzFourier_laplacian_apply]
    unfold twoSchrodingerGenerator twoSchrodingerFrequency
    push_cast
    ring
  rw [htarget] at hfree
  exact hfree

end CubicNLSPhaseRetrieval
