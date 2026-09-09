import Lean_Code.CarlemanSourceCurve
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-! A Plancherel transform on the pair model of two-dimensional space. -/

open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The continuous linear coordinate equivalence underlying the measurable
pair model.  It is kept separate from the measure equivalence because the
Schwartz-space API is phrased using continuous linear equivalences. -/
def euclideanPairCLE : E2 ≃L[ℝ] (ℝ × ℝ) :=
  ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toContinuousLinearEquiv).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv)

def euclideanToPair (x : E2) : ℝ × ℝ :=
  MeasurableEquiv.finTwoArrow (WithLp.ofLp x)

theorem euclideanToPair_measurePreserving :
    MeasurePreserving euclideanToPair
      (volume : Measure E2) (volume.prod volume : Measure (ℝ × ℝ)) := by
  have h1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 2 → ℝ))
      (volume : Measure E2) (volume : Measure (Fin 2 → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin 2)
  have h2 : MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ)
      (volume : Measure (Fin 2 → ℝ)) (volume.prod volume : Measure (ℝ × ℝ)) :=
    volume_preserving_finTwoArrow ℝ
  change MeasurePreserving
    (fun x : E2 => MeasurableEquiv.finTwoArrow (WithLp.ofLp x)) _ _
  exact h2.comp h1

def pairToEuclidean (x : ℝ × ℝ) : E2 :=
  WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm x)

@[simp] theorem euclideanPairCLE_apply (x : E2) :
    euclideanPairCLE x = euclideanToPair x := rfl

@[simp] theorem euclideanPairCLE_symm_apply (x : ℝ × ℝ) :
    euclideanPairCLE.symm x = pairToEuclidean x := rfl

theorem pairToEuclidean_measurePreserving :
    MeasurePreserving pairToEuclidean
      (volume.prod volume : Measure (ℝ × ℝ)) (volume : Measure E2) := by
  have h1 : MeasurePreserving (MeasurableEquiv.finTwoArrow.symm : ℝ × ℝ → Fin 2 → ℝ)
      (volume.prod volume : Measure (ℝ × ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  have h2 : MeasurePreserving (@WithLp.toLp 2 (Fin 2 → ℝ))
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure E2) :=
    PiLp.volume_preserving_toLp (Fin 2)
  change MeasurePreserving
    (fun x : ℝ × ℝ => WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm x)) _ _
  exact h2.comp h1

abbrev EuclideanL2Two := Lp ℂ 2 (volume : Measure E2)

def pairToEuclideanL2 (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    EuclideanL2Two :=
  Lp.compMeasurePreserving euclideanToPair euclideanToPair_measurePreserving f

def euclideanToPairL2 (f : EuclideanL2Two) :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) :=
  Lp.compMeasurePreserving pairToEuclidean pairToEuclidean_measurePreserving f

@[simp] private lemma pairToEuclidean_toPair (z : ℝ × ℝ) :
    euclideanToPair (pairToEuclidean z) = z := by
  simp [euclideanToPair, pairToEuclidean]

@[simp] private lemma euclideanToPair_toEuclidean (z : E2) :
    pairToEuclidean (euclideanToPair z) = z := by
  simp [euclideanToPair, pairToEuclidean]
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> rfl

private lemma euclideanToPairL2_pairToEuclideanL2
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    euclideanToPairL2 (pairToEuclideanL2 f) = f := by
  unfold euclideanToPairL2 pairToEuclideanL2
  rw [← Lp.compMeasurePreserving_comp_apply f
    euclideanToPair_measurePreserving pairToEuclidean_measurePreserving]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (euclideanToPair_measurePreserving.comp pairToEuclidean_measurePreserving)]
    with z hz
  rw [hz]
  simp only [Function.comp_apply, pairToEuclidean_toPair]

private lemma pairToEuclideanL2_euclideanToPairL2 (f : EuclideanL2Two) :
    pairToEuclideanL2 (euclideanToPairL2 f) = f := by
  unfold euclideanToPairL2 pairToEuclideanL2
  rw [← Lp.compMeasurePreserving_comp_apply f
    pairToEuclidean_measurePreserving euclideanToPair_measurePreserving]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (pairToEuclidean_measurePreserving.comp euclideanToPair_measurePreserving)]
    with z hz
  rw [hz]
  simp only [Function.comp_apply, euclideanToPair_toEuclidean]

def pairEuclideanL2Equiv :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) ≃ₗᵢ[ℂ] EuclideanL2Two where
  toFun := pairToEuclideanL2
  invFun := euclideanToPairL2
  left_inv := euclideanToPairL2_pairToEuclideanL2
  right_inv := pairToEuclideanL2_euclideanToPairL2
  map_add' := (Lp.compMeasurePreservingₗᵢ ℂ euclideanToPair
    euclideanToPair_measurePreserving).map_add
  map_smul' := (Lp.compMeasurePreservingₗᵢ ℂ euclideanToPair
    euclideanToPair_measurePreserving).map_smul
  norm_map' := fun f => Lp.norm_compMeasurePreserving f euclideanToPair_measurePreserving

def fourierL2Two :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) :=
  pairEuclideanL2Equiv.trans
    ((MeasureTheory.Lp.fourierTransformₗᵢ E2 ℂ).trans pairEuclideanL2Equiv.symm)

/-- Pull a Schwartz function on pair coordinates back to Euclidean space. -/
def pairSchwartzToEuclidean : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(E2, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euclideanPairCLE

/-- Push a Euclidean Schwartz function to pair coordinates. -/
def euclideanSchwartzToPair : 𝓢(E2, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euclideanPairCLE.symm

@[simp] theorem pairSchwartzToEuclidean_toPair (f : 𝓢(E2, ℂ)) :
    pairSchwartzToEuclidean (euclideanSchwartzToPair f) = f := by
  ext x
  simp [pairSchwartzToEuclidean, euclideanSchwartzToPair]

@[simp] theorem euclideanSchwartzToPair_toEuclidean (f : 𝓢(ℝ × ℝ, ℂ)) :
    euclideanSchwartzToPair (pairSchwartzToEuclidean f) = f := by
  ext x
  simp [pairSchwartzToEuclidean, euclideanSchwartzToPair]

/-- The two-dimensional Fourier transform expressed on pair coordinates. -/
def pairSchwartzFourier (f : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  euclideanSchwartzToPair (𝓕 (pairSchwartzToEuclidean f))

/-- The inverse two-dimensional Fourier transform on pair coordinates. -/
def pairSchwartzFourierInv (f : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  euclideanSchwartzToPair (𝓕⁻ (pairSchwartzToEuclidean f))

@[simp] theorem pairSchwartzFourier_fourierInv (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourier (pairSchwartzFourierInv f) = f := by
  unfold pairSchwartzFourier pairSchwartzFourierInv
  rw [pairSchwartzToEuclidean_toPair, FourierTransform.fourier_fourierInv_eq]
  exact euclideanSchwartzToPair_toEuclidean f

@[simp] theorem pairSchwartzFourierInv_fourier (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourierInv (pairSchwartzFourier f) = f := by
  unfold pairSchwartzFourier pairSchwartzFourierInv
  rw [pairSchwartzToEuclidean_toPair, FourierTransform.fourierInv_fourier_eq]
  exact euclideanSchwartzToPair_toEuclidean f

@[simp] theorem pairSchwartzFourierInv_add (f g : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourierInv (f + g) =
      pairSchwartzFourierInv f + pairSchwartzFourierInv g := by
  unfold pairSchwartzFourierInv
  simp

@[simp] theorem pairSchwartzFourierInv_smul (c : ℂ)
    (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourierInv (c • f) = c • pairSchwartzFourierInv f := by
  unfold pairSchwartzFourierInv
  simp

private lemma pairToEuclideanL2_toLp (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairToEuclideanL2 (f.toLp 2 (volume.prod volume)) =
      (pairSchwartzToEuclidean f).toLp 2 volume := by
  unfold pairToEuclideanL2
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (f.toLp 2 (volume.prod volume)) euclideanToPair_measurePreserving,
    euclideanToPair_measurePreserving.quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume.prod volume)),
    (pairSchwartzToEuclidean f).coeFn_toLp 2 volume] with x hcomp hf hpair
  rw [hcomp, Function.comp_apply, hf, hpair]
  rfl

private lemma euclideanToPairL2_toLp (f : 𝓢(E2, ℂ)) :
    euclideanToPairL2 (f.toLp 2 volume) =
      (euclideanSchwartzToPair f).toLp 2 (volume.prod volume) := by
  unfold euclideanToPairL2
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (f.toLp 2 volume)
      pairToEuclidean_measurePreserving,
    pairToEuclidean_measurePreserving.quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 volume),
    (euclideanSchwartzToPair f).coeFn_toLp 2 (volume.prod volume)]
      with x hcomp hf hpair
  rw [hcomp, Function.comp_apply, hf, hpair]
  rfl

/-- Compatibility of the pair-coordinate Schwartz and `L²` Fourier
transforms. -/
theorem fourierL2Two_toLp (f : 𝓢(ℝ × ℝ, ℂ)) :
    fourierL2Two (f.toLp 2 (volume.prod volume)) =
      (pairSchwartzFourier f).toLp 2 (volume.prod volume) := by
  rw [fourierL2Two, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply]
  change euclideanToPairL2
      (FourierTransform.fourier (pairToEuclideanL2
        (f.toLp 2 (volume.prod volume)))) = _
  rw [pairToEuclideanL2_toLp, SchwartzMap.toLp_fourier_eq,
    euclideanToPairL2_toLp]
  rfl

theorem fourierL2Two_symm_toLp (f : 𝓢(ℝ × ℝ, ℂ)) :
    fourierL2Two.symm (f.toLp 2 (volume.prod volume)) =
      (pairSchwartzFourierInv f).toLp 2 (volume.prod volume) := by
  apply fourierL2Two.injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourierL2Two_toLp,
    pairSchwartzFourier_fourierInv]

/-- Pointwise conjugation on the pair-coordinate `L²` space. -/
def conjugateL2Two (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) :=
  (Lp.memLp f).star.toLp (star (f : ℝ × ℝ → ℂ))

theorem coeFn_conjugateL2Two
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    (conjugateL2Two f : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      fun x => star ((f : ℝ × ℝ → ℂ) x) :=
  MemLp.coeFn_toLp _

theorem norm_conjugateL2Two
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    ‖conjugateL2Two f‖ = ‖f‖ := by
  rw [conjugateL2Two, Lp.norm_toLp, Lp.norm_def]
  rw [eLpNorm_star]

private lemma conjugateL2Two_sub
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    conjugateL2Two (f - g) = conjugateL2Two f - conjugateL2Two g := by
  apply Lp.ext
  filter_upwards [coeFn_conjugateL2Two (f - g), coeFn_conjugateL2Two f,
    coeFn_conjugateL2Two g, Lp.coeFn_sub f g,
    Lp.coeFn_sub (conjugateL2Two f) (conjugateL2Two g)]
      with x hfg hf hg hsub hout
  rw [hfg, hsub, hout]
  change star ((f : ℝ × ℝ → ℂ) x - (g : ℝ × ℝ → ℂ) x) =
    (conjugateL2Two f : ℝ × ℝ → ℂ) x -
      (conjugateL2Two g : ℝ × ℝ → ℂ) x
  rw [hf, hg]
  simp

private lemma conjugateL2Two_add
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    conjugateL2Two (f + g) = conjugateL2Two f + conjugateL2Two g := by
  apply Lp.ext
  filter_upwards [coeFn_conjugateL2Two (f + g), coeFn_conjugateL2Two f,
    coeFn_conjugateL2Two g, Lp.coeFn_add f g,
    Lp.coeFn_add (conjugateL2Two f) (conjugateL2Two g)]
      with x hfg hf hg hadd hout
  rw [hfg, hadd, hout]
  change star ((f : ℝ × ℝ → ℂ) x + (g : ℝ × ℝ → ℂ) x) =
    (conjugateL2Two f : ℝ × ℝ → ℂ) x +
      (conjugateL2Two g : ℝ × ℝ → ℂ) x
  rw [hf, hg]
  simp

private lemma conjugateL2Two_smul (c : ℂ)
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    conjugateL2Two (c • f) = star c • conjugateL2Two f := by
  apply Lp.ext
  filter_upwards [coeFn_conjugateL2Two (c • f), coeFn_conjugateL2Two f,
    Lp.coeFn_smul c f, Lp.coeFn_smul (star c) (conjugateL2Two f)]
      with x hcf hf hsmul hout
  rw [hcf, hsmul, hout]
  change star (c * (f : ℝ × ℝ → ℂ) x) =
    star c * (conjugateL2Two f : ℝ × ℝ → ℂ) x
  rw [hf]
  simp

/-- The continuous complex-bilinear `L²` pairing, represented as a Hilbert
inner product after conjugating the first argument. -/
def bilinearL2Two
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) : ℂ :=
  inner ℂ (conjugateL2Two f) g

theorem bilinearL2Two_eq_integral
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2Two f g = ∫ x, (f : ℝ × ℝ → ℂ) x * (g : ℝ × ℝ → ℂ) x := by
  rw [bilinearL2Two, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_conjugateL2Two f] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

private lemma bilinearL2Two_toLp (f g : 𝓢(ℝ × ℝ, ℂ)) :
    bilinearL2Two (f.toLp 2 (volume.prod volume))
      (g.toLp 2 (volume.prod volume)) =
        ∫ x, f x * g x ∂(volume.prod volume) := by
  rw [bilinearL2Two_eq_integral]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume.prod volume),
    g.coeFn_toLp 2 (volume.prod volume)] with x hf hg
  rw [hf, hg]

theorem norm_bilinearL2Two_le
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    ‖bilinearL2Two f g‖ ≤ ‖f‖ * ‖g‖ := by
  exact (norm_inner_le_norm _ _).trans_eq (by rw [norm_conjugateL2Two])

theorem bilinearL2Two_add_left
    (f₁ f₂ g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2Two (f₁ + f₂) g =
      bilinearL2Two f₁ g + bilinearL2Two f₂ g := by
  simp only [bilinearL2Two, conjugateL2Two_add, inner_add_left]

theorem bilinearL2Two_smul_left (c : ℂ)
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2Two (c • f) g = c * bilinearL2Two f g := by
  simp only [bilinearL2Two, conjugateL2Two_smul, inner_smul_left]
  simp

theorem bilinearL2Two_add_right
    (f g₁ g₂ : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2Two f (g₁ + g₂) =
      bilinearL2Two f g₁ + bilinearL2Two f g₂ := by
  simp only [bilinearL2Two, inner_add_right]

theorem bilinearL2Two_smul_right (c : ℂ)
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2Two f (c • g) = c * bilinearL2Two f g := by
  simp only [bilinearL2Two, inner_smul_right]

theorem bilinearL2Two_sub_right
    (f g₁ g₂ : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2Two f (g₁ - g₂) =
      bilinearL2Two f g₁ - bilinearL2Two f g₂ := by
  simp only [bilinearL2Two, inner_sub_right]

private noncomputable def bilinearL2TwoLinear :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) →ₗ[ℂ]
      Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ bilinearL2Two
    bilinearL2Two_add_left bilinearL2Two_smul_left
    bilinearL2Two_add_right bilinearL2Two_smul_right

/-- The bilinear `L²` pairing as a continuous bilinear map. -/
noncomputable def bilinearL2TwoCLM :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) →L[ℂ]
      Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) →L[ℂ] ℂ :=
  bilinearL2TwoLinear.mkContinuous₂ 1 (fun f g => by
    change ‖bilinearL2Two f g‖ ≤ 1 * ‖f‖ * ‖g‖
    simpa only [one_mul] using norm_bilinearL2Two_le f g)

@[simp] theorem bilinearL2TwoCLM_apply
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2TwoCLM f g = bilinearL2Two f g := rfl

theorem bilinearL2Two_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => bilinearL2Two (f x) (g x)) μ := by
  exact bilinearL2TwoCLM.continuous₂.comp_aestronglyMeasurable (hf.prodMk hg)

theorem tendsto_bilinearL2Two
    {ι : Type*} {l : Filter ι}
    {f g : ι → Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))}
    {f₀ g₀ : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀)) :
    Tendsto (fun i => bilinearL2Two (f i) (g i)) l
      (𝓝 (bilinearL2Two f₀ g₀)) := by
  exact bilinearL2TwoCLM.continuous₂.continuousAt.tendsto.comp
    (hf.prodMk_nhds hg)

/-- Schwartz functions determine an `L²` vector through the continuous
bilinear pairing. -/
theorem eq_zero_of_bilinear_schwartz
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)))
    (h : ∀ q : 𝓢(ℝ × ℝ, ℂ),
      bilinearL2Two f (q.toLp 2 (volume.prod volume)) = 0) :
    f = 0 := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := ℂ)
    (E := ℝ × ℝ) (p := (2 : ℝ≥0∞)) (μ := volume.prod volume) (by norm_num)
  have hall : ∀ g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)),
      bilinearL2Two f g = 0 := by
    intro g
    let L := bilinearL2TwoCLM f
    let Z : Set (Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :=
      {u | L u = 0}
    have hker : Set.range (SchwartzMap.toLpCLM ℝ ℂ (2 : ℝ≥0∞)
        (volume.prod volume)) ⊆ Z := by
      rintro _ ⟨q, rfl⟩
      exact h q
    have hclosure : closure (Set.range (SchwartzMap.toLpCLM ℝ ℂ (2 : ℝ≥0∞)
        (volume.prod volume))) ⊆ Z := by
      exact closure_minimal hker (isClosed_singleton.preimage L.continuous)
    exact hclosure (by simpa only [hdense.closure_range] using Set.mem_univ g)
  have hz := hall (conjugateL2Two f)
  unfold bilinearL2Two at hz
  rw [inner_self_eq_zero] at hz
  apply norm_eq_zero.mp
  rw [← norm_conjugateL2Two]
  exact norm_eq_zero.mpr hz

/-- The continuous linear functional given by the bilinear `L²` pairing
against a fixed second argument. -/
def bilinearL2TwoLeftCLM
    (g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) →L[ℂ] ℂ :=
  let L : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)) →ₗ[ℂ] ℂ :=
    { toFun := fun f => bilinearL2Two f g
      map_add' := fun f₁ f₂ => bilinearL2Two_add_left f₁ f₂ g
      map_smul' := fun c f => by
        rw [bilinearL2Two_smul_left]
        rfl }
  L.mkContinuous ‖g‖ (fun f => by
    change ‖bilinearL2Two f g‖ ≤ ‖g‖ * ‖f‖
    simpa only [mul_comm] using norm_bilinearL2Two_le f g)

@[simp] theorem bilinearL2TwoLeftCLM_apply
    (f g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    bilinearL2TwoLeftCLM g f = bilinearL2Two f g := rfl

private lemma dist_bilinearL2Two_left
    (f f' g : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ))) :
    dist (bilinearL2Two f g) (bilinearL2Two f' g) ≤ dist f f' * ‖g‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  simp only [bilinearL2Two]
  rw [← inner_sub_left, ← conjugateL2Two_sub]
  exact (norm_inner_le_norm _ _).trans_eq (by rw [norm_conjugateL2Two])

private lemma pairSchwartz_integral_fourier_mul_eq
    (f g : 𝓢(ℝ × ℝ, ℂ)) :
    ∫ x, pairSchwartzFourier f x * g x ∂(volume.prod volume) =
      ∫ x, f x * pairSchwartzFourier g x ∂(volume.prod volume) := by
  have h := SchwartzMap.integral_fourier_mul_eq
    (pairSchwartzToEuclidean f) (pairSchwartzToEuclidean g)
  have hleft := euclideanToPair_measurePreserving.integral_comp
    euclideanPairCLE.toHomeomorph.measurableEmbedding
    (fun x => pairSchwartzFourier f x * g x)
  have hright := euclideanToPair_measurePreserving.integral_comp
    euclideanPairCLE.toHomeomorph.measurableEmbedding
    (fun x => f x * pairSchwartzFourier g x)
  rw [← hleft, ← hright]
  simpa [pairSchwartzFourier, pairSchwartzToEuclidean,
    euclideanSchwartzToPair, pairToEuclidean_toPair] using h

/-- Self-adjointness of the Fourier transform for the continuous bilinear
`L²` pairing, with the second input Schwartz. -/
theorem bilinearL2Two_fourier_left
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)))
    (g : 𝓢(ℝ × ℝ, ℂ)) :
    bilinearL2Two (fourierL2Two f) (g.toLp 2 (volume.prod volume)) =
      bilinearL2Two f ((pairSchwartzFourier g).toLp 2
        (volume.prod volume)) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := ℂ)
    (E := ℝ × ℝ) (p := (2 : ℝ≥0∞)) (μ := volume.prod volume) (by norm_num)
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hex (n : ℕ) : ∃ h : 𝓢(ℝ × ℝ, ℂ),
      dist (h.toLp 2 (volume.prod volume)) f < ε n := by
    simpa only [SchwartzMap.toLpCLM_apply, dist_comm] using
      hdense.exists_dist_lt f (hεpos n)
  let h : ℕ → 𝓢(ℝ × ℝ, ℂ) := fun n => Classical.choose (hex n)
  have hh (n : ℕ) : dist ((h n).toLp 2 (volume.prod volume)) f < ε n :=
    Classical.choose_spec (hex n)
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hto : Tendsto (fun n => (h n).toLp 2 (volume.prod volume))
      atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hh n).le) hεzero
  have hfourier : Tendsto
      (fun n => fourierL2Two ((h n).toLp 2 (volume.prod volume)))
      atTop (𝓝 (fourierL2Two f)) := fourierL2Two.continuous.continuousAt.tendsto.comp hto
  have hleft : Tendsto (fun n => bilinearL2Two
      (fourierL2Two ((h n).toLp 2 (volume.prod volume)))
      (g.toLp 2 (volume.prod volume))) atTop
      (𝓝 (bilinearL2Two (fourierL2Two f)
        (g.toLp 2 (volume.prod volume)))) := by
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_bilinearL2Two_left _ _ _)
    simpa using (tendsto_iff_dist_tendsto_zero.1 hfourier).mul_const
      ‖g.toLp 2 (volume.prod volume)‖
  have hright : Tendsto (fun n => bilinearL2Two
      ((h n).toLp 2 (volume.prod volume))
      ((pairSchwartzFourier g).toLp 2 (volume.prod volume))) atTop
      (𝓝 (bilinearL2Two f ((pairSchwartzFourier g).toLp 2
        (volume.prod volume)))) := by
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_bilinearL2Two_left _ _ _)
    simpa using (tendsto_iff_dist_tendsto_zero.1 hto).mul_const
      ‖(pairSchwartzFourier g).toLp 2 (volume.prod volume)‖
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with n
  rw [fourierL2Two_toLp, bilinearL2Two_toLp, bilinearL2Two_toLp]
  exact (pairSchwartz_integral_fourier_mul_eq (h n) g).symm

theorem bilinearL2Two_fourierInv_right
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)))
    (g : 𝓢(ℝ × ℝ, ℂ)) :
    bilinearL2Two f ((pairSchwartzFourierInv g).toLp 2
        (volume.prod volume)) =
      bilinearL2Two (fourierL2Two.symm f)
        (g.toLp 2 (volume.prod volume)) := by
  have h := bilinearL2Two_fourier_left (fourierL2Two.symm f)
    (pairSchwartzFourierInv g)
  rw [LinearIsometryEquiv.apply_symm_apply, pairSchwartzFourier_fourierInv] at h
  exact h

/-- Compactly supported smooth physical-space tests remain a determining
family after the pair-coordinate Fourier transform. -/
theorem eq_zero_of_bilinear_pairSchwartzFourier_compact
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)))
    (h : ∀ g : 𝓢(ℝ × ℝ, ℂ), HasCompactSupport (g : ℝ × ℝ → ℂ) →
      bilinearL2Two f ((pairSchwartzFourier g).toLp 2
        (volume.prod volume)) = 0) :
    f = 0 := by
  have hfourier : fourierL2Two f = 0 := by
    apply Lp.ext
    have hloc : LocallyIntegrable
        (fourierL2Two f : ℝ × ℝ → ℂ) (volume.prod volume) :=
      (Lp.memLp (fourierL2Two f)).locallyIntegrable (by norm_num)
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
      (fun g hg hgc => by
        let gC : ℝ × ℝ → ℂ := Complex.ofRealCLM ∘ g
        have hgCdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gC := by
          exact Complex.ofRealCLM.contDiff.comp hg
        have hgCc : HasCompactSupport gC := by
          exact hgc.comp_left rfl
        let gs : 𝓢(ℝ × ℝ, ℂ) := hgCc.toSchwartzMap hgCdiff
        have hpair : bilinearL2Two (fourierL2Two f)
            (gs.toLp 2 (volume.prod volume)) = 0 := by
          rw [bilinearL2Two_fourier_left]
          apply h gs
          change HasCompactSupport gC
          exact hgCc
        rw [bilinearL2Two_eq_integral] at hpair
        rw [← hpair]
        apply integral_congr_ae
        filter_upwards [gs.coeFn_toLp 2 (volume.prod volume)] with x hx
        rw [hx]
        change (g x : ℂ) * (fourierL2Two f : ℝ × ℝ → ℂ) x =
          (fourierL2Two f : ℝ × ℝ → ℂ) x * gs x
        change (g x : ℂ) * (fourierL2Two f : ℝ × ℝ → ℂ) x =
          (fourierL2Two f : ℝ × ℝ → ℂ) x * gC x
        simp only [gC, Function.comp_apply, Complex.ofRealCLM_apply]
        ring)
    filter_upwards [hae, Lp.coeFn_zero ℂ 2 (volume.prod volume)] with x hx hz
    exact hx.trans hz.symm
  exact fourierL2Two.injective (by simpa using hfourier)

theorem eq_zero_of_bilinear_pairSchwartzFourierInv_compact
    (f : Lp ℂ 2 (volume.prod volume : Measure (ℝ × ℝ)))
    (h : ∀ g : 𝓢(ℝ × ℝ, ℂ), HasCompactSupport (g : ℝ × ℝ → ℂ) →
      bilinearL2Two f ((pairSchwartzFourierInv g).toLp 2
        (volume.prod volume)) = 0) :
    f = 0 := by
  have hinv : fourierL2Two.symm f = 0 := by
    apply Lp.ext
    have hloc : LocallyIntegrable
        (fourierL2Two.symm f : ℝ × ℝ → ℂ) (volume.prod volume) :=
      (Lp.memLp (fourierL2Two.symm f)).locallyIntegrable (by norm_num)
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
      (fun g hg hgc => by
        let gC : ℝ × ℝ → ℂ := Complex.ofRealCLM ∘ g
        have hgCdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gC := by
          exact Complex.ofRealCLM.contDiff.comp hg
        have hgCc : HasCompactSupport gC := hgc.comp_left rfl
        let gs : 𝓢(ℝ × ℝ, ℂ) := hgCc.toSchwartzMap hgCdiff
        have hpair : bilinearL2Two (fourierL2Two.symm f)
            (gs.toLp 2 (volume.prod volume)) = 0 := by
          rw [← bilinearL2Two_fourierInv_right]
          exact h gs (by change HasCompactSupport gC; exact hgCc)
        rw [bilinearL2Two_eq_integral] at hpair
        rw [← hpair]
        apply integral_congr_ae
        filter_upwards [gs.coeFn_toLp 2 (volume.prod volume)] with x hx
        rw [hx]
        change (g x : ℂ) * (fourierL2Two.symm f : ℝ × ℝ → ℂ) x =
          (fourierL2Two.symm f : ℝ × ℝ → ℂ) x * gC x
        simp only [gC, Function.comp_apply, Complex.ofRealCLM_apply]
        ring)
    filter_upwards [hae, Lp.coeFn_zero ℂ 2 (volume.prod volume)] with x hx hz
    exact hx.trans hz.symm
  exact fourierL2Two.symm.injective (by simpa using hinv)

/-- Euclidean coordinate vectors corresponding to the two entries of a pair. -/
def pairBasis0 : E2 := euclideanPairCLE.symm (1, 0)
def pairBasis1 : E2 := euclideanPairCLE.symm (0, 1)

/-- Coordinate derivatives on pair Schwartz space, defined through the
Euclidean model so that Fourier identities are immediate. -/
def pairPartial0 (f : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  euclideanSchwartzToPair (LineDeriv.lineDerivOp pairBasis0
    (pairSchwartzToEuclidean f))

def pairPartial1 (f : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  euclideanSchwartzToPair (LineDeriv.lineDerivOp pairBasis1
    (pairSchwartzToEuclidean f))

theorem pairPartial0_apply (f : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial0 f z = deriv (fun x => f (x, z.2)) z.1 := by
  let c : ℝ → ℝ × ℝ := fun x => (x, z.2)
  have hc : HasDerivAt c (1, 0) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have hfcomp := (f.hasFDerivAt z).comp_hasDerivAt z.1 hc
  have hder : deriv (fun x => f (x, z.2)) z.1 =
      fderiv ℝ f z (1, 0) := by exact hfcomp.deriv
  have heq : pairPartial0 f =
      LineDeriv.lineDerivOp ((1, 0) : ℝ × ℝ) f := by
    unfold pairPartial0 pairBasis0
    unfold pairSchwartzToEuclidean euclideanSchwartzToPair
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    ext x
    simp [pairSchwartzToEuclidean, euclideanSchwartzToPair]
  rw [heq, hder]
  exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _

theorem pairPartial1_apply (f : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    pairPartial1 f z = deriv (fun y => f (z.1, y)) z.2 := by
  let c : ℝ → ℝ × ℝ := fun y => (z.1, y)
  have hc : HasDerivAt c (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hfcomp := (f.hasFDerivAt z).comp_hasDerivAt z.2 hc
  have hder : deriv (fun y => f (z.1, y)) z.2 =
      fderiv ℝ f z (0, 1) := by exact hfcomp.deriv
  have heq : pairPartial1 f =
      LineDeriv.lineDerivOp ((0, 1) : ℝ × ℝ) f := by
    unfold pairPartial1 pairBasis1
    unfold pairSchwartzToEuclidean euclideanSchwartzToPair
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    ext x
    simp [pairSchwartzToEuclidean, euclideanSchwartzToPair]
  rw [heq, hder]
  exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _

theorem inner_pairBasis0 (x : E2) :
    inner ℝ x pairBasis0 = (euclideanToPair x).1 := by
  rw [PiLp.inner_apply]
  simp [pairBasis0, euclideanPairCLE, euclideanToPair]

theorem inner_pairBasis1 (x : E2) :
    inner ℝ x pairBasis1 = (euclideanToPair x).2 := by
  rw [PiLp.inner_apply]
  simp [pairBasis1, euclideanPairCLE, euclideanToPair]

/-- Frequency multipliers corresponding to the two physical coordinate
derivatives under Mathlib's `2π` Fourier convention. -/
def pairFrequencyDeriv0 (f : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  euclideanSchwartzToPair
    (-(2 * Real.pi * Complex.I) •
      SchwartzMap.smulLeftCLM ℂ (fun x : E2 => inner ℝ x pairBasis0)
        (pairSchwartzToEuclidean f))

def pairFrequencyDeriv1 (f : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  euclideanSchwartzToPair
    (-(2 * Real.pi * Complex.I) •
      SchwartzMap.smulLeftCLM ℂ (fun x : E2 => inner ℝ x pairBasis1)
        (pairSchwartzToEuclidean f))

theorem pairFrequencyDeriv0_apply (f : 𝓢(ℝ × ℝ, ℂ)) (ξ : ℝ × ℝ) :
    pairFrequencyDeriv0 f ξ =
      -(2 * Real.pi * Complex.I) * (ξ.1 : ℂ) * f ξ := by
  unfold pairFrequencyDeriv0 euclideanSchwartzToPair pairSchwartzToEuclidean
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_apply, smul_eq_mul]
  have hg : (fun x : E2 => inner ℝ x pairBasis0).HasTemperateGrowth := by
    convert (((innerSL ℝ) pairBasis0).hasTemperateGrowth) using 1
    funext x
    exact real_inner_comm pairBasis0 x
  rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
    (g := fun x : E2 => inner ℝ x pairBasis0) hg]
  rw [inner_pairBasis0]
  simp
  ring

theorem pairFrequencyDeriv1_apply (f : 𝓢(ℝ × ℝ, ℂ)) (ξ : ℝ × ℝ) :
    pairFrequencyDeriv1 f ξ =
      -(2 * Real.pi * Complex.I) * (ξ.2 : ℂ) * f ξ := by
  unfold pairFrequencyDeriv1 euclideanSchwartzToPair pairSchwartzToEuclidean
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_apply, smul_eq_mul]
  have hg : (fun x : E2 => inner ℝ x pairBasis1).HasTemperateGrowth := by
    convert (((innerSL ℝ) pairBasis1).hasTemperateGrowth) using 1
    funext x
    exact real_inner_comm pairBasis1 x
  rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
    (g := fun x : E2 => inner ℝ x pairBasis1) hg]
  rw [inner_pairBasis1]
  simp
  ring

theorem pairPartial0_pairSchwartzFourier (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairPartial0 (pairSchwartzFourier f) =
      pairSchwartzFourier (pairFrequencyDeriv0 f) := by
  unfold pairPartial0 pairSchwartzFourier pairFrequencyDeriv0
  rw [pairSchwartzToEuclidean_toPair,
    pairSchwartzToEuclidean_toPair]
  rw [SchwartzMap.lineDerivOp_fourier_eq]

theorem pairPartial1_pairSchwartzFourier (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairPartial1 (pairSchwartzFourier f) =
      pairSchwartzFourier (pairFrequencyDeriv1 f) := by
  unfold pairPartial1 pairSchwartzFourier pairFrequencyDeriv1
  rw [pairSchwartzToEuclidean_toPair,
    pairSchwartzToEuclidean_toPair]
  rw [SchwartzMap.lineDerivOp_fourier_eq]

theorem pairSchwartzFourierInv_pairPartial0 (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourierInv (pairPartial0 f) =
      pairFrequencyDeriv0 (pairSchwartzFourierInv f) := by
  unfold pairPartial0 pairSchwartzFourierInv pairFrequencyDeriv0
  rw [pairSchwartzToEuclidean_toPair,
    pairSchwartzToEuclidean_toPair]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]

theorem pairSchwartzFourierInv_pairPartial1 (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourierInv (pairPartial1 f) =
      pairFrequencyDeriv1 (pairSchwartzFourierInv f) := by
  unfold pairPartial1 pairSchwartzFourierInv pairFrequencyDeriv1
  rw [pairSchwartzToEuclidean_toPair,
    pairSchwartzToEuclidean_toPair]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]

/-- Frequency-side multiplier produced by the spatial part of the conjugated
adjoint test. -/
def pairFrequencyConjugatedAdjoint (β : ℝ) (f : 𝓢(ℝ × ℝ, ℂ)) :
    𝓢(ℝ × ℝ, ℂ) :=
  pairFrequencyDeriv0 (pairFrequencyDeriv0 f) +
    pairFrequencyDeriv1 (pairFrequencyDeriv1 f) +
    ((2 * β : ℝ) : ℂ) • pairFrequencyDeriv0 f +
    ((β ^ 2 : ℝ) : ℂ) • f

theorem pairFrequencyConjugatedAdjoint_apply (β : ℝ)
    (f : 𝓢(ℝ × ℝ, ℂ)) (ξ : ℝ × ℝ) :
    pairFrequencyConjugatedAdjoint β f ξ =
      (((β ^ 2 - 4 * Real.pi ^ 2 * (ξ.1 ^ 2 + ξ.2 ^ 2) : ℝ) : ℂ) -
        Complex.I * ((4 * Real.pi * β * ξ.1 : ℝ) : ℂ)) * f ξ := by
  change pairFrequencyDeriv0 (pairFrequencyDeriv0 f) ξ +
      pairFrequencyDeriv1 (pairFrequencyDeriv1 f) ξ +
      ((2 * β : ℝ) : ℂ) * pairFrequencyDeriv0 f ξ +
      ((β ^ 2 : ℝ) : ℂ) * f ξ = _
  rw [pairFrequencyDeriv0_apply, pairFrequencyDeriv0_apply,
    pairFrequencyDeriv1_apply, pairFrequencyDeriv1_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pairConjugatedSpatial_pairSchwartzFourier (β : ℝ)
    (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairPartial0 (pairPartial0 (pairSchwartzFourier f)) +
        pairPartial1 (pairPartial1 (pairSchwartzFourier f)) +
        ((2 * β : ℝ) : ℂ) • pairPartial0 (pairSchwartzFourier f) +
        ((β ^ 2 : ℝ) : ℂ) • pairSchwartzFourier f =
      pairSchwartzFourier (pairFrequencyConjugatedAdjoint β f) := by
  rw [pairPartial0_pairSchwartzFourier,
    pairPartial0_pairSchwartzFourier,
    pairPartial1_pairSchwartzFourier,
    pairPartial1_pairSchwartzFourier]
  unfold pairFrequencyConjugatedAdjoint pairSchwartzFourier
  simp

theorem pairSchwartzFourierInv_conjugatedSpatial (β : ℝ)
    (f : 𝓢(ℝ × ℝ, ℂ)) :
    pairSchwartzFourierInv
        (pairPartial0 (pairPartial0 f) + pairPartial1 (pairPartial1 f) +
          ((2 * β : ℝ) : ℂ) • pairPartial0 f +
          ((β ^ 2 : ℝ) : ℂ) • f) =
      pairFrequencyConjugatedAdjoint β (pairSchwartzFourierInv f) := by
  rw [pairSchwartzFourierInv_add, pairSchwartzFourierInv_add,
    pairSchwartzFourierInv_add, pairSchwartzFourierInv_smul,
    pairSchwartzFourierInv_smul,
    pairSchwartzFourierInv_pairPartial0,
    pairSchwartzFourierInv_pairPartial0,
    pairSchwartzFourierInv_pairPartial1,
    pairSchwartzFourierInv_pairPartial1]
  rfl

end CubicNLSPhaseRetrieval
end
