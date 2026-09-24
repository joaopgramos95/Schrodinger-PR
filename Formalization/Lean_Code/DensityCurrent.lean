import Lean_Code.Setup

/-!
# The density determines the current

Blueprint chapter: `chap:current` (module 9).
Imports: modules 6, 7, 8, and 12.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The spacetime equal-modulus hypothesis used throughout the recovery argument. -/
def SameModulus (u v : ℝ → L2) : Prop :=
  ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
    ‖(u p.1 : ℝ → ℂ) p.2‖ = ‖(v p.1 : ℝ → ℂ) p.2‖

/-- Pointwise multiplication maps `L² × L²` into `L¹`. -/
theorem densityProductMem (f g : L2) :
    MemLp (fun x : ℝ => (f : ℝ → ℂ) x * (g : ℝ → ℂ) x) 1 volume := by
  simpa using (Lp.memLp g).mul' (Lp.memLp f)

/-- Bundled pointwise `L² × L² → L¹` product. -/
def densityProductL1 (f g : L2) : Lp ℂ 1 (volume : Measure ℝ) :=
  (densityProductMem f g).toLp
    (fun x : ℝ => (f : ℝ → ℂ) x * (g : ℝ → ℂ) x)

theorem norm_densityProductL1_le (f g : L2) :
    ‖densityProductL1 f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [densityProductL1, Lp.norm_toLp, Lp.norm_def, Lp.norm_def,
    ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)
  · have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (p := 2) (q := 2) (r := 1)
      (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g)
      (fun x y : ℂ => x * y) 1 (by filter_upwards with x; simp)
    simpa using h

theorem coe_densityProductL1 (f g : L2) :
    (densityProductL1 f g : ℝ → ℂ) =ᵐ[volume]
      fun x => (f : ℝ → ℂ) x * (g : ℝ → ℂ) x :=
  MemLp.coeFn_toLp _

/-- The pointwise product as a bilinear map. -/
noncomputable def densityProductLinear :
    L2 →ₗ[ℂ] L2 →ₗ[ℂ] Lp ℂ 1 (volume : Measure ℝ) :=
  LinearMap.mk₂ ℂ densityProductL1
    (fun f1 f2 g => by
      apply Lp.ext
      filter_upwards [coe_densityProductL1 (f1 + f2) g, coe_densityProductL1 f1 g,
        coe_densityProductL1 f2 g, Lp.coeFn_add f1 f2,
        Lp.coeFn_add (densityProductL1 f1 g) (densityProductL1 f2 g)]
      with x h h1 h2 hadd hout
      simp only [h, h1, h2, hadd, hout, Pi.add_apply]
      ring)
    (fun c f g => by
      apply Lp.ext
      filter_upwards [coe_densityProductL1 (c • f) g, coe_densityProductL1 f g,
        Lp.coeFn_smul c f, Lp.coeFn_smul c (densityProductL1 f g)]
      with x h hfg hf hout
      simp only [h, hfg, hf, hout, Pi.smul_apply]
      ring)
    (fun f g1 g2 => by
      apply Lp.ext
      filter_upwards [coe_densityProductL1 f (g1 + g2), coe_densityProductL1 f g1,
        coe_densityProductL1 f g2, Lp.coeFn_add g1 g2,
        Lp.coeFn_add (densityProductL1 f g1) (densityProductL1 f g2)]
      with x h h1 h2 hadd hout
      simp only [h, h1, h2, hadd, hout, Pi.add_apply]
      ring)
    (fun c f g => by
      apply Lp.ext
      filter_upwards [coe_densityProductL1 f (c • g), coe_densityProductL1 f g,
        Lp.coeFn_smul c g, Lp.coeFn_smul c (densityProductL1 f g)]
      with x h hfg hg hout
      simp only [h, hfg, hg, hout, Pi.smul_apply]
      ring)

/-- Continuous pointwise product `L² × L² → L¹`. -/
noncomputable def densityProductCLM :
    L2 →L[ℂ] L2 →L[ℂ] Lp ℂ 1 (volume : Measure ℝ) :=
  densityProductLinear.mkContinuous₂ 1 (fun f g => by
    change ‖densityProductL1 f g‖ ≤ 1 * ‖f‖ * ‖g‖
    simpa using norm_densityProductL1_le f g)

/-- Complex conjugation on the canonical `L²` model. -/
noncomputable def conjL2 (f : L2) : L2 :=
  Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume f

/-- The density `|f|²`, bundled in complex `L¹`. -/
noncomputable def densityL1 (f : L2) : Lp ℂ 1 (volume : Measure ℝ) :=
  densityProductCLM (conjL2 f) f

theorem continuous_densityL1 : Continuous densityL1 := by
  apply Continuous.clm_apply
  · exact densityProductCLM.continuous.comp
      (Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume).continuous
  · exact continuous_id

theorem coe_densityL1 (f : L2) :
    (densityL1 f : ℝ → ℂ) =ᵐ[volume]
      fun x => ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
  have hp : (densityProductCLM (conjL2 f) f : ℝ → ℂ) =ᵐ[volume]
      fun x => (conjL2 f : ℝ → ℂ) x * (f : ℝ → ℂ) x := by
    simpa [densityProductCLM, densityProductLinear] using
      coe_densityProductL1 (conjL2 f) f
  have hc := Complex.conjLIE.toContinuousLinearMap.coeFn_compLpL f
  filter_upwards [hp, hc] with x hp hc
  rw [densityL1, hp, conjL2, hc]
  simpa using Complex.conj_mul' ((f : ℝ → ℂ) x)

/-- `cor:all-time-density`: spacetime equality propagates to every `L²` time slice. -/
theorem all_time_density (σ : ℝ) (u v : GlobalSolution σ)
    (hmod : SameModulus u.u v.u) :
    ∀ t : ℝ, ∀ᵐ x : ℝ ∂volume,
      ‖(u.u t : ℝ → ℂ) x‖ ^ 2 = ‖(v.u t : ℝ → ℂ) x‖ ^ 2 := by
  have hsections : ∀ᵐ t : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      ‖(u.u t : ℝ → ℂ) x‖ = ‖(v.u t : ℝ → ℂ) x‖ :=
    Measure.ae_ae_of_ae_prod hmod
  have hdens : ∀ᵐ t : ℝ ∂volume, densityL1 (u.u t) = densityL1 (v.u t) := by
    filter_upwards [hsections] with t ht
    apply Lp.ext
    filter_upwards [coe_densityL1 (u.u t), coe_densityL1 (v.u t), ht]
      with x hu hv hx
    rw [hu, hv, hx]
  have hcu : Continuous (fun t => densityL1 (u.u t)) :=
    continuous_densityL1.comp u.continuous
  have hcv : Continuous (fun t => densityL1 (v.u t)) :=
    continuous_densityL1.comp v.continuous
  have hall : (fun t => densityL1 (u.u t)) = fun t => densityL1 (v.u t) :=
    Measure.eq_of_ae_eq hdens hcu hcv
  intro t
  have heq := congrFun hall t
  have hraw : (densityL1 (u.u t) : ℝ → ℂ) =ᵐ[volume]
      (densityL1 (v.u t) : ℝ → ℂ) := Filter.Eventually.of_forall fun x =>
        congrArg (fun q : Lp ℂ 1 (volume : Measure ℝ) => (q : ℝ → ℂ) x) heq
  filter_upwards [coe_densityL1 (u.u t), coe_densityL1 (v.u t), hraw]
    with x hu hv h
  rw [hu, hv] at h
  exact Complex.ofReal_injective h

/-- Equal spacetime moduli on an open time set give equal densities on every
time slice of that set. -/
theorem density_on_open (σ : ℝ) (u v : GlobalSolution σ) (I : Set ℝ)
    (hI : IsOpen I) (hmod : SameModulusOnSet I u.u v.u) :
    ∀ t ∈ I, ∀ᵐ x : ℝ ∂volume,
      ‖(u.u t : ℝ → ℂ) x‖ ^ 2 = ‖(v.u t : ℝ → ℂ) x‖ ^ 2 := by
  have hsections : ∀ᵐ t : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      t ∈ I → ‖(u.u t : ℝ → ℂ) x‖ = ‖(v.u t : ℝ → ℂ) x‖ :=
    Measure.ae_ae_of_ae_prod hmod
  have hdens : ∀ᵐ t : ℝ ∂volume.restrict I,
      densityL1 (u.u t) = densityL1 (v.u t) := by
    filter_upwards [ae_restrict_mem hI.measurableSet, ae_restrict_of_ae hsections]
      with t htI ht
    apply Lp.ext
    filter_upwards [coe_densityL1 (u.u t), coe_densityL1 (v.u t), ht]
      with x hu hv hx
    rw [hu, hv, hx htI]
  have hcu : Continuous (fun t => densityL1 (u.u t)) :=
    continuous_densityL1.comp u.continuous
  have hcv : Continuous (fun t => densityL1 (v.u t)) :=
    continuous_densityL1.comp v.continuous
  have hall : Set.EqOn (fun t => densityL1 (u.u t))
      (fun t => densityL1 (v.u t)) I :=
    Measure.eqOn_open_of_ae_eq hdens hI hcu.continuousOn hcv.continuousOn
  intro t ht
  have heq := hall ht
  have hraw : (densityL1 (u.u t) : ℝ → ℂ) =ᵐ[volume]
      (densityL1 (v.u t) : ℝ → ℂ) := Filter.Eventually.of_forall fun x =>
        congrArg (fun q : Lp ℂ 1 (volume : Measure ℝ) => (q : ℝ → ℂ) x) heq
  filter_upwards [coe_densityL1 (u.u t), coe_densityL1 (v.u t), hraw]
    with x hu hv h
  rw [hu, hv] at h
  exact Complex.ofReal_injective h

end CubicNLSPhaseRetrieval
