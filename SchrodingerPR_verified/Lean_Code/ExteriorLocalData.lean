import Lean_Code.WeakMild
import Lean_Code.WronskianExterior
import Lean_Code.EndpointForcing
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Local two-particle data for the exterior equation

The cubic forcing is locally square-integrable in time with values in `L²`.
Tensoring it with the other continuous `L²` solution therefore gives the
local `L²_{t,x,y}` source required by the distributional exterior equation.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

set_option maxHeartbeats 1000000

private lemma cubic_section_L2_eq_L6_cubed (f : L2) :
    eLpNorm (fun x : ℝ => ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) *
      (f : ℝ → ℂ) x) 2 volume =
      eLpNorm (f : ℝ → ℂ) 6 volume ^ (3 : ℝ) := by
  calc
    eLpNorm (fun x : ℝ => ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) *
        (f : ℝ → ℂ) x) 2 volume =
        eLpNorm (fun x : ℝ => ‖(f : ℝ → ℂ) x‖ ^ (3 : ℝ)) 2 volume := by
      apply eLpNorm_congr_norm_ae
      filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa [pow_succ]
    _ = eLpNorm (f : ℝ → ℂ) 6 volume ^ (3 : ℝ) := by
      rw [eLpNorm_norm_rpow _ (by norm_num)]
      norm_num

private theorem nonlin_eLpNorm_two_Icc_lt_top (sigma : ℝ)
    (u : GlobalSolution sigma) (T : ℝ) :
    eLpNorm u.nonlin 2 (volume.restrict (Set.Icc (-T) T)) < ⊤ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
  apply ne_of_lt
  calc
    (∫⁻ t in Set.Icc (-T) T, ‖u.nonlin t‖ₑ ^ (2 : ℝ) ∂volume) =
        ∫⁻ t in Set.Icc (-T) T,
          (eLpNorm (u.nonlin t : ℝ → ℂ) 2 volume) ^ (2 : ℝ) ∂volume := by
      apply lintegral_congr
      intro t
      rw [← Lp.enorm_def]
    _ = ∫⁻ t in Set.Icc (-T) T,
          (eLpNorm (u.u t : ℝ → ℂ) 6 volume) ^ (6 : ℝ) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae u.nonlin_eq] with t ht
      rw [eLpNorm_congr_ae ht, cubic_section_L2_eq_L6_cubed]
      rw [← ENNReal.rpow_mul]
      norm_num
    _ < ⊤ := by simpa [ENNReal.rpow_natCast] using u.memL6_loc T

/-- The recorded cubic curve belongs to `L²_t L²_x` on every symmetric
compact interval. -/
theorem nonlin_memLp_two_Icc (sigma : ℝ) (u : GlobalSolution sigma)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp u.nonlin 2 (volume.restrict (Set.Icc (-T) T)) :=
  ⟨endpoint_nonlin_aestronglyMeasurable_Icc sigma u (-T) T (neg_le_self hT),
    nonlin_eLpNorm_two_Icc_lt_top sigma u T⟩

private theorem solution_memLp_top_Icc (sigma : ℝ) (u : GlobalSolution sigma)
    (T : ℝ) : MemLp u.u ⊤ (volume.restrict (Set.Icc (-T) T)) := by
  have hcomp : IsCompact (u.u '' Set.Icc (-T) T) :=
    isCompact_Icc.image_of_continuousOn u.continuous.continuousOn
  obtain ⟨R, _hRpos, hR⟩ := hcomp.isBounded.subset_closedBall_lt 0 (0 : L2)
  apply memLp_top_of_bound u.continuous.aestronglyMeasurable.restrict R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hmem := hR ⟨t, ht, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem

/-- A cubic forcing tensor a continuous solution is locally `L²` as a
two-particle-valued curve. -/
theorem nonlin_tensor_memLp_two_Icc (sigma : ℝ) (u v : GlobalSolution sigma)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun t => tensorProductL2 (u.nonlin t) (v.u t)) 2
      (volume.restrict (Set.Icc (-T) T)) := by
  have hnu := nonlin_memLp_two_Icc sigma u T hT
  have hv := solution_memLp_top_Icc sigma v T
  apply MemLp.of_bilin tensorProductL2 1 hnu hv
  · exact tensorProductCLM.continuous₂.comp_aestronglyMeasurable
      (hnu.1.prodMk hv.1)
  · filter_upwards with t
    change ‖tensorProductL2 (u.nonlin t) (v.u t)‖ ≤
      (1 : ℝ) * ‖u.nonlin t‖ * ‖v.u t‖
    rw [norm_tensorProductL2]
    simp

/-- The nonlinear curve has a global a.e.-strongly-measurable version. -/
theorem nonlin_aestronglyMeasurable (sigma : ℝ) (u : GlobalSolution sigma) :
    AEStronglyMeasurable u.nonlin volume := by
  have hloc (n : ℕ) : AEStronglyMeasurable u.nonlin
      (volume.restrict (Set.Icc (-(n : ℝ)) (n : ℝ))) :=
    (nonlin_memLp_two_Icc sigma u n (by positivity)).1
  have hall := AEStronglyMeasurable.iUnion hloc
  have hunion : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) (n : ℝ)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt |x|
    refine ⟨n, ?_, ?_⟩
    · exact neg_le_of_abs_le hn.le
    · exact (le_abs_self x).trans hn.le
  rw [hunion, Measure.restrict_univ] at hall
  exact hall

/-- A measurable scalar representative of the nonlinear `L²` curve. -/
def nonlinearRepresentative (sigma : ℝ) (u : GlobalSolution sigma) :
    ℝ × ℝ → ℂ :=
  Classical.choose (joint_representative_L2_measurable volume u.nonlin
    (nonlin_aestronglyMeasurable sigma u))

lemma nonlinearRepresentative_measurable (sigma : ℝ) (u : GlobalSolution sigma) :
    Measurable (nonlinearRepresentative sigma u) :=
  (Classical.choose_spec (joint_representative_L2_measurable volume u.nonlin
    (nonlin_aestronglyMeasurable sigma u))).1

lemma nonlinearRepresentative_slice (sigma : ℝ) (u : GlobalSolution sigma) :
    ∀ᵐ t : ℝ ∂volume,
      (fun x => nonlinearRepresentative sigma u (t, x)) =ᵐ[volume]
        (u.nonlin t : ℝ → ℂ) :=
  (Classical.choose_spec (joint_representative_L2_measurable volume u.nonlin
    (nonlin_aestronglyMeasurable sigma u))).2

/-- A measurable representative of the tensor `u.nonlin ⊗ v`. -/
def measurableNonlinTensor (sigma : ℝ) (u v : GlobalSolution sigma) :
    ℝ × (ℝ × ℝ) → ℂ := fun p =>
  nonlinearRepresentative sigma u (p.1, p.2.1) *
    solutionRepresentative sigma v (p.1, p.2.2)

lemma measurableNonlinTensor_measurable (sigma : ℝ)
    (u v : GlobalSolution sigma) : Measurable (measurableNonlinTensor sigma u v) := by
  exact (nonlinearRepresentative_measurable sigma u).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) |>.mul
    ((solutionRepresentative_measurable sigma v).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

lemma measurableNonlinTensor_slice (sigma : ℝ) (u v : GlobalSolution sigma) :
    ∀ᵐ t : ℝ ∂volume,
      (fun z => measurableNonlinTensor sigma u v (t, z)) =ᵐ[volume.prod volume]
        fun z => (u.nonlin t : ℝ → ℂ) z.1 * (v.u t : ℝ → ℂ) z.2 := by
  filter_upwards [nonlinearRepresentative_slice sigma u] with t hnu
  have hv := solutionRepresentative_slice sigma v t
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnu,
    Measure.quasiMeasurePreserving_snd.ae hv] with z hnu' hv'
  simp only [measurableNonlinTensor, hnu', hv']

/-- Fubini transfer from an `L²`-valued curve to a jointly measurable scalar
representative. -/
theorem memLp_two_prod_of_slices
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    {mu : Measure A} {nu : Measure X} [SFinite nu]
    (F : A × X → ℂ) (hF : AEStronglyMeasurable F (mu.prod nu))
    (w : A → Lp ℂ 2 nu) (hw : MemLp w 2 mu)
    (hslice : ∀ᵐ a ∂mu, (fun x => F (a, x)) =ᵐ[nu] (w a : X → ℂ)) :
    MemLp F 2 (mu.prod nu) := by
  refine ⟨hF, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
  apply ne_of_lt
  rw [lintegral_prod _ (hF.enorm.pow_const 2)]
  calc
    (∫⁻ a, ∫⁻ x, ‖F (a, x)‖ₑ ^ (2 : ℝ) ∂nu ∂mu) =
        ∫⁻ a, ‖w a‖ₑ ^ (2 : ℝ) ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hslice] with a ha
      calc
        (∫⁻ x, ‖F (a, x)‖ₑ ^ (2 : ℝ) ∂nu) =
            ∫⁻ x, ‖(w a : X → ℂ) x‖ₑ ^ (2 : ℝ) ∂nu := by
          apply lintegral_congr_ae
          filter_upwards [ha] with x hx
          rw [hx]
        _ = ‖w a‖ₑ ^ (2 : ℝ) := by
          rw [Lp.enorm_def]
          exact (eLpNorm_nnreal_pow_eq_lintegral
            (f := (w a : X → ℂ)) (p := (2 : NNReal)) (by norm_num)).symm
    _ < ⊤ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hw.2

/-- The measurable nonlinear tensor is locally square-integrable in all
three variables. -/
theorem measurableNonlinTensor_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (measurableNonlinTensor sigma u v) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)) := by
  let W : ℝ → TwoParticleL2 := fun t => tensorProductL2 (u.nonlin t) (v.u t)
  have hW := nonlin_tensor_memLp_two_Icc sigma u v T hT
  apply memLp_two_prod_of_slices (measurableNonlinTensor sigma u v)
    (measurableNonlinTensor_measurable sigma u v).aestronglyMeasurable W hW
  filter_upwards [ae_restrict_of_ae (measurableNonlinTensor_slice sigma u v)]
    with t ht
  filter_upwards [ht, coe_tensorProductL2 (u.nonlin t) (v.u t)] with z hraw hcoe
  exact hraw.trans hcoe.symm

private theorem solution_nonlin_tensor_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun t => tensorProductL2 (u.u t) (v.nonlin t)) 2
      (volume.restrict (Set.Icc (-T) T)) := by
  have hu := solution_memLp_top_Icc sigma u T
  have hnv := nonlin_memLp_two_Icc sigma v T hT
  apply MemLp.of_bilin tensorProductL2 1 hu hnv
  · exact tensorProductCLM.continuous₂.comp_aestronglyMeasurable
      (hu.1.prodMk hnv.1)
  · filter_upwards with t
    change ‖tensorProductL2 (u.u t) (v.nonlin t)‖ ≤
      (1 : ℝ) * ‖u.u t‖ * ‖v.nonlin t‖
    rw [norm_tensorProductL2]
    simp

/-- The source obtained by differentiating the exterior tensor in the
interaction picture, expressed using jointly measurable representatives. -/
def measurableExteriorSource (sigma : ℝ) (u v : GlobalSolution sigma) :
    ℝ × (ℝ × ℝ) → ℂ := fun p =>
  (sigma : ℂ) *
    (nonlinearRepresentative sigma u (p.1, p.2.1) *
          solutionRepresentative sigma v (p.1, p.2.2) +
      solutionRepresentative sigma u (p.1, p.2.1) *
          nonlinearRepresentative sigma v (p.1, p.2.2) -
      nonlinearRepresentative sigma v (p.1, p.2.1) *
          solutionRepresentative sigma u (p.1, p.2.2) -
      solutionRepresentative sigma v (p.1, p.2.1) *
          nonlinearRepresentative sigma u (p.1, p.2.2))

lemma measurableExteriorSource_measurable (sigma : ℝ)
    (u v : GlobalSolution sigma) : Measurable (measurableExteriorSource sigma u v) := by
  have hnu := nonlinearRepresentative_measurable sigma u
  have hnv := nonlinearRepresentative_measurable sigma v
  have hu := solutionRepresentative_measurable sigma u
  have hv := solutionRepresentative_measurable sigma v
  unfold measurableExteriorSource
  fun_prop

def exteriorSourceCurve (sigma : ℝ) (u v : GlobalSolution sigma)
    (t : ℝ) : TwoParticleL2 :=
  (sigma : ℂ) •
    ((tensorProductL2 (u.nonlin t) (v.u t) +
        tensorProductL2 (u.u t) (v.nonlin t)) -
      tensorProductL2 (v.nonlin t) (u.u t) -
      tensorProductL2 (v.u t) (u.nonlin t))

/-- The bundled exterior source is Bochner-integrable on every finite time
interval.  This is the time-curve form of the local spacetime `L²` estimate. -/
theorem exteriorSourceCurve_intervalIntegrable (sigma : ℝ)
    (u v : GlobalSolution sigma) (a b : ℝ) :
    IntervalIntegrable (exteriorSourceCurve sigma u v) volume a b := by
  let T : ℝ := |a| + |b|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have h1 := nonlin_tensor_memLp_two_Icc sigma u v T hT
  have h2 := solution_nonlin_tensor_memLp_two_Icc sigma u v T hT
  have h3 := nonlin_tensor_memLp_two_Icc sigma v u T hT
  have h4 := solution_nonlin_tensor_memLp_two_Icc sigma v u T hT
  have hcurve : MemLp (exteriorSourceCurve sigma u v) 2
      (volume.restrict (Set.Icc (-T) T)) := by
    exact (((h1.add h2).sub h3).sub h4).const_smul (sigma : ℂ)
  have hsub : Set.uIcc a b ⊆ Set.Icc (-T) T := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨hat, htb⟩ | ⟨hbt, hta⟩
    · constructor <;> dsimp [T] <;>
        linarith [neg_abs_le a, neg_abs_le b, le_abs_self a, le_abs_self b]
    · constructor <;> dsimp [T] <;>
        linarith [neg_abs_le a, neg_abs_le b, le_abs_self a, le_abs_self b]
  have hcurve1 : MemLp (exteriorSourceCurve sigma u v) 1
      (volume.restrict (Set.Icc (-T) T)) := hcurve.mono_exponent (by norm_num)
  have hint : IntegrableOn (exteriorSourceCurve sigma u v) (Set.Icc (-T) T) :=
    memLp_one_iff_integrable.mp hcurve1
  exact (hint.mono_set hsub).intervalIntegrable

lemma measurableExteriorSource_slice (sigma : ℝ)
    (u v : GlobalSolution sigma) :
    ∀ᵐ t : ℝ ∂volume,
      (fun z => measurableExteriorSource sigma u v (t, z))
        =ᵐ[volume.prod volume]
          (exteriorSourceCurve sigma u v t : ℝ × ℝ → ℂ) := by
  filter_upwards [nonlinearRepresentative_slice sigma u,
    nonlinearRepresentative_slice sigma v] with t hnu hnv
  have hu := solutionRepresentative_slice sigma u t
  have hv := solutionRepresentative_slice sigma v t
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnu,
    Measure.quasiMeasurePreserving_snd.ae hnu,
    Measure.quasiMeasurePreserving_fst.ae hnv,
    Measure.quasiMeasurePreserving_snd.ae hnv,
    Measure.quasiMeasurePreserving_fst.ae hu,
    Measure.quasiMeasurePreserving_snd.ae hu,
    Measure.quasiMeasurePreserving_fst.ae hv,
    Measure.quasiMeasurePreserving_snd.ae hv,
    coe_tensorProductL2 (u.nonlin t) (v.u t),
    coe_tensorProductL2 (u.u t) (v.nonlin t),
    coe_tensorProductL2 (v.nonlin t) (u.u t),
    coe_tensorProductL2 (v.u t) (u.nonlin t),
    Lp.coeFn_add (tensorProductL2 (u.nonlin t) (v.u t))
      (tensorProductL2 (u.u t) (v.nonlin t)),
    Lp.coeFn_sub
      (tensorProductL2 (u.nonlin t) (v.u t) +
        tensorProductL2 (u.u t) (v.nonlin t))
      (tensorProductL2 (v.nonlin t) (u.u t)),
    Lp.coeFn_sub
      ((tensorProductL2 (u.nonlin t) (v.u t) +
          tensorProductL2 (u.u t) (v.nonlin t)) -
        tensorProductL2 (v.nonlin t) (u.u t))
      (tensorProductL2 (v.u t) (u.nonlin t)),
    Lp.coeFn_smul (sigma : ℂ)
      (((tensorProductL2 (u.nonlin t) (v.u t) +
          tensorProductL2 (u.u t) (v.nonlin t)) -
        tensorProductL2 (v.nonlin t) (u.u t)) -
        tensorProductL2 (v.u t) (u.nonlin t))]
      with z hnux hnuy hnvx hnvy hux huy hvx hvy h1 h2 h3 h4 hadd hsub1 hsub2 hsmul
  simp only [measurableExteriorSource, exteriorSourceCurve, hsmul, Pi.smul_apply,
    hsub2, Pi.sub_apply, hsub1, hadd, Pi.add_apply, h1, h2, h3, h4,
    hnux, hnuy, hnvx, hnvy, hux, huy, hvx, hvy, smul_eq_mul]

/-- The measurable exterior source is locally `L²` in spacetime. -/
theorem measurableExteriorSource_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (measurableExteriorSource sigma u v) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)) := by
  have h1 := nonlin_tensor_memLp_two_Icc sigma u v T hT
  have h2 := solution_nonlin_tensor_memLp_two_Icc sigma u v T hT
  have h3 := nonlin_tensor_memLp_two_Icc sigma v u T hT
  have h4 := solution_nonlin_tensor_memLp_two_Icc sigma v u T hT
  have hcurve : MemLp (exteriorSourceCurve sigma u v) 2
      (volume.restrict (Set.Icc (-T) T)) := by
    exact (((h1.add h2).sub h3).sub h4).const_smul (sigma : ℂ)
  apply memLp_two_prod_of_slices (measurableExteriorSource sigma u v)
    (measurableExteriorSource_measurable sigma u v).aestronglyMeasurable
    (exteriorSourceCurve sigma u v) hcurve
  exact ae_restrict_of_ae (measurableExteriorSource_slice sigma u v)

/-- The measurable exterior field is locally square-integrable in spacetime.
This lower-exponent estimate is sufficient for all compactly supported weak
pairings and follows directly from continuity of the bundled exterior curve. -/
theorem measurableExterior_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) :
    MemLp (measurableExterior u v) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)) := by
  let W : ℝ → TwoParticleL2 := fun t => exteriorProductL2 (u.u t) (v.u t)
  have hWcont : Continuous W :=
    continuous_exteriorProductL2 u.u v.u u.continuous v.continuous
  have hcomp : IsCompact (W '' Set.Icc (-T) T) :=
    isCompact_Icc.image_of_continuousOn hWcont.continuousOn
  obtain ⟨R, _hRpos, hR⟩ := hcomp.isBounded.subset_closedBall_lt 0
    (0 : TwoParticleL2)
  have hWtop : MemLp W ⊤ (volume.restrict (Set.Icc (-T) T)) := by
    apply memLp_top_of_bound hWcont.aestronglyMeasurable.restrict R
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hmem := hR ⟨t, ht, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
  have hWtwo : MemLp W 2 (volume.restrict (Set.Icc (-T) T)) :=
    hWtop.mono_exponent (by norm_num)
  apply memLp_two_prod_of_slices (measurableExterior u v)
    (measurableExterior_measurable u v).aestronglyMeasurable W hWtwo
  filter_upwards with t
  filter_upwards [measurableExterior_slice u v t,
    coe_exteriorProductL2 (u.u t) (v.u t)] with z hraw hcoe
  exact hraw.trans hcoe.symm

/-- The particle-coordinate ridge potential built from the same jointly
measurable solution representative. -/
def measurableParticlePotential (sigma : ℝ) (u : GlobalSolution sigma)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ((sigma * (‖solutionRepresentative sigma u (p.1, p.2.1)‖ ^ 2 +
    ‖solutionRepresentative sigma u (p.1, p.2.2)‖ ^ 2) : ℝ) : ℂ)

lemma measurableParticlePotential_measurable (sigma : ℝ)
    (u : GlobalSolution sigma) : Measurable (measurableParticlePotential sigma u) := by
  have hu := solutionRepresentative_measurable sigma u
  unfold measurableParticlePotential
  fun_prop

/-- On an equal-density time region, the differentiated tensor source
factors as the real ridge potential times the exterior product. -/
theorem measurableExteriorSource_eq_potential_mul (sigma : ℝ)
    (u v : GlobalSolution sigma) (I : Set ℝ) (hI : IsOpen I)
    (hmod : SameModulusOnSet I u.u v.u) :
    ∀ᵐ p : ℝ × (ℝ × ℝ)
      ∂((volume.restrict I).prod (volume.prod volume)),
      measurableExteriorSource sigma u v p =
        measurableParticlePotential sigma u p * measurableExterior u v p := by
  change ∀ᵐ p : ℝ × (ℝ × ℝ)
      ∂((volume.restrict I).prod (volume.prod volume)),
    measurableExteriorSource sigma u v p =
      (measurableParticlePotential sigma u * measurableExterior u v) p
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurableExteriorSource_measurable sigma u v)
    ((measurableParticlePotential_measurable sigma u).mul
      (measurableExterior_measurable u v)))]
  filter_upwards [ae_restrict_mem hI.measurableSet,
      ae_restrict_of_ae (nonlinearRepresentative_slice sigma u),
      ae_restrict_of_ae (nonlinearRepresentative_slice sigma v),
      ae_restrict_of_ae u.nonlin_eq, ae_restrict_of_ae v.nonlin_eq]
      with t htI hnu hnv hnlu hnlv
  have hu := solutionRepresentative_slice sigma u t
  have hv := solutionRepresentative_slice sigma v t
  have hd := density_on_open sigma u v I hI hmod t htI
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnu,
      Measure.quasiMeasurePreserving_snd.ae hnu,
      Measure.quasiMeasurePreserving_fst.ae hnv,
      Measure.quasiMeasurePreserving_snd.ae hnv,
      Measure.quasiMeasurePreserving_fst.ae hnlu,
      Measure.quasiMeasurePreserving_snd.ae hnlu,
      Measure.quasiMeasurePreserving_fst.ae hnlv,
      Measure.quasiMeasurePreserving_snd.ae hnlv,
      Measure.quasiMeasurePreserving_fst.ae hu,
      Measure.quasiMeasurePreserving_snd.ae hu,
      Measure.quasiMeasurePreserving_fst.ae hv,
      Measure.quasiMeasurePreserving_snd.ae hv,
      Measure.quasiMeasurePreserving_fst.ae hd,
      Measure.quasiMeasurePreserving_snd.ae hd]
      with z hnux hnuy hnvx hnvy hnlux hnluy hnlvx hnlvy
        hux huy hvx hvy hdx hdy
  simp only [Pi.mul_apply, measurableExteriorSource, measurableParticlePotential,
    measurableExterior, hnux, hnuy, hnvx, hnvy, hnlux, hnluy,
    hnlvx, hnlvy, hux, huy, hvx, hvy]
  push_cast
  have hdxC : ((‖(u.u t : ℝ → ℂ) z.1‖ : ℂ) ^ 2) =
      ((‖(v.u t : ℝ → ℂ) z.1‖ : ℂ) ^ 2) := by
    exact_mod_cast hdx
  have hdyC : ((‖(u.u t : ℝ → ℂ) z.2‖ : ℂ) ^ 2) =
      ((‖(v.u t : ℝ → ℂ) z.2‖ : ℂ) ^ 2) := by
    exact_mod_cast hdy
  rw [← hdxC, ← hdyC]
  ring

/-- Composition in the spatial variables with the fixed normal-coordinate
linear equivalence preserves finite `Lᵖ` membership on any time measure. -/
theorem MemLp.comp_time_normalToParticle
    {A : Type*} [MeasurableSpace A] (mu : Measure A) [SFinite mu]
    {p : ℝ≥0∞} {g : A × (ℝ × ℝ) → ℂ}
    (hg : MemLp g p (mu.prod (volume.prod volume))) :
    MemLp (g ∘ fun z => (z.1, normalToParticle z.2)) p
      (mu.prod (volume.prod volume)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal
    |(LinearMap.det (normalToParticle : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|
  let L : A × (ℝ × ℝ) → A × (ℝ × ℝ) := Prod.map id normalToParticle
  have hdet : LinearMap.det (normalToParticle :
      (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' normalToParticle).ne_zero
  have hnormal : Measure.map normalToParticle (volume.prod volume) =
      c • (volume.prod volume) := by
    simpa [c] using Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume.prod volume : Measure (ℝ × ℝ)) hdet
  have hmap : Measure.map L (mu.prod (volume.prod volume)) =
      c • (mu.prod (volume.prod volume)) := by
    rw [show Measure.map L (mu.prod (volume.prod volume)) =
        (Measure.map id mu).prod (Measure.map normalToParticle
          (volume.prod volume)) by
      symm
      exact Measure.map_prod_map mu (volume.prod volume) measurable_id
        normalToParticle.toLinearMap.continuous_of_finiteDimensional.measurable]
    rw [Measure.map_id, hnormal, Measure.prod_smul_right]
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgmap : MemLp g p (Measure.map L (mu.prod (volume.prod volume))) := by
    rw [hmap]
    exact hg.smul_measure hc
  have hcomp := hgmap.comp_of_map
    ((show Measurable L by
      exact measurable_id.prodMap
        normalToParticle.toLinearMap.continuous_of_finiteDimensional.measurable).aemeasurable)
  simpa [L, Function.comp_def, Prod.map] using hcomp

/-- Exterior source transported to normal/tangential coordinates. -/
def measurableNormalExteriorSource (sigma : ℝ) (u v : GlobalSolution sigma) :
    ℝ × (ℝ × ℝ) → ℂ :=
  measurableExteriorSource sigma u v ∘
    fun p => (p.1, normalToParticle p.2)

lemma measurableNormalExteriorSource_measurable (sigma : ℝ)
    (u v : GlobalSolution sigma) :
    Measurable (measurableNormalExteriorSource sigma u v) := by
  exact (measurableExteriorSource_measurable sigma u v).comp
    (measurable_fst.prodMk
      (normalToParticle.toLinearMap.continuous_of_finiteDimensional.measurable.comp
        measurable_snd))

theorem measurableNormalExteriorSource_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (measurableNormalExteriorSource sigma u v) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)) := by
  unfold measurableNormalExteriorSource
  exact MemLp.comp_time_normalToParticle
    (p := 2) (g := measurableExteriorSource sigma u v)
    (volume.restrict (Set.Icc (-T) T))
    (measurableExteriorSource_memLp_two_Icc sigma u v T hT)

/-- Local spacetime `L²` control is preserved by the normal-coordinate
rotation. -/
theorem measurableNormalExterior_memLp_two_Icc (sigma : ℝ)
    (u v : GlobalSolution sigma) (T : ℝ) :
    MemLp (measurableNormalExterior u v) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume)) := by
  change MemLp
    (measurableExterior u v ∘ fun p => (p.1, normalToParticle p.2)) 2
      ((volume.restrict (Set.Icc (-T) T)).prod (volume.prod volume))
  exact MemLp.comp_time_normalToParticle
    (p := 2) (g := measurableExterior u v)
    (volume.restrict (Set.Icc (-T) T))
    (measurableExterior_memLp_two_Icc sigma u v T)

/-- In normal coordinates the same source is exactly the ridge forcing on
the equal-modulus region. -/
theorem measurableNormalExteriorSource_eq_ridge_mul (sigma : ℝ)
    (u v : GlobalSolution sigma) (I : Set ℝ) (hI : IsOpen I)
    (hmod : SameModulusOnSet I u.u v.u) :
    ∀ᵐ p : ℝ × (ℝ × ℝ)
      ∂((volume.restrict I).prod (volume.prod volume)),
      measurableNormalExteriorSource sigma u v p =
        measurableRidgePotential sigma u p * measurableNormalExterior u v p := by
  have hqmp := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (volume.restrict I))
    normalToParticle_quasiMeasurePreserving
  have h := hqmp.ae
    (measurableExteriorSource_eq_potential_mul sigma u v I hI hmod)
  simpa [measurableNormalExteriorSource, measurableParticlePotential,
    measurableRidgePotential, measurableNormalExterior,
    fromNormalCoordinates, normalToParticle, Function.comp_def, Prod.map] using h

end CubicNLSPhaseRetrieval
