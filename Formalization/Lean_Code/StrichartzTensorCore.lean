import Lean_Code.StrichartzKernel

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 2000000

namespace CubicNLSPhaseRetrieval

def conjSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap

@[simp] lemma conjSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjSchwartz f x = conj (f x) := rfl

def tensorRaw {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ i, a i p.1 * b i p.2

def tensorConjSlice {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) :
    SchwartzMap ℝ ℂ :=
  ∑ i, conj (a i t) • conjSchwartz (b i)

@[simp] lemma tensorConjSlice_apply {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ)
    (t x : ℝ) : tensorConjSlice a b t x = conj (tensorRaw a b (t, x)) := by
  simp [tensorConjSlice, tensorRaw, conjSchwartz, map_sum, map_mul, smul_eq_mul]

def tensorAdjointCurve {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) : L2 :=
  freeProp (-t) ((tensorConjSlice a b t).toLp 2 volume)

lemma tensorAdjointCurve_eq_sum {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) :
    tensorAdjointCurve a b t =
      ∑ i, conj (a i t) • freeProp (-t) ((conjSchwartz (b i)).toLp 2 volume) := by
  unfold tensorAdjointCurve tensorConjSlice
  change freeProp (-t) ((SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (∑ i, conj (a i t) • conjSchwartz (b i))) = _
  rw [map_sum]
  change (freePropLIE (-t))
    (∑ i, (SchwartzMap.toLpCLM ℂ ℂ 2 volume)
      (conj (a i t) • conjSchwartz (b i))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, SchwartzMap.toLpCLM_apply, freePropLIE_apply, freeProp_smul]

lemma tensorAdjointCurve_integrable {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    Integrable (tensorAdjointCurve a b) volume := by
  rw [show tensorAdjointCurve a b = fun t =>
      ∑ i, conj (a i t) • freeProp (-t) ((conjSchwartz (b i)).toLp 2 volume) by
    funext t
    exact tensorAdjointCurve_eq_sum a b t]
  apply integrable_finset_sum
  intro i hi
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => conj (a i t) • freeProp (-t) ((conjSchwartz (b i)).toLp 2 volume)) volume := by
    apply Continuous.aestronglyMeasurable
    exact ((Complex.continuous_conj.comp (a i).continuous).smul
      (continuous_freeProp_joint.comp
        (continuous_neg.prodMk continuous_const)))
  apply Integrable.mono' ((a i).integrable.norm.const_mul
    ‖(conjSchwartz (b i)).toLp 2 volume‖) hmeas
  filter_upwards with t
  rw [norm_smul, norm_freeProp, mul_comm]
  simp only [Complex.norm_conj]
  exact le_rfl

def tensorAdjoint {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) : L2 :=
  ∫ t : ℝ, tensorAdjointCurve a b t

/- This identity is not needed by the quadratic-form proof; omitting it keeps
the compiled tensor core substantially smaller. -/
/-
lemma freeProp_tensorAdjoint {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) :
    freeProp t (tensorAdjoint a b) =
      ∫ s : ℝ, ∑ i, conj (a i s) •
        freeProp (t - s) ((conjSchwartz (b i)).toLp 2 volume) := by
  let U : L2 →L[ℂ] L2 := (freePropLIE t).toContinuousLinearEquiv.toContinuousLinearMap
  rw [tensorAdjoint, show freeProp t (∫ s : ℝ, tensorAdjointCurve a b s) =
      U (∫ s : ℝ, tensorAdjointCurve a b s) by rfl,
    ← U.integral_comp_comm (tensorAdjointCurve_integrable a b)]
  apply integral_congr_ae
  filter_upwards with s
  unfold U
  rw [tensorAdjointCurve_eq_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, freePropLIE_apply]
  congr 1
  rw [propagator_unitary.2.1]
  congr 2
  ring
-/

/- Split into the follow-on `StrichartzTensorL1` and
`StrichartzTensorPairing` modules to keep compiled proof objects small. -/
/-
def schwartzL1E (f : SchwartzMap ℝ ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ‖f x‖ₑ

lemma schwartzL1E_ne_top (f : SchwartzMap ℝ ℂ) : schwartzL1E f ≠ ⊤ := by
  exact ne_of_lt (by
    simpa only [schwartzL1E] using
      (hasFiniteIntegral_iff_enorm.mp f.integrable.hasFiniteIntegral))

def tensorSliceL1 {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) : ℝ≥0∞ :=
  schwartzL1E (tensorConjSlice a b t)

def tensorSize {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∑ i, ‖a i t‖ₑ * schwartzL1E (conjSchwartz (b i))

lemma tensorSliceL1_measurable {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    Measurable (tensorSliceL1 a b) := by
  have hG : Measurable (fun p : ℝ × ℝ => conj (tensorRaw a b p)) := by
    fun_prop
  have hm := spatialL1_measurable (fun p : ℝ × ℝ => conj (tensorRaw a b p)) hG
  convert hm using 1
  funext t
  unfold tensorSliceL1 schwartzL1E spatialL1
  apply lintegral_congr
  intro x
  rw [tensorConjSlice_apply]

lemma tensorSliceL1_le_size {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) :
    tensorSliceL1 a b t ≤ tensorSize a b t := by
  unfold tensorSliceL1 schwartzL1E tensorSize tensorConjSlice
  calc
    (∫⁻ x : ℝ, ‖(∑ i, conj (a i t) • conjSchwartz (b i)) x‖ₑ) ≤
        ∫⁻ x : ℝ, ∑ i, ‖(conj (a i t) • conjSchwartz (b i)) x‖ₑ := by
      apply lintegral_mono
      intro x
      exact enorm_sum_le Finset.univ (fun i => (conj (a i t) • conjSchwartz (b i)) x)
    _ = ∑ i, ∫⁻ x : ℝ, ‖(conj (a i t) • conjSchwartz (b i)) x‖ₑ := by
      rw [lintegral_finset_sum]
      intro i hi
      fun_prop
    _ = ∑ i, ‖a i t‖ₑ * ∫⁻ x : ℝ, ‖conjSchwartz (b i) x‖ₑ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_apply, enorm_smul, enorm_conj]
      rw [lintegral_const_mul']
      exact enorm_ne_top

lemma tensorSliceL1_memLp {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    MemLp (tensorSliceL1 a b) (4 / 3) volume := by
  have hsize_meas : AEStronglyMeasurable (tensorSize a b) volume := by
    apply Measurable.aestronglyMeasurable
    unfold tensorSize
    fun_prop
  refine ⟨(tensorSliceL1_measurable a b).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (eLpNorm_mono_enorm (fun t => by
    simpa only [enorm_eq_self] using tensorSliceL1_le_size a b t))
  apply lt_of_le_of_lt (eLpNorm_sum_le (s := Finset.univ) (fun i hi => by
    fun_prop) (by norm_num))
  apply ENNReal.sum_lt_top
  intro i hi
  rw [show (fun t : ℝ => ‖a i t‖ₑ * schwartzL1E (conjSchwartz (b i))) =
      fun t => schwartzL1E (conjSchwartz (b i)) * ‖a i t‖ₑ by
    funext t
    ring]
  rw [eLpNorm_ennreal_const_mul volume _ (schwartzL1E_ne_top _) _ (4 / 3)
    (by norm_num) (by norm_num), eLpNorm_enorm]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (schwartzL1E_ne_top _))
    ((a i).memLp (4 / 3) volume).2

lemma freeKernelOp_schwartz_bound (t x : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖freeKernelOp t f x‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E f := by
  unfold freeKernelOp schwartzL1E
  calc
    ‖∫ y : ℝ, freeKernel t x y * f y‖ₑ ≤
        ∫⁻ y : ℝ, ‖freeKernel t x y * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y : ℝ,
        ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * ‖f y‖ₑ := by
      apply lintegral_congr
      intro y
      rw [enorm_mul, enorm_freeKernel]
    _ = ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) *
        ∫⁻ y : ℝ, ‖f y‖ₑ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top

lemma inner_freeProp_schwartz_bound (t : ℝ) (f g : SchwartzMap ℝ ℂ) (ht : t ≠ 0) :
    ‖@inner ℂ L2 _ (f.toLp 2 volume) (freeProp t (g.toLp 2 volume))‖ₑ ≤
      schwartzL1E f *
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E g) := by
  rw [MeasureTheory.L2.inner_def]
  have hfcoe : (⇑(f.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume] f :=
    (f.memLp 2 volume).coeFn_toLp
  have hgker := free_kernel_explicit t ht g
  calc
    ‖∫ x : ℝ, @inner ℂ ℂ _ ((f.toLp 2 volume) x)
        ((freeProp t (g.toLp 2 volume)) x)‖ₑ ≤
        ∫⁻ x : ℝ, ‖@inner ℂ ℂ _ ((f.toLp 2 volume) x)
          ((freeProp t (g.toLp 2 volume)) x)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ * ‖freeKernelOp t g x‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [hfcoe, hgker] with x hfx hgx
      rw [hfx, hgx]
      simp only [RCLike.inner_apply, conj_toReal, ofReal_zero, mul_zero, zero_add,
        enorm_mul, enorm_conj]
    _ ≤ ∫⁻ x : ℝ, ‖f x‖ₑ *
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E g) := by
      apply lintegral_mono
      intro x
      exact mul_le_mul_left' (freeKernelOp_schwartz_bound t x g) _
    _ = schwartzL1E f *
        (ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) * schwartzL1E g) := by
      unfold schwartzL1E
      rw [lintegral_mul_const'']
      exact f.continuous.enorm.aemeasurable

lemma inner_integral_left {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] (f : X → E) (hf : Integrable f) (c : E) :
    @inner ℂ E _ (∫ x, f x) c = ∫ x, @inner ℂ E _ (f x) c := by
  symm
  exact (innerSLFlip ℂ c).integral_comp_comm hf

lemma inner_tensorAdjoint_double {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    @inner ℂ L2 _ (tensorAdjoint a b) (tensorAdjoint a b) =
      ∫ s : ℝ, ∫ r : ℝ,
        @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r) := by
  have hcur := tensorAdjointCurve_integrable a b
  rw [tensorAdjoint, inner_integral_left _ hcur]
  apply integral_congr_ae
  filter_upwards with s
  exact (innerSL ℂ (tensorAdjointCurve a b s)).integral_comp_comm hcur |>.symm

lemma inner_tensorAdjointCurve_bound {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ)
    (s r : ℝ) (hsr : s ≠ r) :
    ‖@inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ ≤
      tensorSliceL1 a b s *
        (ENNReal.ofReal ((4 * Real.pi * |s - r|) ^ (-(1 / 2 : ℝ))) *
          tensorSliceL1 a b r) := by
  have htime : s - r ≠ 0 := sub_ne_zero.mpr hsr
  have hinner :
      @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r) =
        @inner ℂ L2 _ ((tensorConjSlice a b s).toLp 2 volume)
          (freeProp (s - r) ((tensorConjSlice a b r).toLp 2 volume)) := by
    unfold tensorAdjointCurve
    rw [← inner_freeProp s]
    congr 1
    · rw [propagator_unitary.2.1]
      convert propagator_unitary.2.2.1 _ using 1
      ring
    · rw [propagator_unitary.2.1]
      congr 2
      ring
  rw [hinner]
  exact inner_freeProp_schwartz_bound (s - r)
    (tensorConjSlice a b s) (tensorConjSlice a b r) htime

def tensorG {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (tensorRaw a b p)

lemma tensorG_measurable {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    Measurable (tensorG a b) := by
  unfold tensorG tensorRaw
  fun_prop

lemma spatialL1_tensorG {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) (t : ℝ) :
    spatialL1 (tensorG a b) t = tensorSliceL1 a b t := by
  unfold spatialL1 tensorSliceL1 schwartzL1E tensorG
  apply lintegral_congr
  intro x
  rw [tensorConjSlice_apply]

lemma lintegral_mul_le_eLpNorm_four_thirds_four
    (q F : ℝ → ℝ≥0∞) (hq : AEMeasurable q volume) (hF : AEMeasurable F volume) :
    ∫⁻ t : ℝ, q t * F t ≤ eLpNorm q (4 / 3) volume * eLpNorm F 4 volume := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (4 / 3 : ℝ).HolderConjugate 4 by
      rw [Real.holderConjugate_iff]
      constructor <;> norm_num)
    hq hF
  simpa only [Pi.mul_apply,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 / 3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 / 3 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, one_div_div] using hh

lemma freeKernel_time_factor (t : ℝ) :
    ENNReal.ofReal ((4 * Real.pi * |t|) ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (|t| ^ (-(1 / 2 : ℝ))) := by
  rw [show 4 * Real.pi * |t| = (4 * Real.pi) * |t| by ring]
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (abs_nonneg t)]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]

/- The first version of the assembled estimate is retained temporarily below
for comparison while its proof is split into small, separately compiled
lemmas in `StrichartzDuality`.  It is not part of the Lean environment. -/
/-
set_option maxHeartbeats 10000000 in
theorem tensorAdjoint_sq_estimate :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ (n : ℕ) (a b : Fin n → SchwartzMap ℝ ℂ),
      ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
        D * eLpNorm (tensorSliceL1 a b) (4 / 3) volume ^ (2 : ℕ) := by
  have hp : (1 : ℝ≥0∞) < 4 / 3 := by
    rw [← ENNReal.toReal_lt_toReal (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  have hpq : (4 / 3 : ℝ≥0∞) < 4 := by
    rw [← ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)]
    norm_num
  have hexp : (4 : ℝ≥0∞)⁻¹ =
      (4 / 3 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (1 / 2 : ℝ) := by
    have hl : (4 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
    have hdiv : (4 / 3 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvtop : (4 / 3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hdiv
    have hr : (4 / 3 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.sub_ne_top hinvtop
    have hle : ENNReal.ofReal (1 / 2 : ℝ) ≤ (4 / 3 : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.toReal_le_toReal (by norm_num) hinvtop]
      norm_num
    apply le_antisymm
    · rw [← ENNReal.toReal_le_toReal hl hr,
        ENNReal.toReal_sub_of_le hle hinvtop]
      norm_num
    · rw [← ENNReal.toReal_le_toReal hr hl,
        ENNReal.toReal_sub_of_le hle hinvtop]
      norm_num
  obtain ⟨Ch, hChtop, hHLS⟩ := HLS_time (1 / 2) (by norm_num) (by norm_num)
    (4 / 3) 4 hp hpq (by norm_num) (by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
      exact hexp)
  let c : ℝ≥0∞ := ENNReal.ofReal ((4 * Real.pi) ^ (-(1 / 2 : ℝ)))
  refine ⟨c * Ch, ENNReal.mul_lt_top (by simp [c]) hChtop, ?_⟩
  intro n a b
  let G : ℝ × ℝ → ℂ := tensorG a b
  let q : ℝ → ℝ≥0∞ := tensorSliceL1 a b
  have hG : Measurable G := tensorG_measurable a b
  have hq : Measurable q := tensorSliceL1_measurable a b
  have hfinite (t : ℝ) : spatialL1 G t ≠ ⊤ := by
    rw [show spatialL1 G t = q t by exact spatialL1_tensorG a b t]
    exact schwartzL1E_ne_top _
  have hmix : scalarMixedENorm volume volume (4 / 3) 1 G < ⊤ := by
    rw [← spatialL1Complex_eLpNorm G hfinite]
    have heq : eLpNorm (spatialL1Complex G) (4 / 3) volume =
        eLpNorm q (4 / 3) volume := by
      apply eLpNorm_congr_enorm_ae
      filter_upwards with t
      rw [spatialL1Complex_enorm G hfinite]
      exact (spatialL1_tensorG a b t).trans (enorm_eq_self _).symm
    rw [heq]
    exact (tensorSliceL1_memLp a b).2
  have hqcomplex := spatialL1Complex_memLp G hG hfinite hmix
  have hfrac := hHLS (spatialL1Complex G) hqcomplex
  have hfracmeas : AEMeasurable
      (fractionalIntegral (1 / 2) (spatialL1Complex G)) volume :=
    (fractionalIntegral_measurable (1 / 2) (spatialL1Complex G)
      hqcomplex.1).aemeasurable
  have hdouble : ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
      c * ∫⁻ s : ℝ, q s * fractionalIntegral (1 / 2) (spatialL1Complex G) s := by
    rw [← enorm_norm, ← enorm_pow, inner_self_eq_norm_sq_to_K,
      inner_tensorAdjoint_double]
    calc
      ‖∫ s : ℝ, ∫ r : ℝ,
          @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ ≤
          ∫⁻ s : ℝ, ‖∫ r : ℝ,
            @inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s : ℝ, ∫⁻ r : ℝ,
          ‖@inner ℂ L2 _ (tensorAdjointCurve a b s) (tensorAdjointCurve a b r)‖ₑ := by
        apply lintegral_mono
        intro s
        exact enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s : ℝ, ∫⁻ r : ℝ, q s *
          (ENNReal.ofReal ((4 * Real.pi * |s - r|) ^ (-(1 / 2 : ℝ))) * q r) := by
        apply lintegral_mono_ae
        filter_upwards with s
        apply lintegral_mono_ae
        rw [ae_iff]
        have hsingle : volume {s} = 0 := measure_singleton s
        filter_upwards [show ∀ᵐ r : ℝ ∂volume, r ≠ s by
          rw [ae_iff]
          simpa only [Set.setOf_not_ne, Set.singleton_eq_singleton_iff] using hsingle] with r hrs
        exact inner_tensorAdjointCurve_bound a b s r (Ne.symm hrs)
      _ = c * ∫⁻ s : ℝ, q s *
          fractionalIntegral (1 / 2) (spatialL1Complex G) s := by
        simp_rw [freeKernel_time_factor, ← spatialL1_tensorG a b,
          ← fractionalIntegral_spatialL1 G hfinite]
        simp_rw [show ∀ s r : ℝ, spatialL1 G s *
            (c * ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r) =
            c * (spatialL1 G s *
              (ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r)) by
          intro s r
          ring]
        rw [show (∫⁻ s : ℝ, ∫⁻ r : ℝ, c *
              (spatialL1 G s *
                (ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) * spatialL1 G r))) =
            c * ∫⁻ s : ℝ, spatialL1 G s *
              (∫⁻ r : ℝ, ENNReal.ofReal (|s - r| ^ (-(1 / 2 : ℝ))) *
                spatialL1 G r) by
          simp_rw [lintegral_const_mul' _ _ (by simp [c] : c ≠ ⊤),
            lintegral_const_mul' _ _ (hfinite _), mul_assoc]]
        congr 1
        apply lintegral_congr
        intro s
        rw [fractionalIntegral_spatialL1 G hfinite]
        rw [spatialL1_tensorG]
  calc
    ‖tensorAdjoint a b‖ₑ ^ (2 : ℕ) ≤
        c * ∫⁻ s : ℝ, q s * fractionalIntegral (1 / 2) (spatialL1Complex G) s := hdouble
    _ ≤ c * (eLpNorm q (4 / 3) volume *
        eLpNorm (fractionalIntegral (1 / 2) (spatialL1Complex G)) 4 volume) := by
      gcongr
      exact lintegral_mul_le_eLpNorm_four_thirds_four q _ hq.aemeasurable hfracmeas
    _ ≤ c * (eLpNorm q (4 / 3) volume *
        (Ch * eLpNorm (spatialL1Complex G) (4 / 3) volume)) := by
      gcongr
    _ = (c * Ch) * eLpNorm q (4 / 3) volume ^ (2 : ℕ) := by
      have heq : eLpNorm (spatialL1Complex G) (4 / 3) volume =
          eLpNorm q (4 / 3) volume := by
        apply eLpNorm_congr_enorm_ae
        filter_upwards with t
        rw [spatialL1Complex_enorm G hfinite, spatialL1_tensorG]
        exact (enorm_eq_self _).symm
      rw [heq]
      ring

theorem tensorAdjoint_estimate :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (n : ℕ) (a b : Fin n → SchwartzMap ℝ ℂ),
      ‖tensorAdjoint a b‖ₑ ≤ C * eLpNorm (tensorSliceL1 a b) (4 / 3) volume := by
  obtain ⟨D, hDtop, hD⟩ := tensorAdjoint_sq_estimate
  let C : ℝ≥0∞ := D ^ (1 / 2 : ℝ)
  refine ⟨C, ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDtop.ne, ?_⟩
  intro n a b
  let x : ℝ≥0∞ := ‖tensorAdjoint a b‖ₑ
  let y : ℝ≥0∞ := eLpNorm (tensorSliceL1 a b) (4 / 3) volume
  have hs := ENNReal.rpow_le_rpow (hD n a b) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change x ≤ C * y
  calc
    x = (x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (D * y ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := hs
    _ = C * y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul]
      norm_num
-/

-/
end CubicNLSPhaseRetrieval
