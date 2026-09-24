import Lean_Code.ScalarMixedNorms
import Lean_Code.EndpointCompleteness
import Lean_Code.EndpointIdentification
import Lean_Code.FractionalIntegration
import Lean_Code.StrichartzFiniteEndpoint

/-!
# One-dimensional Strichartz estimates

Blueprint chapter: `chap:strichartz` (module 4).
Imports: modules 0, 2, and 3.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

set_option maxHeartbeats 2000000 in
/-- Extension of the endpoint homogeneous estimate from Schwartz data to all
of `L²`.  The proof uses the explicit scalar mixed-norm completion and the
almost-everywhere identification lemma, rather than a nonseparable Bochner
duality argument. -/
theorem hom_strichartz_four_top_of_schwartz
    (C : ℝ≥0∞) (hCtop : C < ⊤)
    (hschwartz : ∀ φ : SchwartzMap ℝ ℂ,
      scalarMixedENorm volume volume 4 ⊤
          (curveRepresentative fun t => freeProp t (φ.toLp 2 volume)) ≤
        C * ENNReal.ofReal ‖φ.toLp 2 volume‖) :
    ∀ f : L2, scalarMixedENorm volume volume 4 ⊤
        (curveRepresentative fun t => freeProp t f) ≤ C * ENNReal.ofReal ‖f‖ := by
  intro f
  let L : SchwartzMap ℝ ℂ →L[ℂ] L2 := SchwartzMap.toLpCLM ℂ ℂ 2 volume
  have hLdense : DenseRange L :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  have hrad (n : ℕ) : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  choose φ hφ using fun n => hLdense.exists_dist_lt f (hrad n)
  let fn : ℕ → L2 := fun n => L (φ n)
  have hfn : Tendsto fn atTop (𝓝 f) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Metric.tendsto_atTop] at hzero
    obtain ⟨N, hN⟩ := hzero ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hsmall : (1 : ℝ) / (n + 1) < ε := by
      have := hN n hn
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (hrad n)] using this
    have hφn := hφ n
    rw [dist_comm] at hφn
    exact hφn.trans hsmall
  let W : ℕ → ℝ × ℝ → ℂ := fun n =>
    Classical.choose (joint_representative_L2_measurable volume
      (fun t => freeProp t (fn n))
      ((propagator_unitary.2.2.2.1 (fn n))).aestronglyMeasurable)
  have hWmeas (n : ℕ) : Measurable (W n) :=
    (Classical.choose_spec (joint_representative_L2_measurable volume
      (fun t => freeProp t (fn n))
      ((propagator_unitary.2.2.2.1 (fn n))).aestronglyMeasurable)).1
  have hWslice (n : ℕ) : ∀ᵐ t : ℝ ∂volume,
      (fun x => W n (t, x)) =ᵐ[volume]
        (freeProp t (fn n) : ℝ → ℂ) :=
    (Classical.choose_spec (joint_representative_L2_measurable volume
      (fun t => freeProp t (fn n))
      ((propagator_unitary.2.2.2.1 (fn n))).aestronglyMeasurable)).2
  have hmixed_eq (m n : ℕ) :
      scalarMixedENorm volume volume 4 ⊤ (fun z => W m z - W n z) =
        scalarMixedENorm volume volume 4 ⊤
          (fun z => curveRepresentative (fun t => freeProp t (fn m)) z -
            curveRepresentative (fun t => freeProp t (fn n)) z) := by
    unfold scalarMixedENorm sectionENorm
    apply eLpNorm_congr_ae
    filter_upwards [hWslice m, hWslice n] with t hmt hnt
    apply eLpNorm_congr_ae
    filter_upwards [hmt, hnt] with x hmx hnx
    simp only [curveRepresentative, Prod.fst, Prod.snd, hmx, hnx]
  have hsingle_eq (n : ℕ) :
      scalarMixedENorm volume volume 4 ⊤ (W n) =
        scalarMixedENorm volume volume 4 ⊤
          (curveRepresentative fun t => freeProp t (fn n)) := by
    unfold scalarMixedENorm sectionENorm
    apply eLpNorm_congr_ae
    filter_upwards [hWslice n] with t ht
    exact eLpNorm_congr_ae ht
  have hbound (n : ℕ) :
      scalarMixedENorm volume volume 4 ⊤
          (curveRepresentative fun t => freeProp t (fn n)) ≤
        C * ENNReal.ofReal ‖fn n‖ := by
    simpa only [fn, L, SchwartzMap.toLpCLM_apply] using hschwartz (φ n)
  have hWmem (n : ℕ) : MemScalarMixed volume volume 4 ⊤ (W n) := by
    refine ⟨(hWmeas n).aestronglyMeasurable, ?_⟩
    rw [hsingle_eq n]
    exact (hbound n).trans_lt
      (ENNReal.mul_lt_top hCtop (by finiteness))
  have hfnCauchy : CauchySeq fn := hfn.cauchySeq
  have hWCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      scalarMixedENorm volume volume 4 ⊤ (fun z => W m z - W n z) <
        ENNReal.ofReal ε := by
    intro ε hε
    let δ : ℝ := ε / (C.toReal + 1)
    have hden : 0 < C.toReal + 1 := by positivity
    have hδ : 0 < δ := div_pos hε hden
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hfnCauchy) δ hδ
    refine ⟨N, fun m n hm hn => ?_⟩
    rw [hmixed_eq]
    have hflow :
        scalarMixedENorm volume volume 4 ⊤
            (fun z => curveRepresentative (fun t => freeProp t (fn m)) z -
              curveRepresentative (fun t => freeProp t (fn n)) z) =
          scalarMixedENorm volume volume 4 ⊤
            (curveRepresentative fun t => freeProp t (fn m - fn n)) := by
      unfold scalarMixedENorm sectionENorm
      apply eLpNorm_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      apply eLpNorm_congr_ae
      simp only [curveRepresentative]
      rw [freeProp_sub]
      filter_upwards [Lp.coeFn_sub (freeProp t (fn m)) (freeProp t (fn n))] with x hx
      simpa only [Pi.sub_apply] using hx.symm
    rw [hflow]
    have hmn :
        scalarMixedENorm volume volume 4 ⊤
            (curveRepresentative fun t => freeProp t (fn m - fn n)) ≤
          C * ENNReal.ofReal ‖fn m - fn n‖ := by
      have htoLp : (φ m - φ n).toLp 2 volume =
          (φ m).toLp 2 volume - (φ n).toLp 2 volume := by
        change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (φ m - φ n) = _
        rw [map_sub]
        rfl
      simpa only [fn, L, SchwartzMap.toLpCLM_apply, htoLp] using
        hschwartz (φ m - φ n)
    apply lt_of_le_of_lt hmn
    have hdist : ‖fn m - fn n‖ < δ := by
      simpa only [dist_eq_norm] using hN m hm n hn
    calc
      C * ENNReal.ofReal ‖fn m - fn n‖ ≤
          ENNReal.ofReal (C.toReal + 1) * ENNReal.ofReal ‖fn m - fn n‖ := by
        apply mul_le_mul_right'
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num)]
        simp only [ENNReal.ofReal_toReal hCtop.ne, ENNReal.ofReal_one]
        exact self_le_add_right C 1
      _ = ENNReal.ofReal ((C.toReal + 1) * ‖fn m - fn n‖) := by
        rw [ENNReal.ofReal_mul hden.le]
      _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        rw [show ε = (C.toReal + 1) * δ by
          dsimp [δ]
          field_simp]
        exact mul_lt_mul_of_pos_left hdist hden
  obtain ⟨H, hH, hWH⟩ :=
    scalar_endpoint_complete volume volume 4 (by norm_num) (by norm_num)
      W hWmeas hWmem hWCauchy
  have hcanonical_conv : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      scalarMixedENorm volume volume 4 ⊤
        (fun p => curveRepresentative (fun t => freeProp t (fn n)) p - H p) <
          ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hWH ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [show scalarMixedENorm volume volume 4 ⊤
        (fun p => curveRepresentative (fun t => freeProp t (fn n)) p - H p) =
      scalarMixedENorm volume volume 4 ⊤ (fun p => W n p - H p) by
        unfold scalarMixedENorm sectionENorm
        apply eLpNorm_congr_ae
        filter_upwards [hWslice n] with t ht
        apply eLpNorm_congr_ae
        filter_upwards [ht] with x hx
        simp only [curveRepresentative, Prod.fst, Prod.snd, hx]]
    exact hN n hn
  exact (strichartz_endpoint_identification f fn hfn H hH hcanonical_conv C hCtop hbound).2

/-- The scalar endpoint estimate obtained from the explicit tensor `TT*`
argument on Schwartz data and the `L²` density theorem above. -/
theorem TTstar_endpoint :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : L2,
    scalarMixedENorm volume volume 4 ⊤
        (curveRepresentative fun t => freeProp t f) ≤
      C * ENNReal.ofReal ‖f‖ := by
  obtain ⟨C, hCtop, hschwartz⟩ := schwartz_free_endpoint_estimate
  refine ⟨C, hCtop, hom_strichartz_four_top_of_schwartz C hCtop ?_⟩
  intro φ
  rw [curveRepresentative_schwartz_mixed_eq]
  exact hschwartz φ

/-- The homogeneous endpoint estimate used by the nonlinear and
phase-retrieval arguments. -/
theorem hom_strichartz :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : L2,
    scalarMixedENorm volume volume 4 ⊤
      (curveRepresentative fun t => freeProp t f) ≤ C * ENNReal.ofReal ‖f‖ := by
  exact TTstar_endpoint

section ChristKiselev

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Full Banach-valued integral operator on a measurable time set. -/
def fullKernelOp (I : Set ℝ) (K : ℝ → ℝ → A →L[ℝ] B) (F : ℝ → A) (t : ℝ) : B :=
  ∫ s in I, K t s (F s)

/-- Retarded restriction of a Banach-valued integral operator. -/
def retardedKernelOp (I : Set ℝ) (K : ℝ → ℝ → A →L[ℝ] B)
    (F : ℝ → A) (t : ℝ) : B :=
  ∫ s in I ∩ Set.Iio t, K t s (F s)

end ChristKiselev

/-- A rough forcing/output pair is the completion of classical retarded Duhamel integrals. -/
def IsRetardedDuhamelCompletion (I : Set ℝ) (t0 : ℝ) (F : ℝ × ℝ → ℂ)
    (R : ℝ → L2) : Prop :=
  ∃ Fn : ℕ → ℝ → L2,
    (∀ n t, t ∈ I →
      IntervalIntegrable (fun s => freeProp (t - s) (Fn n s)) volume t0 t) ∧
    Tendsto (fun n => eLpNorm ((I ×ˢ (Set.univ : Set ℝ)).indicator
      (fun p => curveRepresentative (Fn n) p - F p)) (6 / 5) (volume.prod volume))
      atTop (𝓝 0) ∧
    Tendsto (fun n =>
      scalarMixedENorm (volume.restrict I) volume 6 6
        (curveRepresentative (fun t =>
          (∫ s in t0..t, freeProp (t - s) (Fn n s)) - R t)) +
      scalarMixedENorm (volume.restrict I) volume ⊤ 2
        (curveRepresentative (fun t =>
          (∫ s in t0..t, freeProp (t - s) (Fn n s)) - R t)))
      atTop (𝓝 0)

end CubicNLSPhaseRetrieval
