import Mathlib
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Scalar mixed norms and representatives

Blueprint chapter: `chap:mixed-norms` (module 0).
Imports: Mathlib only.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

section MixedNorms

variable {τ χ : Type*} [MeasurableSpace τ] [MeasurableSpace χ]

/-- `conv:joint-representatives`: product-a.e. scalar spacetime functions. -/
abbrev ScalarSpacetime (μt : Measure τ) (μx : Measure χ) :=
  MeasureTheory.AEEqFun (τ × χ) ℂ (μt.prod μx)

/-- Spatial section `L^q` seminorm, including the `q = ∞` endpoint. -/
def sectionENorm (μx : Measure χ) (q : ℝ≥0∞) (f : τ × χ → ℂ) (t : τ) : ℝ≥0∞ :=
  eLpNorm (fun x => f (t, x)) q μx

/-- `def:scalar-mixed-norm`: the scalar `L^p_t L^q_x` extended norm. -/
def scalarMixedENorm (μt : Measure τ) (μx : Measure χ) (p q : ℝ≥0∞)
    (f : τ × χ → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun t => sectionENorm μx q f t) p μt

/-- Finite membership in the scalar mixed-norm space. -/
def MemScalarMixed (μt : Measure τ) (μx : Measure χ) (p q : ℝ≥0∞)
    (f : τ × χ → ℂ) : Prop :=
  AEStronglyMeasurable f (μt.prod μx) ∧ scalarMixedENorm μt μx p q f < ⊤

/-- Restricting a scalar spacetime function pointwise cannot increase any
mixed seminorm. -/
theorem scalarMixedENorm_indicator_le (μt : Measure τ) (μx : Measure χ)
    (p q : ℝ≥0∞) (E : Set (τ × χ)) (f : τ × χ → ℂ) :
    scalarMixedENorm μt μx p q (E.indicator f) ≤
      scalarMixedENorm μt μx p q f := by
  unfold scalarMixedENorm sectionENorm
  apply eLpNorm_mono_enorm
  intro t
  apply eLpNorm_mono_enorm
  intro x
  by_cases hx : (t, x) ∈ E
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- `lem:measurable-esssup-section`: measurability of the endpoint section norm. -/
theorem measurable_esssup_section (_μt : Measure τ) (μx : Measure χ) [SFinite μx]
    (f : τ × χ → ℂ) (hf : Measurable f) :
    Measurable (fun t => sectionENorm μx ⊤ f t) := by
  simp_rw [sectionENorm, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  apply measurable_of_Ioi
  intro a
  let S : Set (τ × χ) := {p | a < ‖f p‖ₑ}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.enorm
  have hm : Measurable (fun t => μx ((Prod.mk t) ⁻¹' S)) :=
    measurable_measure_prodMk_left hS
  have heq :
      (fun t => essSup (fun x => ‖f (t, x)‖ₑ) μx) ⁻¹' Set.Ioi a =
        (fun t => μx ((Prod.mk t) ⁻¹' S)) ⁻¹' Set.Ioi 0 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro ha
      apply pos_iff_ne_zero.mpr
      change μx {x | a < ‖f (t, x)‖ₑ} ≠ 0
      rw [← frequently_ae_iff]
      simpa only [essSup] using
        (frequently_lt_of_lt_limsup (u := fun x => ‖f (t, x)‖ₑ)
          (f := ae μx) (by isBoundedDefault) (by simpa only [essSup] using ha))
    · intro hpos
      by_contra hnot
      have hle : essSup (fun x => ‖f (t, x)‖ₑ) μx ≤ a := le_of_not_gt hnot
      have hfreq : ∃ᵐ x ∂μx, a < ‖f (t, x)‖ₑ := by
        rw [frequently_ae_iff]
        simpa only [S, Set.preimage_setOf_eq] using ne_of_gt hpos
      have hae : ∀ᵐ x ∂μx, ‖f (t, x)‖ₑ ≤ a :=
        (ENNReal.ae_le_essSup (fun x => ‖f (t, x)‖ₑ)).mono
          (fun _ hx => hx.trans hle)
      obtain ⟨x, hx⟩ := (hfreq.and_eventually hae).exists
      exact (not_lt_of_ge hx.2) hx.1
  rw [heq]
  exact hm measurableSet_Ioi

theorem scalarMixedENorm_sub_le_add (μt : Measure τ) (μx : Measure χ)
    [SFinite μx] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f g h : τ × χ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) :
    scalarMixedENorm μt μx p ⊤ (fun z => f z - g z) ≤
      scalarMixedENorm μt μx p ⊤ (fun z => f z - h z) +
        scalarMixedENorm μt μx p ⊤ (fun z => h z - g z) := by
  let A : τ → ℝ≥0∞ := fun t => sectionENorm μx ⊤ (fun z => f z - h z) t
  let B : τ → ℝ≥0∞ := fun t => sectionENorm μx ⊤ (fun z => h z - g z) t
  have hA : Measurable A :=
    measurable_esssup_section μt μx (fun z => f z - h z) (hf.sub hh)
  have hB : Measurable B :=
    measurable_esssup_section μt μx (fun z => h z - g z) (hh.sub hg)
  have hpoint : ∀ t,
      sectionENorm μx ⊤ (fun z => f z - g z) t ≤ A t + B t := by
    intro t
    have hfs : AEStronglyMeasurable (fun x => f (t, x) - h (t, x)) μx :=
      ((hf.sub hh).comp measurable_prodMk_left).aestronglyMeasurable
    have hgs : AEStronglyMeasurable (fun x => h (t, x) - g (t, x)) μx :=
      ((hh.sub hg).comp measurable_prodMk_left).aestronglyMeasurable
    change eLpNorm (fun x => f (t, x) - g (t, x)) ⊤ μx ≤ _
    rw [show (fun x => f (t, x) - g (t, x)) =
        (fun x => f (t, x) - h (t, x)) + (fun x => h (t, x) - g (t, x)) by
      funext x
      simp only [Pi.add_apply]
      ring]
    exact eLpNorm_add_le hfs hgs (by simp)
  calc
    scalarMixedENorm μt μx p ⊤ (fun z => f z - g z) ≤ eLpNorm (A + B) p μt := by
      apply eLpNorm_mono_enorm
      intro t
      simpa only [Pi.add_apply, enorm_eq_self] using hpoint t
    _ ≤ eLpNorm A p μt + eLpNorm B p μt :=
      eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable hp
    _ = _ := rfl

theorem ae_tsum_ennreal_lt_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (d : ℕ → X → ℝ≥0∞) (hd : ∀ n, Measurable (d n))
    (hsum : (∑' n, eLpNorm (d n) p μ) ≠ ⊤) :
    ∀ᵐ x ∂μ, (∑' n, d n x) < ⊤ := by
  have hp_lt : p < ⊤ := lt_top_iff_ne_top.mpr hp_top
  have hfinite (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) :
      ∀ᵐ x ∂μ, x ∈ s → (∑' n, d n x) < ⊤ := by
    rw [← ae_restrict_iff' hs]
    apply ae_lt_top' (AEMeasurable.tsum fun i => (hd i).aemeasurable.restrict)
    rw [lintegral_tsum fun i => (hd i).aemeasurable.restrict]
    apply ne_of_lt
    have hbound : (∑' n, eLpNorm (d n) p (μ.restrict s) *
        (μ.restrict s) Set.univ ^ (1 / ENNReal.toReal 1 - 1 / p.toReal)) < ⊤ := by
      rw [ENNReal.tsum_mul_right]
      apply ENNReal.mul_lt_top
      · apply lt_of_le_of_lt _ hsum.lt_top
        gcongr with n
        exact Measure.restrict_le_self
      · simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
          ENNReal.toReal_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_div]
        apply ENNReal.rpow_lt_top_of_nonneg _ hμs
        simp only [sub_nonneg]
        apply inv_le_one_of_one_le₀
        rw [← ENNReal.ofReal_le_iff_le_toReal hp_lt.ne]
        simpa
    apply lt_of_le_of_lt _ hbound
    gcongr with i
    simpa only [eLpNorm_one_eq_lintegral_enorm, enorm_eq_self] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp
        (hd i).aestronglyMeasurable.restrict)
  have hlocal : ∀ᵐ x ∂μ, ∀ n,
      x ∈ spanningSets μ n → (∑' i, d i x) < ⊤ := by
    apply ae_all_iff.2
    intro n
    exact hfinite _ (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n).ne
  filter_upwards [hlocal] with x hx
  exact hx (spanningSetsIndex μ x) (mem_spanningSetsIndex μ x)

/- `lem:mixed-subsequence-uniform`: summable endpoint section differences a.e. -/
set_option maxHeartbeats 800000 in
theorem mixed_subsequence_uniform (μt : Measure τ) (μx : Measure χ)
    [SigmaFinite μt] [SFinite μx] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (F : ℕ → τ × χ → ℂ) (f : τ × χ → ℂ)
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      scalarMixedENorm μt μx p ⊤ (fun z => F n z - f z) < ENNReal.ofReal ε) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ t : τ ∂μt,
    (∑' k : ℕ, sectionENorm μx ⊤
      (fun z => F (φ (k + 1)) z - F (φ k) z) t) < ⊤ := by
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n + 2)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  choose N hN using fun n => hconv (ε n) (hεpos n)
  let φ : ℕ → ℕ := fun n => Nat.rec (N 0) (fun k m => max (N (k + 1)) (m + 1)) n
  have hφstep (n : ℕ) : φ (n + 1) = max (N (n + 1)) (φ n + 1) := by
    simp [φ]
  have hφN (n : ℕ) : N n ≤ φ n := by
    cases n with
    | zero => simp [φ]
    | succ n => rw [hφstep]; exact le_max_left _ _
  have hφmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hφstep]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let D : ℕ → τ → ℝ≥0∞ := fun k t => sectionENorm μx ⊤
    (fun z => F (φ (k + 1)) z - F (φ k) z) t
  have hDmeas (k : ℕ) : Measurable (D k) := by
    exact measurable_esssup_section μt μx
      (fun z => F (φ (k + 1)) z - F (φ k) z)
      ((hF _).sub (hF _))
  have hDbound (k : ℕ) : eLpNorm (D k) p μt ≤
      ENNReal.ofReal (ε (k + 1)) + ENNReal.ofReal (ε k) := by
    calc
      eLpNorm (D k) p μt = scalarMixedENorm μt μx p ⊤
          (fun z => F (φ (k + 1)) z - F (φ k) z) := rfl
      _ ≤ scalarMixedENorm μt μx p ⊤ (fun z => F (φ (k + 1)) z - f z) +
          scalarMixedENorm μt μx p ⊤ (fun z => f z - F (φ k) z) :=
        scalarMixedENorm_sub_le_add μt μx p hp _ _ _ (hF _) (hF _) hf
      _ = scalarMixedENorm μt μx p ⊤ (fun z => F (φ (k + 1)) z - f z) +
          scalarMixedENorm μt μx p ⊤ (fun z => F (φ k) z - f z) := by
        congr 1
        unfold scalarMixedENorm sectionENorm
        congr 1
        funext t
        rw [show (fun x => f (t, x) - F (φ k) (t, x)) =
            -(fun x => F (φ k) (t, x) - f (t, x)) by
          funext x
          simp]
        exact eLpNorm_neg _ _ _
      _ ≤ ENNReal.ofReal (ε (k + 1)) + ENNReal.ofReal (ε k) := by
        gcongr
        · exact (hN (k + 1) (φ (k + 1)) (hφN (k + 1))).le
        · exact (hN k (φ k) (hφN k)).le
  have hsum : (∑' k, eLpNorm (D k) p μt) ≠ ⊤ := by
    apply ne_of_lt
    calc
      (∑' k, eLpNorm (D k) p μt) ≤
          ∑' k, (ENNReal.ofReal (ε (k + 1)) + ENNReal.ofReal (ε k)) := by
        gcongr with k
        exact hDbound k
      _ < ⊤ := by
        rw [ENNReal.tsum_add]
        simp only [ε, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2⁻¹),
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num only [ENNReal.ofReal_ofNat]
        simp_rw [show ∀ a : ℕ, a + 1 + 2 = 3 + a by omega,
          show ∀ a : ℕ, a + 2 = 2 + a by omega, pow_add]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        norm_num only [ENNReal.one_sub_inv_two, inv_inv]
        finiteness
  exact ⟨φ, hφmono, ae_tsum_ennreal_lt_top μt p hp hp_top D hDmeas hsum⟩

end MixedNorms

/-- `lem:C0-limit-identification`: a uniform `C₀` limit is the L² limit representative. -/
theorem C0_limit_identification (f : Lp ℂ 2 (volume : Measure ℝ))
    (fn : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hcont : ∀ n, Continuous (fn n))
    (hvanish : ∀ n, Tendsto (fn n) atTop (𝓝 0) ∧ Tendsto (fn n) atBot (𝓝 0))
    (hmem : ∀ n, MemLp (fn n) 2 volume)
    (hL2 : Tendsto (fun n => (hmem n).toLp (fn n)) atTop (𝓝 f))
    (huniform : TendstoUniformly fn g atTop) :
  Continuous g ∧ Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0) ∧
    (f : ℝ → ℂ) =ᵐ[volume] g := by
  have hgcont : Continuous g := huniform.continuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall hcont))
  have hgtop : Tendsto g atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp huniform (ε / 2) hhalf).exists
    filter_upwards [(Metric.tendsto_nhds.mp (hvanish n).1) (ε / 2) hhalf] with x hx
    calc
      dist (g x) 0 ≤ dist (g x) (fn n x) + dist (fn n x) 0 := dist_triangle _ _ _
      _ < ε := by linarith [hn x]
  have hgbot : Tendsto g atBot (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp huniform (ε / 2) hhalf).exists
    filter_upwards [(Metric.tendsto_nhds.mp (hvanish n).2) (ε / 2) hhalf] with x hx
    calc
      dist (g x) 0 ≤ dist (g x) (fn n x) + dist (fn n x) 0 := dist_triangle _ _ _
      _ < ε := by linarith [hn x]
  obtain ⟨ns, hns, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      ((hmem (ns n)).toLp (fn (ns n)) : ℝ → ℂ) x = fn (ns n) x := by
    rw [ae_all_iff]
    exact fun n => (hmem (ns n)).coeFn_toLp
  have hfg : (f : ℝ → ℂ) =ᵐ[volume] g := by
    filter_upwards [hsub, hcoe] with x hx hcx
    have hpoint : Tendsto (fun i => fn (ns i) x) atTop (𝓝 (g x)) :=
      (huniform.tendsto_at x).comp hns.tendsto_atTop
    have hsub' : Tendsto (fun i => fn (ns i) x) atTop (𝓝 ((f : ℝ → ℂ) x)) := by
      simpa only [hcx] using hx
    exact tendsto_nhds_unique hsub' hpoint
  exact ⟨hgcont, hgtop, hgbot, hfg⟩

section SumIntersection

variable {E : Type*} [AddCommGroup E]

/-- `def:sum-intersection-norm`: algebraic sum. -/
def mixedSumSet (A B : AddSubgroup E) : Set E :=
  {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

/-- `def:sum-intersection-norm`: algebraic intersection. -/
def mixedIntersectionSet (A B : AddSubgroup E) : Set E := (A : Set E) ∩ B

/-- Infimal sum gauge. -/
def mixedSumGauge (A B : AddSubgroup E) (nA nB : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  sInf {r | ∃ a ∈ A, ∃ b ∈ B, x = a + b ∧ r = nA a + nB b}

/-- Maximum intersection gauge. -/
def mixedIntersectionGauge (nA nB : E → ℝ≥0∞) (x : E) : ℝ≥0∞ := max (nA x) (nB x)

/-- Cauchy completeness for a set equipped with an extended additive gauge. -/
def GaugeComplete (S : Set E) (N : E → ℝ≥0∞) : Prop :=
  ∀ u : ℕ → E, (∀ n, u n ∈ S) →
    (∀ ε : ℝ, 0 < ε → ∃ k, ∀ m n, k ≤ m → k ≤ n → N (u m - u n) < ENNReal.ofReal ε) →
    ∃ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ n, k ≤ n → N (u n - x) < ENNReal.ofReal ε

end SumIntersection

/-- A simple function with values in `L²` has a jointly measurable canonical
representative.  This is the finite-range base case for the joint
representative construction below. -/
private theorem measurable_simpleFunc_L2_coe {I : Type*} [MeasurableSpace I]
    (s : MeasureTheory.SimpleFunc I (Lp ℂ 2 (volume : Measure ℝ))) :
    Measurable (fun p : I × ℝ => (s p.1 : ℝ → ℂ) p.2) := by
  classical
  induction s using MeasureTheory.SimpleFunc.induction' with
  | const c =>
      exact (Lp.stronglyMeasurable c).measurable.comp measurable_snd
  | @pcw f g A hA hf hg =>
      classical
      have heq : (fun p : I × ℝ =>
          ((MeasureTheory.SimpleFunc.piecewise A hA f g) p.1 : ℝ → ℂ) p.2) =
          fun p => if p.1 ∈ A then (f p.1 : ℝ → ℂ) p.2 else (g p.1 : ℝ → ℂ) p.2 := by
        funext p
        by_cases hp : p.1 ∈ A <;>
          simp [MeasureTheory.SimpleFunc.coe_piecewise, Set.piecewise, hp]
      rw [heq]
      exact hf.ite (hA.preimage measurable_fst) hg

/-- A strongly measurable `L²` path has a jointly measurable representative
whose spatial slice represents the prescribed `L²` class at every parameter.
The everywhere-slice conclusion is useful for continuous solution curves; the
AE-strongly-measurable wrapper below recovers the more general a.e. statement. -/
theorem joint_representative_L2_measurable_strong
    {I : Type*} [MeasurableSpace I]
    (μ : Measure I) (u : I → Lp ℂ 2 (volume : Measure ℝ))
    (humeas : StronglyMeasurable u) :
  ∃ U : I × ℝ → ℂ,
    Measurable U ∧
      ∀ t : I, (fun x => U (t, x)) =ᵐ[volume] (u t : ℝ → ℂ) := by
  let g : I → Lp ℂ 2 (volume : Measure ℝ) := u
  have hg : StronglyMeasurable g := by simpa only [g] using humeas
  let s : ℕ → MeasureTheory.SimpleFunc I (Lp ℂ 2 (volume : Measure ℝ)) := hg.approx
  have hs_tendsto (t : I) : Tendsto (fun n => s n t) atTop (𝓝 (g t)) :=
    hg.tendsto_approx t
  let ε : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  let P : ℕ → ℕ → I → Prop := fun k n t => dist (s n t) (g t) < ε k
  have hPmeas (k n : ℕ) : MeasurableSet {t | P k n t} := by
    change MeasurableSet {t | dist (s n t) (g t) < ε k}
    exact measurableSet_lt ((s n).stronglyMeasurable.dist hg).measurable measurable_const
  have hPexists (k : ℕ) (t : I) : ∃ n, P k n t := by
    have hevent : ∀ᶠ n in atTop, dist (s n t) (g t) < ε k :=
      (tendsto_order.1 (tendsto_iff_dist_tendsto_zero.mp (hs_tendsto t))).2
        _ (hεpos k)
    exact hevent.exists
  let pick (k : ℕ) (t : I) : ℕ := Nat.find (hPexists k t)
  let v (k : ℕ) (t : I) : Lp ℂ 2 (volume : Measure ℝ) := s (pick k t) t
  have hv_close (k : ℕ) (t : I) : dist (v k t) (g t) < ε k := by
    exact Nat.find_spec (hPexists k t)
  let V (k : ℕ) (p : I × ℝ) : ℂ := (v k p.1 : ℝ → ℂ) p.2
  have hV_meas (k : ℕ) : Measurable (V k) := by
    change Measurable fun p : I × ℝ =>
      (s (Nat.find (hPexists k p.1)) p.1 : ℝ → ℂ) p.2
    exact Measurable.find
      (fun n => measurable_simpleFunc_L2_coe (s n))
      (fun n => (hPmeas k n).preimage measurable_fst)
      (fun p => hPexists k p.1)
  let d (k : ℕ) (t : I) : Lp ℂ 2 (volume : Measure ℝ) := v (k + 1) t - v k t
  let D (k : ℕ) (p : I × ℝ) : ℂ := V (k + 1) p - V k p
  have hD_meas (k : ℕ) : Measurable (D k) := (hV_meas (k + 1)).sub (hV_meas k)
  have hd_norm (k : ℕ) (t : I) : ‖d k t‖ ≤ ε (k + 1) + ε k := by
    calc
      ‖d k t‖ = dist (v (k + 1) t) (v k t) := by simp [d, dist_eq_norm]
      _ ≤ dist (v (k + 1) t) (g t) + dist (v k t) (g t) :=
        dist_triangle_right _ _ _
      _ ≤ ε (k + 1) + ε k := add_le_add (hv_close (k + 1) t).le (hv_close k t).le
  have hmajor : Summable (fun k => ε (k + 1) + ε k) := by
    have hshift : Summable (fun k : ℕ => ε (k + 1)) := by
      simpa [ε, pow_succ, mul_comm] using
        summable_geometric_two.mul_left (1 / 2 : ℝ)
    exact hshift.add (by simpa [ε] using summable_geometric_two)
  have hd_norm_summable (t : I) : Summable (fun k => ‖d k t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hd_norm k t) hmajor
  have hd_summable (t : I) : Summable (d · t) := (hd_norm_summable t).of_norm
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (x := (1 / 2 : ℝ)) (by norm_num))
  have hv_tendsto (t : I) : Tendsto (fun k => v k t) atTop (𝓝 (g t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg)
      (fun k => (hv_close k t).le) hε_tendsto
  have hd_hasSum (t : I) : HasSum (d · t) (g t - v 0 t) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm (hd_norm_summable t)).2
    have htel : (fun n => ∑ k ∈ Finset.range n, d k t) =
        fun n => v n t - v 0 t := by
      funext n
      simpa only [d] using Finset.sum_range_sub (fun k => v k t) n
    rw [htel]
    exact (hv_tendsto t).sub_const (v 0 t)
  have hd_tsum (t : I) : ∑' k, d k t = g t - v 0 t := (hd_hasSum t).tsum_eq
  let U : I × ℝ → ℂ := fun p => V 0 p + ∑' k, D k p
  have hUmeas : Measurable U := (hV_meas 0).add (Measurable.tsum hD_meas)
  refine ⟨U, hUmeas, fun t => ?_⟩
  have hdenorm : ∑' k, ‖d k t‖ₑ ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (hd_norm_summable t)
  have hcoe := MeasureTheory.Lp.coeFn_tsum hdenorm
  have hterms : ∀ᵐ x : ℝ ∂volume, ∀ k : ℕ,
      (d k t : ℝ → ℂ) x = D k (t, x) := by
    apply ae_all_iff.2
    intro k
    exact (Lp.coeFn_sub (v (k + 1) t) (v k t)).mono fun x hx => by
      simpa only [d, D, V, Pi.sub_apply] using hx
  have hgdecomp : g t = v 0 t + ∑' k, d k t := by
    rw [hd_tsum]
    abel
  have hsumcoe :
      (g t : ℝ → ℂ) =ᵐ[volume] fun x => V 0 (t, x) + ∑' k, D k (t, x) := by
    rw [hgdecomp]
    filter_upwards [Lp.coeFn_add (v 0 t) (∑' k, d k t), hcoe, hterms]
      with x hadd hseries hterm
    simp only [Pi.add_apply] at hadd ⊢
    rw [hadd, hseries]
    congr 1
    apply tsum_congr
    exact hterm
  simpa only [U, g] using hsumcoe.symm

/-- Measurable form of `joint_representative_L2` for an a.e. strongly
measurable path. -/
theorem joint_representative_L2_measurable {I : Type*} [MeasurableSpace I]
    (μ : Measure I) (u : I → Lp ℂ 2 (volume : Measure ℝ))
    (humeas : AEStronglyMeasurable u μ) :
  ∃ U : I × ℝ → ℂ,
    Measurable U ∧
      ∀ᵐ t : I ∂μ, (fun x => U (t, x)) =ᵐ[volume] (u t : ℝ → ℂ) := by
  let g : I → Lp ℂ 2 (volume : Measure ℝ) := humeas.mk u
  obtain ⟨U, hU, hslice⟩ :=
    joint_representative_L2_measurable_strong μ g humeas.stronglyMeasurable_mk
  refine ⟨U, hU, ?_⟩
  filter_upwards [humeas.ae_eq_mk] with t ht
  exact (hslice t).trans (Filter.Eventually.of_forall fun x => by
    have hx := congrArg
      (fun z : Lp ℂ 2 (volume : Measure ℝ) => (z : ℝ → ℂ) x) ht.symm
    simpa only [g] using hx)

/-- A jointly measurable scalar representative commutes with a Bochner
integral in `L²`.  The conclusion is an equality of spatial functions almost
everywhere, which is the form needed for Duhamel integrals.

The proof tests both sides on every finite-measure spatial set.  On such a set,
the `L²` pairing with its indicator is the scalar set integral; the pairing
commutes with the Bochner integral, and Fubini changes the order of integration.
Local scalar integrability follows from Cauchy--Schwarz. -/
theorem coeFn_integral_L2_of_joint {S : Type*} [MeasurableSpace S]
    (nu : Measure S) [SFinite nu]
    (g : S → Lp ℂ 2 (volume : Measure ℝ)) (G : S × ℝ → ℂ)
    (hg : Integrable g nu)
    (hG : AEStronglyMeasurable G (nu.prod volume))
    (hslice : ∀ᵐ s : S ∂nu,
      (fun x => G (s, x)) =ᵐ[volume] (g s : ℝ → ℂ)) :
    ((∫ s, g s ∂nu : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ s, G (s, x) ∂nu := by
  let v : Lp ℂ 2 (volume : Measure ℝ) := ∫ s, g s ∂nu
  let H : ℝ → ℂ := fun x => ∫ s, G (s, x) ∂nu
  have hprod (B : Set ℝ) (hB : MeasurableSet B) (hBfin : volume B < ⊤) :
      Integrable G (nu.prod (volume.restrict B)) := by
    have hmeasure : nu.prod (volume.restrict B) ≤ nu.prod volume :=
      Measure.prod_mono le_rfl Measure.restrict_le_self
    have hGres : AEStronglyMeasurable G (nu.prod (volume.restrict B)) :=
      hG.mono_measure hmeasure
    refine ⟨hGres, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_prod _ hGres.enorm]
    have hsection : ∀ᵐ s : S ∂nu,
        (∫⁻ x, ‖G (s, x)‖ₑ ∂volume.restrict B) ≤
          ‖g s‖ₑ * (volume B) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
      filter_upwards [hslice] with s hs
      calc
        (∫⁻ x, ‖G (s, x)‖ₑ ∂volume.restrict B) =
            eLpNorm (g s : ℝ → ℂ) 1 (volume.restrict B) := by
          rw [← eLpNorm_one_eq_lintegral_enorm]
          exact eLpNorm_congr_ae (ae_restrict_of_ae hs)
        _ ≤ eLpNorm (g s : ℝ → ℂ) 2 (volume.restrict B) *
            (volume.restrict B) Set.univ ^
              (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
            (Lp.stronglyMeasurable (g s)).aestronglyMeasurable.restrict
        _ ≤ eLpNorm (g s : ℝ → ℂ) 2 volume *
            (volume.restrict B) Set.univ ^
              (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2) := by
          exact mul_le_mul_right'
            (eLpNorm_mono_measure _ Measure.restrict_le_self) _
        _ = ‖g s‖ₑ * (volume B) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
          rw [← Lp.enorm_def]
          simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, hB,
            ENNReal.toReal_one, ENNReal.toReal_ofNat]
    apply lt_of_le_of_lt (lintegral_mono_ae hsection)
    rw [lintegral_mul_const'' _ hg.1.enorm]
    apply ENNReal.mul_lt_top hg.2
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBfin.ne
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro B hB hBfin
    exact integrableOn_Lp_of_measure_ne_top v (by norm_num) hBfin.ne
  · intro B hB hBfin
    change Integrable H (volume.restrict B)
    simpa only [H] using (hprod B hB hBfin).integral_prod_right
  · intro B hB hBfin
    let eB : Lp ℂ 2 (volume : Measure ℝ) :=
      indicatorConstLp 2 hB hBfin.ne (1 : ℂ)
    have hswap := integral_integral_swap
      (f := fun s x => G (s, x)) (hprod B hB hBfin)
    calc
      ∫ x in B, (v : ℝ → ℂ) x ∂volume = inner ℂ eB v := by
        symm
        exact L2.inner_indicatorConstLp_one hB hBfin.ne v
      _ = ∫ s, inner ℂ eB (g s) ∂nu := by
        exact ((innerSL ℂ eB).integral_comp_comm hg).symm
      _ = ∫ s, ∫ x in B, (g s : ℝ → ℂ) x ∂volume ∂nu := by
        apply integral_congr_ae
        filter_upwards with s
        exact L2.inner_indicatorConstLp_one hB hBfin.ne (g s)
      _ = ∫ s, ∫ x in B, G (s, x) ∂volume ∂nu := by
        apply integral_congr_ae
        filter_upwards [hslice] with s hs
        exact integral_congr_ae (ae_restrict_of_ae hs.symm)
      _ = ∫ x in B, ∫ s, G (s, x) ∂nu ∂volume := hswap
      _ = ∫ x in B, H x ∂volume := rfl

/-- `lem:joint-representative-L2`: an a.e. strongly measurable `L²` path has
a jointly measurable scalar representative.

The proof chooses, measurably in the parameter, simple `L²` approximants with
geometrically decreasing errors.  Their telescoping differences are absolutely
summable in `L²`; Mathlib's pointwise realization of summable `Lᵖ` series then
identifies the jointly measurable scalar sum with the original `L²` class on
almost every spatial slice. -/
theorem joint_representative_L2 {I : Type*} [MeasurableSpace I] [TopologicalSpace I]
    (μ : Measure I) (u : I → Lp ℂ 2 (volume : Measure ℝ)) (_hu : Continuous u)
    (humeas : AEStronglyMeasurable u μ) :
  ∃ U : I × ℝ → ℂ,
    AEStronglyMeasurable U (μ.prod volume) ∧
      ∀ᵐ t : I ∂μ, (fun x => U (t, x)) =ᵐ[volume] (u t : ℝ → ℂ) := by
  obtain ⟨U, hU, hu⟩ := joint_representative_L2_measurable μ u humeas
  exact ⟨U, hU.aestronglyMeasurable, hu⟩

end CubicNLSPhaseRetrieval
