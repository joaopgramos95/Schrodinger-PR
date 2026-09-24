import Lean_Code.ScalarMixedNorms

/-!
# Sequential completeness of the scalar endpoint mixed norm

This is the pointwise/Fubini completion argument for `Lᵖ_tL∞_x`.  It avoids
viewing the nonseparable space `L∞` as a Bochner target.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

section

variable {τ χ : Type*} [MeasurableSpace τ] [MeasurableSpace χ]

set_option maxHeartbeats 2000000 in
private theorem eLpNorm_tsum_le_tsum_eLpNorm
    (μ : Measure τ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (D : ℕ → τ → ℝ≥0∞) (hD : ∀ k, Measurable (D k))
    (hpoint : ∀ᵐ t ∂μ, (∑' k, D k t) < ⊤) :
    eLpNorm (fun t => ∑' k, D k t) p μ ≤ ∑' k, eLpNorm (D k) p μ := by
  let dR : ℕ → τ → ℝ := fun k t => (D k t).toReal
  have hdR (k : ℕ) : Measurable (dR k) := (hD k).ennreal_toReal
  have htermfinite : ∀ᵐ t ∂μ, ∀ k, D k t ≠ ⊤ := by
    filter_upwards [hpoint] with t ht
    intro k
    exact ne_top_of_le_ne_top ht.ne (ENNReal.le_tsum k)
  have hnorm (k : ℕ) : eLpNorm (dR k) p μ = eLpNorm (D k) p μ := by
    apply eLpNorm_congr_enorm_ae
    filter_upwards [htermfinite] with t ht
    simpa only [enorm_eq_self] using Real.enorm_toReal (ht k)
  have hpartial (n : ℕ) : AEStronglyMeasurable
      (fun t => ∑ k ∈ Finset.range n, dR k t) μ := by
    exact (Finset.measurable_sum _ fun k _ => hdR k).aestronglyMeasurable
  have hfinite (n : ℕ) :
      eLpNorm (fun t => ∑ k ∈ Finset.range n, dR k t) p μ ≤
        ∑ k ∈ Finset.range n, eLpNorm (D k) p μ := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        simp_rw [Finset.sum_range_succ]
        exact (eLpNorm_add_le (hpartial n) (hdR n).aestronglyMeasurable hp).trans
          (add_le_add ih (hnorm n).le)
  have hlim : ∀ᵐ t ∂μ, Tendsto
      (fun n => ∑ k ∈ Finset.range n, dR k t) atTop
        (𝓝 ((∑' k, D k t).toReal)) := by
    filter_upwards [hpoint] with t ht
    have hs : Summable (fun k => dR k t) := ENNReal.summable_toReal ht.ne
    have heq : (∑' k, D k t).toReal = ∑' k, dR k t := by
      exact ENNReal.tsum_toReal_eq fun k =>
        ne_top_of_le_ne_top ht.ne (ENNReal.le_tsum k)
    rw [heq]
    exact hs.hasSum.tendsto_sum_nat
  have hreal : eLpNorm (fun t => (∑' k, D k t).toReal) p μ ≤
      ∑' k, eLpNorm (D k) p μ := by
    refine Lp.eLpNorm_le_of_ae_tendsto
        (u := (atTop : Filter ℕ))
        (f := fun n t => ∑ k ∈ Finset.range n, dR k t)
        (g := fun t => (∑' k, D k t).toReal)
        (C := ∑' k, eLpNorm (D k) p μ) ?_ hpartial hlim
    · filter_upwards with n
      exact (hfinite n).trans (ENNReal.sum_le_tsum _)
  calc
    eLpNorm (fun t => ∑' k, D k t) p μ =
        eLpNorm (fun t => (∑' k, D k t).toReal) p μ := by
      apply eLpNorm_congr_enorm_ae
      filter_upwards [hpoint] with t ht
      simpa only [enorm_eq_self] using (Real.enorm_toReal ht.ne).symm
    _ ≤ ∑' k, eLpNorm (D k) p μ := hreal

set_option maxHeartbeats 20000000 in
/-- Explicit sequential completeness at the scalar `q = ∞` endpoint. -/
theorem scalar_endpoint_complete (μt : Measure τ) (μx : Measure χ)
    [SigmaFinite μt] [SFinite μx]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (F : ℕ → τ × χ → ℂ) (hFmeas : ∀ n, Measurable (F n))
    (hFmem : ∀ n, MemScalarMixed μt μx p ⊤ (F n))
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      scalarMixedENorm μt μx p ⊤ (fun z => F m z - F n z) < ENNReal.ofReal ε) :
    ∃ f : τ × χ → ℂ, MemScalarMixed μt μx p ⊤ f ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        scalarMixedENorm μt μx p ⊤ (fun z => F n z - f z) < ENNReal.ofReal ε := by
  let ε : ℕ → ℝ := fun k => (2 : ℝ)⁻¹ ^ (k + 2)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  choose N hN using fun k => hCauchy (ε k) (hεpos k)
  let φ : ℕ → ℕ := fun n => Nat.rec (N 0)
    (fun k m => max (N (k + 1)) (m + 1)) n
  have hφstep (k : ℕ) : φ (k + 1) = max (N (k + 1)) (φ k + 1) := by
    simp [φ]
  have hφN (k : ℕ) : N k ≤ φ k := by
    cases k with
    | zero => simp [φ]
    | succ k => rw [hφstep]; exact le_max_left _ _
  have hφmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hφstep]
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  let D : ℕ → τ → ℝ≥0∞ := fun k t => sectionENorm μx ⊤
    (fun z => F (φ k) z - F (φ (k + 1)) z) t
  have hDmeas (k : ℕ) : Measurable (D k) := by
    exact measurable_esssup_section μt μx _ ((hFmeas _).sub (hFmeas _))
  have hDbound (k : ℕ) : eLpNorm (D k) p μt ≤ ENNReal.ofReal (ε k) := by
    change scalarMixedENorm μt μx p ⊤
      (fun z => F (φ k) z - F (φ (k + 1)) z) ≤ ENNReal.ofReal (ε k)
    exact (hN k (φ k) (φ (k + 1)) (hφN k)
      ((hφN k).trans (hφmono (Nat.lt_succ_self k)).le)).le
  have hDsum : (∑' k, eLpNorm (D k) p μt) ≠ ⊤ := by
    apply ne_of_lt
    calc
      (∑' k, eLpNorm (D k) p μt) ≤ ∑' k, ENNReal.ofReal (ε k) := by
        gcongr with k
        exact hDbound k
      _ < ⊤ := by
        simp only [ε, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2⁻¹),
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat]
        simp_rw [show ∀ k : ℕ, k + 2 = 2 + k by omega, pow_add]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        exact ENNReal.mul_lt_top (by finiteness)
          (ENNReal.inv_lt_top.2 (by norm_num))
  have hDpoint : ∀ᵐ t : τ ∂μt, (∑' k, D k t) < ⊤ := by
    apply ae_tsum_ennreal_lt_top μt p hp hp_top D hDmeas hDsum
  have hstep : ∀ᵐ t : τ ∂μt, ∀ᵐ x : χ ∂μx, ∀ k : ℕ,
      edist (F (φ k) (t, x)) (F (φ (k + 1)) (t, x)) ≤ D k t := by
    apply Filter.Eventually.of_forall
    intro t
    apply ae_all_iff.2
    intro k
    filter_upwards [ae_le_eLpNormEssSup
      (f := fun x => F (φ k) (t, x) - F (φ (k + 1)) (t, x))] with x hx
    simpa [D, sectionENorm, eLpNorm_exponent_top, edist_dist, ofReal_norm,
      dist_eq_norm] using hx
  let f : τ × χ → ℂ := fun z => limUnder atTop (fun k => F (φ k) z)
  have hfmeas : Measurable f := by
    exact (StronglyMeasurable.limUnder
      (fun k => (hFmeas (φ k)).stronglyMeasurable)).measurable
  have htail_meas (n : ℕ) : Measurable (fun t => ∑' k, D (k + n) t) :=
    Measurable.tsum fun k => hDmeas (k + n)
  have htail_point (n : ℕ) : ∀ᵐ t : τ ∂μt, (∑' k, D (k + n) t) < ⊤ := by
    filter_upwards [hDpoint] with t ht
    exact lt_of_le_of_lt
      (ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h)
        (fun k => D k t)) ht
  have htail_norm (n : ℕ) :
      eLpNorm (fun t => ∑' k, D (k + n) t) p μt ≤
        ∑' k, eLpNorm (D (k + n)) p μt :=
    eLpNorm_tsum_le_tsum_eLpNorm μt p hp (fun k t => D (k + n) t)
      (fun k => hDmeas (k + n)) (htail_point n)
  have hsection_tail : ∀ n : ℕ, ∀ᵐ t : τ ∂μt,
      sectionENorm μx ⊤ (fun z => F (φ n) z - f z) t ≤
        ∑' k, D (k + n) t := by
    intro n
    filter_upwards [hDpoint, hstep] with t ht hsteps
    rw [sectionENorm, eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [hsteps] with x hxstep
    have hxlim : Tendsto (fun k => F (φ k) (t, x)) atTop (𝓝 (f (t, x))) := by
      dsimp only [f]
      exact (cauchySeq_of_edist_le_of_tsum_ne_top (fun k => D k t)
        hxstep ht.ne).tendsto_limUnder
    have hdist : edist (F (φ n) (t, x)) (f (t, x)) ≤
        ∑' k, D (k + n) t := by
      have hshift_step : ∀ k, edist
          (F (φ (k + n)) (t, x)) (F (φ (k.succ + n)) (t, x)) ≤ D (k + n) t := by
        intro k
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hxstep (k + n)
      have hshift_lim : Tendsto (fun k => F (φ (k + n)) (t, x)) atTop
          (𝓝 (f (t, x))) := (Filter.tendsto_add_atTop_iff_nat n).2 hxlim
      simpa using edist_le_tsum_of_edist_le_of_tendsto₀
        (f := fun k => F (φ (k + n)) (t, x))
        (fun k => D (k + n) t) hshift_step hshift_lim
    simpa [edist_dist, dist_eq_norm, ofReal_norm] using hdist
  have hsubseq_bound (n : ℕ) :
      scalarMixedENorm μt μx p ⊤ (fun z => F (φ n) z - f z) ≤
        ∑' k, eLpNorm (D (k + n)) p μt := by
    unfold scalarMixedENorm
    exact (eLpNorm_mono_enorm_ae ((hsection_tail n).mono fun t ht => by
      simpa only [enorm_eq_self] using ht)).trans (htail_norm n)
  have htail_zero : Tendsto (fun n => ∑' k, eLpNorm (D (k + n)) p μt)
      atTop (𝓝 0) := ENNReal.tendsto_sum_nat_add _ hDsum
  have hsubseq_zero : Tendsto
      (fun n => scalarMixedENorm μt μx p ⊤ (fun z => F (φ n) z - f z))
      atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail_zero
      (fun _ => bot_le) hsubseq_bound
  have hffinite : scalarMixedENorm μt μx p ⊤ f < ⊤ := by
    have hzero : ∀ᶠ n in atTop,
        scalarMixedENorm μt μx p ⊤ (fun z => F (φ n) z - f z) < 1 :=
      (tendsto_order.1 hsubseq_zero).2 1 (by norm_num)
    obtain ⟨n, hn⟩ := hzero.exists
    have htri := scalarMixedENorm_sub_le_add μt μx p hp f 0 (F (φ n))
      hfmeas measurable_zero (hFmeas _)
    have hneg : scalarMixedENorm μt μx p ⊤ (fun z => f z - F (φ n) z) =
        scalarMixedENorm μt μx p ⊤ (fun z => F (φ n) z - f z) := by
      unfold scalarMixedENorm sectionENorm
      apply eLpNorm_congr_ae
      filter_upwards with t
      rw [show (fun x => f (t, x) - F (φ n) (t, x)) =
          -(fun x => F (φ n) (t, x) - f (t, x)) by funext x; simp]
      exact eLpNorm_neg _ _ _
    have hn_top : scalarMixedENorm μt μx p ⊤
        (fun z => f z - F (φ n) z) < ⊤ := by
      rw [hneg]
      exact hn.trans (by norm_num)
    have hFtop : scalarMixedENorm μt μx p ⊤
        (fun z => F (φ n) z - 0) < ⊤ := by
      simpa using (hFmem (φ n)).2
    simpa using htri.trans_lt (ENNReal.add_lt_top.2 ⟨hn_top, hFtop⟩)
  refine ⟨f, ⟨hfmeas.aestronglyMeasurable, hffinite⟩, ?_⟩
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hCauchy (δ / 2) (half_pos hδ)
  obtain ⟨K0, hK0⟩ := eventually_atTop.1 ((tendsto_order.1 hsubseq_zero).2
    (ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.2 (half_pos hδ)))
  let K1 := max K0 N0
  let N1 := max N0 (φ K1)
  refine ⟨N1, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_max_left _ _ |>.trans hn
  have hφn0 : N0 ≤ φ K1 :=
    (le_max_right K0 N0).trans ((hφmono.id_le) K1)
  have hfirst := hN0 n (φ K1) hn0 hφn0
  have hsecond : scalarMixedENorm μt μx p ⊤
      (fun z => F (φ K1) z - f z) < ENNReal.ofReal (δ / 2) :=
    hK0 K1 (le_max_left _ _)
  have htri := scalarMixedENorm_sub_le_add μt μx p hp (F n) f (F (φ K1))
    (hFmeas n) hfmeas (hFmeas _)
  calc
    scalarMixedENorm μt μx p ⊤ (fun z => F n z - f z) ≤
        scalarMixedENorm μt μx p ⊤ (fun z => F n z - F (φ K1) z) +
          scalarMixedENorm μt μx p ⊤ (fun z => F (φ K1) z - f z) := htri
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add hfirst hsecond
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (le_of_lt (half_pos hδ)) (le_of_lt (half_pos hδ))]
      congr 1
      ring

end

end CubicNLSPhaseRetrieval
