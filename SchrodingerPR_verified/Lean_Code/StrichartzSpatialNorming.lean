import Lean_Code.StrichartzTensorTest

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 3000000

namespace CubicNLSPhaseRetrieval

abbrev L1Complex : Type := Lp ℂ 1 (volume : Measure ℝ)

local instance : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

private lemma schwartz_unit_range_dense :
    Dense {g : Metric.closedBall (0 : L1Complex) 1 |
      ∃ φ : SchwartzMap ℝ ℂ, φ.toLp 1 volume = (g : L1Complex)} := by
  rw [Metric.dense_iff]
  intro g ε hε
  let c : ℝ := ε / (2 * (ε + 1))
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c < 1 := by
    dsimp [c]
    rw [div_lt_one (by positivity)]
    linarith
  have h2c : 2 * c < ε := by
    dsimp [c]
    rw [show 2 * (ε / (2 * (ε + 1))) = ε / (ε + 1) by field_simp]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  let g' : L1Complex := (1 - c : ℝ) • (g : L1Complex)
  let L : SchwartzMap ℝ ℂ →L[ℂ] L1Complex :=
    SchwartzMap.toLpCLM ℂ ℂ 1 volume
  have hLdense : DenseRange L :=
    SchwartzMap.denseRange_toLpCLM ENNReal.one_ne_top
  obtain ⟨φ, hφ⟩ := hLdense.exists_dist_lt g' hc0
  have hg_norm : ‖(g : L1Complex)‖ ≤ 1 := by
    exact (mem_closedBall_zero_iff.mp g.property)
  have hg'norm : ‖g'‖ ≤ 1 - c := by
    dsimp [g']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hc1)]
    nlinarith
  have hφnorm : ‖L φ‖ < 1 := by
    calc
      ‖L φ‖ ≤ ‖g'‖ + ‖L φ - g'‖ := by
        convert norm_add_le g' (L φ - g') using 1 <;> abel
      _ < (1 - c) + c :=
        add_lt_add_of_le_of_lt hg'norm (by
          have hφ' : dist (L φ) g' < c := by simpa only [dist_comm] using hφ
          simpa only [dist_eq_norm] using hφ')
      _ = 1 := by ring
  let z : Metric.closedBall (0 : L1Complex) 1 :=
    ⟨L φ, by
      rw [mem_closedBall_zero_iff]
      exact hφnorm.le⟩
  refine ⟨z, ?_, φ, ?_⟩
  · rw [mem_ball]
    change dist (z : L1Complex) (g : L1Complex) < ε
    dsimp only [z]
    rw [dist_comm]
    calc
      dist (g : L1Complex) (L φ) ≤ dist (g : L1Complex) g' + dist g' (L φ) :=
        dist_triangle _ _ _
      _ < c + c := by
        apply add_lt_add_of_le_of_lt
        · dsimp [g']
          rw [dist_eq_norm]
          calc
            ‖(g : L1Complex) - (1 - c : ℝ) • (g : L1Complex)‖ =
                ‖c • (g : L1Complex)‖ := by
              congr 1
              module
            _ = c * ‖(g : L1Complex)‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
            _ ≤ c := by nlinarith
        · exact hφ
      _ = 2 * c := by ring
      _ < ε := h2c
  · change L φ = L φ
    rfl

theorem exists_schwartz_unit_norming_sequence :
    ∃ b : ℕ → SchwartzMap ℝ ℂ,
      (∀ n, ‖(b n).toLp 1 volume‖ ≤ 1) ∧
      ∀ g : L1Complex, ‖g‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
        ∃ n, dist ((b n).toLp 1 volume) g < ε := by
  let S : Set (Metric.closedBall (0 : L1Complex) 1) :=
    {g | ∃ φ : SchwartzMap ℝ ℂ, φ.toLp 1 volume = (g : L1Complex)}
  have hS : Dense S := schwartz_unit_range_dense
  obtain ⟨T, hTS, hTcount, hTdense⟩ := hS.exists_countable_dense_subset
  have hTnonempty : T.Nonempty := hTdense.nonempty
  obtain ⟨d, hd⟩ := hTcount.exists_eq_range hTnonempty
  have hdS (n : ℕ) : d n ∈ S := by
    apply hTS
    rw [hd]
    exact ⟨n, rfl⟩
  choose b hb using fun n => hdS n
  have hbnorm (n : ℕ) : ‖(b n).toLp 1 volume‖ ≤ 1 := by
    have hdmem := (d n).property
    rw [mem_closedBall_zero_iff] at hdmem
    simpa only [hb n] using hdmem
  refine ⟨b, hbnorm, ?_⟩
  intro g hg ε hε
  let z : Metric.closedBall (0 : L1Complex) 1 :=
    ⟨g, by rw [mem_closedBall_zero_iff]; exact hg⟩
  obtain ⟨w, hwT, hw⟩ := hTdense.exists_dist_lt z hε
  rw [hd] at hwT
  obtain ⟨n, rfl⟩ := hwT
  refine ⟨n, ?_⟩
  change dist ((b n).toLp 1 volume) g < ε
  rw [hb n]
  change dist (d n) z < ε
  simpa only [dist_comm] using hw

lemma norm_integral_Linfty_L1_le (h : Lp ℂ ⊤ (volume : Measure ℝ))
    (g : L1Complex) :
    ‖∫ x : ℝ, (h : ℝ → ℂ) x * (g : ℝ → ℂ) x‖ ≤ ‖h‖ * ‖g‖ := by
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  let P : Lp ℂ 1 (volume : Measure ℝ) := B.holder 1 h g
  have hcoe : (P : ℝ → ℂ) =ᵐ[volume]
      fun x => (h : ℝ → ℂ) x * (g : ℝ → ℂ) x := by
    exact B.coeFn_holder h g
  rw [← integral_congr_ae hcoe, ← L1.integral_eq_integral]
  calc
    ‖L1.integral P‖ ≤ ‖P‖ := L1.norm_integral_le P
    _ ≤ ‖B‖ * ‖h‖ * ‖g‖ := B.norm_holder_apply_apply_le h g
    _ ≤ ‖h‖ * ‖g‖ := by
      have hB : ‖B‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound (f := B) (by norm_num)
        intro z
        simp only [one_mul]
        apply ContinuousLinearMap.opNorm_le_bound (f := B z) (norm_nonneg z)
        intro w
        change ‖z * w‖ ≤ ‖z‖ * ‖w‖
        rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hB (norm_nonneg h)) (norm_nonneg g)

end CubicNLSPhaseRetrieval
