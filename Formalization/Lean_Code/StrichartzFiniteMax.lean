import Lean_Code.StrichartzTimeProfiles

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators FourierTransform

noncomputable section

set_option maxHeartbeats 5000000

namespace CubicNLSPhaseRetrieval

variable {n : ℕ}

/-- Predicate saying that the natural number `k` represents a maximizing
index for a nonempty family indexed by `Fin (n+1)`.  Quantifying over the
proof of the bound makes the definition independent of proof terms. -/
def IsFiniteWinner (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) (k : ℕ) : Prop :=
  k < n + 1 ∧ ∀ (hk : k < n + 1) (j : Fin (n + 1)),
    ‖A j t‖ ≤ ‖A ⟨k, hk⟩ t‖

lemma finiteWinner_exists (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) :
    ∃ k, IsFiniteWinner A t k := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (n + 1))) (fun j => ‖A j t‖) Finset.univ_nonempty
  refine ⟨i, i.isLt, fun hk j => ?_⟩
  simpa only using himax j (Finset.mem_univ j)

lemma measurableSet_isFiniteWinner (A : Fin (n + 1) → ℝ → ℂ)
    (hA : ∀ i, Measurable (A i)) (k : ℕ) :
    MeasurableSet {t | IsFiniteWinner A t k} := by
  by_cases hk : k < n + 1
  · have hset : {t | IsFiniteWinner A t k} =
        ⋂ j : Fin (n + 1), {t | ‖A j t‖ ≤ ‖A ⟨k, hk⟩ t‖} := by
      ext t
      simp only [IsFiniteWinner, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h j
        exact h.2 hk j
      · intro h
        refine ⟨hk, fun hk' j => ?_⟩
        simpa only [Subsingleton.elim hk' hk] using h j
    rw [hset]
    exact MeasurableSet.iInter fun j => measurableSet_le (hA j).norm (hA ⟨k, hk⟩).norm
  · have hset : {t | IsFiniteWinner A t k} = ∅ := by
      ext t
      simp [IsFiniteWinner, hk]
    rw [hset]
    exact MeasurableSet.empty

/-- The least maximizing index, chosen measurably. -/
def finiteWinnerNat (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) : ℕ :=
  by
    classical
    exact Nat.find (finiteWinner_exists A t)

lemma finiteWinnerNat_isWinner (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) :
    IsFiniteWinner A t (finiteWinnerNat A t) :=
  by
    classical
    exact Nat.find_spec (finiteWinner_exists A t)

lemma finiteWinnerNat_lt (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) :
    finiteWinnerNat A t < n + 1 :=
  (finiteWinnerNat_isWinner A t).1

lemma finiteWinnerNat_measurable (A : Fin (n + 1) → ℝ → ℂ)
    (hA : ∀ i, Measurable (A i)) : Measurable (finiteWinnerNat A) := by
  classical
  exact measurable_find (fun t => finiteWinner_exists A t)
    (measurableSet_isFiniteWinner A hA)

def finiteWinner (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) : Fin (n + 1) :=
  ⟨finiteWinnerNat A t, finiteWinnerNat_lt A t⟩

lemma finiteWinner_max (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ)
    (j : Fin (n + 1)) : ‖A j t‖ ≤ ‖A (finiteWinner A t) t‖ := by
  exact (finiteWinnerNat_isWinner A t).2 (finiteWinnerNat_lt A t) j

/-- Pointwise maximum of the norms of a nonempty finite family. -/
def finiteMaxProfile (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖A (finiteWinner A t) t‖

lemma finiteMaxProfile_nonneg (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) :
    0 ≤ finiteMaxProfile A t := norm_nonneg _

lemma finiteMaxProfile_measurable (A : Fin (n + 1) → ℝ → ℂ)
    (hA : ∀ i, Measurable (A i)) : Measurable (finiteMaxProfile A) := by
  classical
  let w : ℝ → ℕ := finiteWinnerNat A
  have hw : Measurable w := finiteWinnerNat_measurable A hA
  have hpiece (i : Fin (n + 1)) : Measurable
      (fun t => if w t = i then ‖A i t‖ else 0) := by
    apply Measurable.ite
    · exact hw (measurableSet_singleton i.val)
    · exact (hA i).norm
    · exact measurable_const
  have heq : finiteMaxProfile A = fun t =>
      ∑ i : Fin (n + 1), if w t = i then ‖A i t‖ else 0 := by
    funext t
    unfold finiteMaxProfile finiteWinner w
    rw [Finset.sum_eq_single ⟨finiteWinnerNat A t, finiteWinnerNat_lt A t⟩]
    · simp
    · intro j hj hne
      have hn : finiteWinnerNat A t ≠ j.val := by
        intro hwj
        apply hne
        apply Fin.ext
        exact hwj.symm
      simp [hn]
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => hpiece i

lemma finiteMaxProfile_eq (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ) :
    finiteMaxProfile A t = ‖A (finiteWinner A t) t‖ := rfl

lemma finiteMaxProfile_ge (A : Fin (n + 1) → ℝ → ℂ) (t : ℝ)
    (j : Fin (n + 1)) : ‖A j t‖ ≤ finiteMaxProfile A t :=
  finiteWinner_max A t j

lemma finiteMaxProfile_memLp_four (A : Fin (n + 1) → ℝ → ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ)) :
    MemLp (finiteMaxProfile A) 4 (volume : Measure ℝ) := by
  let S : ℝ → ℝ := fun t => ∑ i : Fin (n + 1), ‖A i t‖
  have hS : MemLp S 4 volume := by
    unfold S
    exact memLp_finset_sum _ fun i _ => (hA i).norm
  apply hS.of_le (finiteMaxProfile_measurable A hmeas).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteMaxProfile_nonneg A t),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ S t)]
  unfold S
  exact (finiteMaxProfile_ge A t (finiteWinner A t)).trans
    (Finset.single_le_sum (fun i _ => norm_nonneg (A i t)) (Finset.mem_univ _))

end CubicNLSPhaseRetrieval
