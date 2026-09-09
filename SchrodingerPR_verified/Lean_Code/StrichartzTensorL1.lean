import Lean_Code.StrichartzTensorCore

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators

noncomputable section

set_option maxHeartbeats 10000000

namespace CubicNLSPhaseRetrieval

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
    exact Complex.continuous_conj.measurable.comp (by
      unfold tensorRaw
      fun_prop)
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
      simpa only [SchwartzMap.sum_apply] using
        (enorm_sum_le Finset.univ (fun i => (conj (a i t) • conjSchwartz (b i)) x))
    _ = ∑ i, ∫⁻ x : ℝ, ‖(conj (a i t) • conjSchwartz (b i)) x‖ₑ := by
      rw [lintegral_finset_sum]
      intro i hi
      fun_prop
    _ = ∑ i, ‖a i t‖ₑ * ∫⁻ x : ℝ, ‖conjSchwartz (b i) x‖ₑ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_apply, enorm_smul, RCLike.enorm_conj]
      rw [lintegral_const_mul']
      exact enorm_ne_top

lemma tensorSliceL1_memLp {n : ℕ} (a b : Fin n → SchwartzMap ℝ ℂ) :
    MemLp (tensorSliceL1 a b) (4 / 3) volume := by
  let S : ℝ → ℝ := fun t =>
    ∑ i, (schwartzL1E (conjSchwartz (b i))).toReal * ‖a i t‖
  have hS : MemLp S (4 / 3) volume := by
    unfold S
    classical
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simpa using (MemLp.zero : MemLp (fun _ : ℝ => (0 : ℝ)) (4 / 3) volume)
    | @insert i s hi ih =>
        have hadd := (((a i).memLp (4 / 3) volume).norm.const_mul
          (schwartzL1E (conjSchwartz (b i))).toReal).add ih
        convert hadd using 1
        funext t
        simp only [Pi.add_apply, Finset.sum_insert hi]
  apply hS.of_le_enorm (tensorSliceL1_measurable a b).aestronglyMeasurable
  filter_upwards with t
  calc
    tensorSliceL1 a b t ≤ tensorSize a b t := tensorSliceL1_le_size a b t
    _ = ‖S t‖ₑ := by
      unfold tensorSize S
      rw [Real.enorm_eq_ofReal_abs]
      have hnonneg : 0 ≤ ∑ i,
          (schwartzL1E (conjSchwartz (b i))).toReal * ‖a i t‖ := by positivity
      rw [abs_of_nonneg hnonneg, ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (schwartzL1E_ne_top _), ofReal_norm]
        ring
      · intro i hi
        positivity

end CubicNLSPhaseRetrieval
