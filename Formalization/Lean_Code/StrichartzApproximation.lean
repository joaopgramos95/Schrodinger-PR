import Lean_Code.StrichartzFiniteDual

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators FourierTransform

noncomputable section

set_option maxHeartbeats 500000

namespace CubicNLSPhaseRetrieval

lemma schwartzL1E_eq_ofReal_norm_toLp (b : SchwartzMap ℝ ℂ) :
    schwartzL1E b = ENNReal.ofReal ‖b.toLp 1 volume‖ := by
  rw [SchwartzMap.norm_toLp, ENNReal.ofReal_toReal]
  · exact eLpNorm_one_eq_lintegral_enorm.symm
  · exact (b.memLp 1 volume).2.ne

lemma schwartzL1E_conj_le_one (b : SchwartzMap ℝ ℂ)
    (hb : ‖b.toLp 1 volume‖ ≤ 1) :
    schwartzL1E (conjSchwartz b) ≤ 1 := by
  have heq : schwartzL1E (conjSchwartz b) = schwartzL1E b := by
    unfold schwartzL1E
    apply lintegral_congr
    intro x
    simp only [conjSchwartz_apply, RCLike.enorm_conj]
  calc
    schwartzL1E (conjSchwartz b) = schwartzL1E b := heq
    _ = ENNReal.ofReal ‖b.toLp 1 volume‖ := schwartzL1E_eq_ofReal_norm_toLp b
    _ ≤ 1 := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hb

lemma exists_schwartz_eLpNorm_sub_lt
    (c : ℝ → ℂ) (hc : MemLp c (4 / 3) (volume : Measure ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : SchwartzMap ℝ ℂ,
      eLpNorm (fun t => a t - c t) (4 / 3) (volume : Measure ℝ) <
        ENNReal.ofReal δ := by
  letI : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    norm_num⟩
  let L : SchwartzMap ℝ ℂ →L[ℂ] Lp ℂ (4 / 3) (volume : Measure ℝ) :=
    SchwartzMap.toLpCLM ℂ ℂ (4 / 3) volume
  have hLdense : DenseRange L := SchwartzMap.denseRange_toLpCLM
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  let g : Lp ℂ (4 / 3) (volume : Measure ℝ) := hc.toLp c
  obtain ⟨a, ha⟩ := hLdense.exists_dist_lt g hδ
  refine ⟨a, ?_⟩
  have hcoeA : (L a : ℝ → ℂ) =ᵐ[volume] a :=
    (a.memLp (4 / 3) volume).coeFn_toLp
  have hcoeC : (g : ℝ → ℂ) =ᵐ[volume] c := hc.coeFn_toLp
  have hsub : (fun t : ℝ => a t - c t) =ᵐ[volume]
      fun t => ((L a - g : Lp ℂ (4 / 3) volume) : ℝ → ℂ) t := by
    filter_upwards [hcoeA, hcoeC, Lp.coeFn_sub (L a) g] with t hAt hCt hsubt
    simpa only [Pi.sub_apply, hAt, hCt] using hsubt.symm
  rw [eLpNorm_congr_ae hsub]
  have hmem : MemLp ((L a - g : Lp ℂ (4 / 3) volume) : ℝ → ℂ)
      (4 / 3) volume := Lp.memLp _
  rw [← ENNReal.ofReal_toReal hmem.2.ne]
  rw [ENNReal.ofReal_lt_ofReal_iff hδ]
  have ha' : ‖L a - g‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using ha
  simpa only [Lp.norm_def] using ha'

lemma integral_difference_enorm_le {p q : ℝ≥0∞}
    (u v : ℝ → ℂ) (hu : MemLp u p (volume : Measure ℝ))
    (hv : MemLp v q (volume : Measure ℝ))
    (hp : p = 4 / 3) (hq : q = 4) :
    ‖∫ t : ℝ, u t * v t‖ₑ ≤ eLpNorm u p volume * eLpNorm v q volume := by
  calc
    ‖∫ t : ℝ, u t * v t‖ₑ ≤ ∫⁻ t : ℝ, ‖u t * v t‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t : ℝ, ‖u t‖ₑ * ‖v t‖ₑ := by
      apply lintegral_congr
      intro t
      rw [enorm_mul]
    _ ≤ eLpNorm (fun t => ‖u t‖ₑ) (4 / 3) volume *
        eLpNorm (fun t => ‖v t‖ₑ) 4 volume :=
      lintegral_mul_le_eLpNorm_four_thirds_four _ _
        hu.1.enorm hv.1.enorm
    _ = eLpNorm u p volume * eLpNorm v q volume := by
      rw [eLpNorm_enorm, eLpNorm_enorm, hp, hq]

variable {n : ℕ}

lemma tensorSliceL1_le_dualMagnitude_add_error
    (A : Fin (n + 1) → ℝ → ℂ) (ε : ℝ)
    (a b : Fin (n + 1) → SchwartzMap ℝ ℂ)
    (hb : ∀ i, ‖(b i).toLp 1 volume‖ ≤ 1)
    (hscale : 0 < finiteDualScale A ε) (t : ℝ) :
    tensorSliceL1 a b t ≤
      ENNReal.ofReal (finiteDualMagnitude A ε t) +
        ∑ i : Fin (n + 1), ‖a i t - finiteDualCoeff A ε i t‖ₑ := by
  calc
    tensorSliceL1 a b t ≤ tensorSize a b t := tensorSliceL1_le_size a b t
    _ ≤ ∑ i : Fin (n + 1), ‖a i t‖ₑ := by
      unfold tensorSize
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_one] using mul_le_mul_left'
        (schwartzL1E_conj_le_one (b i) (hb i)) ‖a i t‖ₑ
    _ ≤ ∑ i : Fin (n + 1),
        (‖finiteDualCoeff A ε i t‖ₑ +
          ‖a i t - finiteDualCoeff A ε i t‖ₑ) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖a i t‖ₑ = ‖finiteDualCoeff A ε i t +
            (a i t - finiteDualCoeff A ε i t)‖ₑ := by congr 1 <;> ring
        _ ≤ ‖finiteDualCoeff A ε i t‖ₑ +
            ‖a i t - finiteDualCoeff A ε i t‖ₑ :=
          enorm_add_le _ _
    _ = (∑ i : Fin (n + 1), ‖finiteDualCoeff A ε i t‖ₑ) +
        ∑ i : Fin (n + 1), ‖a i t - finiteDualCoeff A ε i t‖ₑ := by
      rw [Finset.sum_add_distrib]
    _ ≤ ENNReal.ofReal (finiteDualMagnitude A ε t) +
        ∑ i : Fin (n + 1), ‖a i t - finiteDualCoeff A ε i t‖ₑ := by
      have hcoeff : (∑ i : Fin (n + 1), ‖finiteDualCoeff A ε i t‖ₑ) ≤
          ENNReal.ofReal (finiteDualMagnitude A ε t) := by
        calc
          (∑ i : Fin (n + 1), ‖finiteDualCoeff A ε i t‖ₑ) =
              ENNReal.ofReal (∑ i : Fin (n + 1), ‖finiteDualCoeff A ε i t‖) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · apply Finset.sum_congr rfl
              intro i hi
              exact ofReal_norm _ |>.symm
            · intro i hi
              exact norm_nonneg _
          _ ≤ ENNReal.ofReal (finiteDualMagnitude A ε t) :=
            ENNReal.ofReal_le_ofReal (sum_finiteDualCoeff_norm_le A hscale t)
      simpa only [add_comm] using add_le_add_right hcoeff
        (∑ i : Fin (n + 1), ‖a i t - finiteDualCoeff A ε i t‖ₑ)

lemma tensorSliceL1_eLpNorm_le_one_add_errors
    (A : Fin (n + 1) → ℝ → ℂ) (ε : ℝ)
    (a b : Fin (n + 1) → SchwartzMap ℝ ℂ)
    (hb : ∀ i, ‖(b i).toLp 1 volume‖ ≤ 1)
    (hmeas : ∀ i, Measurable (A i))
    (hscale : 0 < finiteDualScale A ε)
    (hmag : eLpNorm (finiteDualMagnitude A ε) (4 / 3) volume ≤ 1) :
    eLpNorm (tensorSliceL1 a b) (4 / 3) volume ≤
      1 + ∑ i : Fin (n + 1),
        eLpNorm (fun t => a i t - finiteDualCoeff A ε i t) (4 / 3) volume := by
  let Q : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (finiteDualMagnitude A ε t)
  let D : Fin (n + 1) → ℝ → ℝ≥0∞ := fun i t =>
    ‖a i t - finiteDualCoeff A ε i t‖ₑ
  let R : ℝ → ℝ≥0∞ := fun t => ∑ i : Fin (n + 1), D i t
  have hQ : Measurable Q := ENNReal.measurable_ofReal.comp
    (finiteDualMagnitude_measurable A hmeas ε)
  have hD (i : Fin (n + 1)) : Measurable (D i) :=
    ((a i).continuous.measurable.sub
      (finiteDualCoeff_measurable A hmeas ε i)).enorm
  have hR : Measurable R := by
    unfold R
    exact Finset.measurable_sum _ fun i _ => hD i
  have hQnorm : eLpNorm Q (4 / 3) volume =
      eLpNorm (finiteDualMagnitude A ε) (4 / 3) volume := by
    unfold Q
    exact eLpNorm_ofReal _ (Filter.Eventually.of_forall fun t =>
      finiteDualMagnitude_nonneg A hscale t)
  have hDnorm (i : Fin (n + 1)) : eLpNorm (D i) (4 / 3) volume =
      eLpNorm (fun t => a i t - finiteDualCoeff A ε i t) (4 / 3) volume := by
    unfold D
    exact eLpNorm_enorm _
  have hDsum : (∑ i : Fin (n + 1), eLpNorm (D i) (4 / 3) volume) =
      ∑ i : Fin (n + 1),
        eLpNorm (fun t => a i t - finiteDualCoeff A ε i t) (4 / 3) volume := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hDnorm i
  have hp : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))).mpr
    norm_num
  calc
    eLpNorm (tensorSliceL1 a b) (4 / 3) volume ≤
        eLpNorm (fun t => Q t + R t) (4 / 3) volume := by
      apply eLpNorm_mono_enorm
      intro t
      simp only [enorm_eq_self]
      unfold R
      exact tensorSliceL1_le_dualMagnitude_add_error A ε a b hb hscale t
    _ ≤ eLpNorm Q (4 / 3) volume +
        eLpNorm R (4 / 3) volume := by
      have hadd := eLpNorm_add_le (p := (4 / 3 : ℝ≥0∞)) (μ := volume)
        (hQ.aestronglyMeasurable (μ := volume))
        (hR.aestronglyMeasurable (μ := volume)) hp
      have hfun : (fun t => Q t + R t) = Q + R := by
        funext t
        rfl
      rw [hfun]
      exact hadd
    _ ≤ eLpNorm Q (4 / 3) volume +
        ∑ i : Fin (n + 1), eLpNorm (D i) (4 / 3) volume := by
      have hsum : eLpNorm R (4 / 3) volume ≤
          ∑ i : Fin (n + 1), eLpNorm (D i) (4 / 3) volume := by
        unfold R
        have hfun : (fun t => ∑ i : Fin (n + 1), D i t) =
            ∑ i : Fin (n + 1), D i := by
          funext t
          simp only [Finset.sum_apply]
        rw [hfun]
        exact eLpNorm_sum_le (s := (Finset.univ : Finset (Fin (n + 1))))
          (μ := volume)
          (fun i hi => (hD i).aestronglyMeasurable (μ := volume)) hp
      exact add_le_add_right hsum _
    _ = eLpNorm (finiteDualMagnitude A ε) (4 / 3) volume +
        ∑ i : Fin (n + 1),
          eLpNorm (fun t => a i t - finiteDualCoeff A ε i t) (4 / 3) volume := by
      rw [hQnorm, hDsum]
    _ ≤ 1 + ∑ i : Fin (n + 1),
        eLpNorm (fun t => a i t - finiteDualCoeff A ε i t) (4 / 3) volume :=
      add_le_add_left hmag _

lemma ENNReal.le_of_forall_le_add_ofReal_mul {x B K : ℝ≥0∞}
    (hB : B < ⊤) (hK : K < ⊤)
    (h : ∀ δ : ℝ, 0 < δ → x ≤ B + ENNReal.ofReal δ * K) : x ≤ B := by
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη hB'
  let δ : ℝ := (η : ℝ) / (K.toReal + 1)
  have hden : 0 < K.toReal + 1 := by positivity
  have hδ : 0 < δ := div_pos (by exact_mod_cast hη) hden
  apply (h δ hδ).trans
  apply add_le_add_right
  have hKof : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hK.ne
  calc
    ENNReal.ofReal δ * K ≤ ENNReal.ofReal δ * ENNReal.ofReal (K.toReal + 1) := by
      apply mul_le_mul_left'
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), hKof]
      simpa using (self_le_add_right K 1)
    _ = ENNReal.ofReal (δ * (K.toReal + 1)) := by
      rw [ENNReal.ofReal_mul hδ.le]
    _ = η := by
      rw [show δ * (K.toReal + 1) = (η : ℝ) by
        dsimp [δ]
        field_simp]
      simp

end CubicNLSPhaseRetrieval
