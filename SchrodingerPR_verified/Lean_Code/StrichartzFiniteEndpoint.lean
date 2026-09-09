import Lean_Code.StrichartzApproximation

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology SchwartzMap ComplexConjugate BigOperators FourierTransform

noncomputable section

set_option maxHeartbeats 300000

namespace CubicNLSPhaseRetrieval

lemma product_integrable_four_thirds_four (u v : ℝ → ℂ)
    (hu : MemLp u (4 / 3) (volume : Measure ℝ))
    (hv : MemLp v 4 (volume : Measure ℝ)) :
    Integrable (fun t => u t * v t) volume := by
  refine ⟨hu.1.mul hv.1, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ t : ℝ, ‖u t * v t‖ₑ) = ∫⁻ t : ℝ, ‖u t‖ₑ * ‖v t‖ₑ := by
      apply lintegral_congr
      intro t
      rw [enorm_mul]
    _ ≤ eLpNorm (fun t => ‖u t‖ₑ) (4 / 3) volume *
        eLpNorm (fun t => ‖v t‖ₑ) 4 volume :=
      lintegral_mul_le_eLpNorm_four_thirds_four _ _ hu.1.enorm hv.1.enorm
    _ < ⊤ := by
      rw [eLpNorm_enorm, eLpNorm_enorm]
      exact ENNReal.mul_lt_top hu.2 hv.2

lemma schwartzFreeFlow_mul_integrable (φ b : SchwartzMap ℝ ℂ) (t : ℝ) :
    Integrable (fun x : ℝ => schwartzFreeFlow φ (t, x) * b x) volume := by
  apply Integrable.mono'
    (b.integrable.norm.const_mul (∫ ξ : ℝ, ‖(𝓕 φ) ξ‖))
    (((schwartzFreeFlow_continuous φ).comp
      (continuous_const.prodMk continuous_id)).mul b.continuous).aestronglyMeasurable
  filter_upwards with x
  change ‖schwartzFreeFlow φ (t, x) * b x‖ ≤
    (∫ ξ : ℝ, ‖(𝓕 φ) ξ‖) * ‖b x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (schwartzFreeFlow_uniform_bound φ t x)
    (norm_nonneg _)

lemma tensor_pairing_eq_sum_freeFlow {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (a b : Fin n → SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, ∫ x : ℝ,
        tensorRaw a b (t, x) *
          curveRepresentative (fun s => freeProp s (φ.toLp 2 volume)) (t, x)) =
      ∫ t : ℝ, ∑ i : Fin n, a i t * freeFlowPairing φ (b i) t := by
  apply integral_congr_ae
  filter_upwards with t
  have hslice := schwartzFreeFlow_slice_ae φ t
  calc
    (∫ x : ℝ, tensorRaw a b (t, x) *
        curveRepresentative (fun s => freeProp s (φ.toLp 2 volume)) (t, x)) =
        ∫ x : ℝ, tensorRaw a b (t, x) * schwartzFreeFlow φ (t, x) := by
      apply integral_congr_ae
      filter_upwards [hslice] with x hx
      unfold curveRepresentative
      rw [← hx]
    _ = ∫ x : ℝ, ∑ i : Fin n,
        (a i t * b i x) * schwartzFreeFlow φ (t, x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold tensorRaw
      rw [Finset.sum_mul]
    _ = ∑ i : Fin n, ∫ x : ℝ,
        (a i t * b i x) * schwartzFreeFlow φ (t, x) := by
      rw [integral_finset_sum]
      intro i hi
      have hi' := (schwartzFreeFlow_mul_integrable φ (b i) t).const_mul (a i t)
      apply hi'.congr
      filter_upwards with x
      ring
    _ = ∑ i : Fin n, a i t * freeFlowPairing φ (b i) t := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold freeFlowPairing
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

variable {n : ℕ}

lemma integral_sum_sub_enorm_le
    (A : Fin (n + 1) → ℝ → ℂ)
    (a : Fin (n + 1) → SchwartzMap ℝ ℂ)
    (hmeas : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 4 (volume : Measure ℝ))
    (ε : ℝ) (hscale : 0 < finiteDualScale A ε) :
    ‖(∫ t : ℝ, ∑ i : Fin (n + 1), a i t * A i t) -
        ∫ t : ℝ, ∑ i : Fin (n + 1), finiteDualCoeff A ε i t * A i t‖ₑ ≤
      ∑ i : Fin (n + 1),
        eLpNorm (fun t => a i t - finiteDualCoeff A ε i t) (4 / 3) volume *
          eLpNorm (A i) 4 volume := by
  rw [← integral_sub]
  · rw [show (fun t : ℝ => (∑ i : Fin (n + 1), a i t * A i t) -
          ∑ i : Fin (n + 1), finiteDualCoeff A ε i t * A i t) =
        fun t => ∑ i : Fin (n + 1),
          (a i t - finiteDualCoeff A ε i t) * A i t by
      funext t
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [integral_finset_sum]
    · exact (enorm_sum_le Finset.univ fun i =>
          ∫ t : ℝ, (a i t - finiteDualCoeff A ε i t) * A i t).trans
        (Finset.sum_le_sum fun i hi => integral_difference_enorm_le
          (fun t => a i t - finiteDualCoeff A ε i t) (A i)
          ((a i).memLp (4 / 3) volume |>.sub
            (finiteDualCoeff_memLp A hmeas hA hscale i)) (hA i) rfl rfl)
    · intro i hi
      exact product_integrable_four_thirds_four _ _
        ((a i).memLp (4 / 3) volume |>.sub
          (finiteDualCoeff_memLp A hmeas hA hscale i)) (hA i)
  · exact integrable_finset_sum _ fun i hi =>
      product_integrable_four_thirds_four _ _ ((a i).memLp (4 / 3) volume) (hA i)
  · exact integrable_finset_sum _ fun i hi => finiteDual_product_integrable A hmeas hA hscale i

theorem finite_max_freeFlow_estimate :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (n : ℕ) (φ : SchwartzMap ℝ ℂ)
        (b : Fin (n + 1) → SchwartzMap ℝ ℂ),
        (∀ i, ‖(b i).toLp 1 volume‖ ≤ 1) →
        eLpNorm (finiteMaxProfile (fun i => freeFlowPairing φ (b i))) 4 volume ≤
          C * ENNReal.ofReal ‖φ.toLp 2 volume‖ := by
  obtain ⟨C, hCtop, hC⟩ := schwartz_tensor_pairing_estimate
  refine ⟨C, hCtop, ?_⟩
  intro n φ b hb
  let A : Fin (n + 1) → ℝ → ℂ := fun i => freeFlowPairing φ (b i)
  let L : ℝ≥0∞ := eLpNorm (finiteMaxProfile A) 4 volume
  let P : ℝ≥0∞ := ENNReal.ofReal ‖φ.toLp 2 volume‖
  have hmeas (i : Fin (n + 1)) : Measurable (A i) :=
    (freeFlowPairing_continuous φ (b i)).measurable
  have hA (i : Fin (n + 1)) : MemLp (A i) 4 volume :=
    freeFlowPairing_memLp_four φ (b i)
  have hM := finiteMaxProfile_memLp_four A hmeas hA
  have hLtop : L < ⊤ := hM.2
  change L ≤ C * P
  by_cases hL0 : L = 0
  · simp [hL0]
  have hLpos : 0 < L := bot_lt_iff_ne_bot.mpr hL0
  have hLreal : 0 < L.toReal := ENNReal.toReal_pos hL0 (ne_of_lt hLtop)
  have hscale : 0 < finiteDualScale A 0 := by
    simpa [finiteDualScale, L] using hLreal
  let S : ℝ≥0∞ := ∑ i : Fin (n + 1), eLpNorm (A i) 4 volume
  let K : ℝ≥0∞ := C * (n + 1 : ℕ) * P + S
  have hPtop : P < ⊤ := ENNReal.ofReal_lt_top
  have hStop : S < ⊤ := by
    unfold S
    rw [ENNReal.sum_lt_top]
    intro i hi
    exact (hA i).2
  have hKtop : K < ⊤ := by
    unfold K
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCtop (by finiteness)) hPtop, hStop⟩
  have hBtop : C * P < ⊤ := ENNReal.mul_lt_top hCtop hPtop
  apply ENNReal.le_of_forall_le_add_ofReal_mul (x := L) (B := C * P)
    (K := K) hBtop hKtop
  intro δ hδ
  have hcLp (i : Fin (n + 1)) :
      MemLp (finiteDualCoeff A 0 i) (4 / 3) volume :=
    finiteDualCoeff_memLp A hmeas hA hscale i
  choose a ha using fun i : Fin (n + 1) =>
    exists_schwartz_eLpNorm_sub_lt (finiteDualCoeff A 0 i) (hcLp i) δ hδ
  let d : ℝ≥0∞ := ENNReal.ofReal δ
  let E : Fin (n + 1) → ℝ≥0∞ := fun i =>
    eLpNorm (fun t => a i t - finiteDualCoeff A 0 i t) (4 / 3) volume
  have hE (i : Fin (n + 1)) : E i ≤ d := (ha i).le
  have hEsum : (∑ i : Fin (n + 1), E i) ≤ (n + 1 : ℕ) * d := by
    calc
      (∑ i : Fin (n + 1), E i) ≤
          (Finset.univ.card : ℕ) • d :=
        Finset.sum_le_card_nsmul Finset.univ E d fun i hi => hE i
      _ = (n + 1 : ℕ) * d := by
        rw [Finset.card_fin]
        simp only [nsmul_eq_mul]
  have htensor : eLpNorm (tensorSliceL1 a b) (4 / 3) volume ≤
      1 + (n + 1 : ℕ) * d := by
    exact (tensorSliceL1_eLpNorm_le_one_add_errors A 0 a b hb hmeas hscale
      (finiteDualMagnitude_zero_eLpNorm A hmeas hA hLpos).le).trans
      (add_le_add_right hEsum 1)
  let Iapprox : ℂ := ∫ t : ℝ, ∑ i : Fin (n + 1), a i t * A i t
  let Iexact : ℂ := ∫ t : ℝ,
    ∑ i : Fin (n + 1), finiteDualCoeff A 0 i t * A i t
  have hIexact : Iexact = (L.toReal : ℂ) := by
    unfold Iexact
    simpa only [L] using integral_sum_finiteDualCoeff_mul_zero A hmeas hA hLpos
  have hLenorm : ‖Iexact‖ₑ = L := by
    rw [hIexact]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ne_of_lt hLtop)]
  have happrox : ‖Iapprox‖ₑ ≤ C * (1 + (n + 1 : ℕ) * d) * P := by
    unfold Iapprox
    rw [← tensor_pairing_eq_sum_freeFlow φ a b]
    exact (hC (n + 1) a b (φ.toLp 2 volume)).trans
      (mul_le_mul_right' (mul_le_mul_left' htensor C) P)
  have herr : ‖Iapprox - Iexact‖ₑ ≤ d * S := by
    calc
      ‖Iapprox - Iexact‖ₑ ≤
          ∑ i : Fin (n + 1), E i * eLpNorm (A i) 4 volume := by
        exact integral_sum_sub_enorm_le A a hmeas hA 0 hscale
      _ ≤ ∑ i : Fin (n + 1), d * eLpNorm (A i) 4 volume := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_right' (hE i) _
      _ = d * S := by
        unfold S
        rw [Finset.mul_sum]
  have htri : L ≤ ‖Iapprox‖ₑ + ‖Iapprox - Iexact‖ₑ := by
    rw [← hLenorm]
    calc
      ‖Iexact‖ₑ = ‖Iapprox - (Iapprox - Iexact)‖ₑ := by congr 1 <;> ring
      _ ≤ ‖Iapprox‖ₑ + ‖Iapprox - Iexact‖ₑ := enorm_sub_le
  calc
    L ≤ ‖Iapprox‖ₑ + ‖Iapprox - Iexact‖ₑ := htri
    _ ≤ (C * (1 + (n + 1 : ℕ) * d) * P) + d * S :=
      add_le_add happrox herr
    _ = C * P + d * K := by
      unfold K
      ring

lemma freeFlowPairing_eq_spatialPairing (φ b : SchwartzMap ℝ ℂ) (t : ℝ) :
    freeFlowPairing φ b t =
      spatialPairing ((schwartzFreeFlow_section_memLp_top φ t).toLp
        (fun x => schwartzFreeFlow φ (t, x))) (b.toLp 1 volume) := by
  unfold freeFlowPairing spatialPairing
  have hh := (schwartzFreeFlow_section_memLp_top φ t).coeFn_toLp
  have hb := b.coeFn_toLp 1 volume
  apply integral_congr_ae
  filter_upwards [hh, hb] with x hhx hbx
  rw [hhx, ← hbx]

def natFiniteMax (A : ℕ → ℝ → ℂ) (n : ℕ) : ℝ → ℝ :=
  finiteMaxProfile (fun i : Fin (n + 1) => A i.val)

lemma natFiniteMax_measurable (A : ℕ → ℝ → ℂ) (hA : ∀ k, Measurable (A k))
    (n : ℕ) : Measurable (natFiniteMax A n) :=
  finiteMaxProfile_measurable _ fun i => hA i.val

lemma natFiniteMax_nonneg (A : ℕ → ℝ → ℂ) (n : ℕ) (t : ℝ) :
    0 ≤ natFiniteMax A n t := finiteMaxProfile_nonneg _ t

lemma natFiniteMax_mono (A : ℕ → ℝ → ℂ) (t : ℝ) :
    Monotone (fun n => ENNReal.ofReal (natFiniteMax A n t)) := by
  intro n m hnm
  apply ENNReal.ofReal_le_ofReal
  let w : Fin (n + 1) := finiteWinner (fun i : Fin (n + 1) => A i.val) t
  have hwlt : w.val < m + 1 := lt_of_lt_of_le w.isLt (Nat.add_le_add_right hnm 1)
  exact finiteMaxProfile_ge (fun i : Fin (m + 1) => A i.val) t ⟨w.val, hwlt⟩

lemma iSup_natFiniteMax (A : ℕ → ℝ → ℂ) (t : ℝ) :
    (⨆ n : ℕ, ENNReal.ofReal (natFiniteMax A n t)) =
      ⨆ k : ℕ, ENNReal.ofReal ‖A k t‖ := by
  apply le_antisymm
  · apply iSup_le
    intro n
    unfold natFiniteMax finiteMaxProfile
    exact le_iSup (fun k : ℕ => ENNReal.ofReal ‖A k t‖)
      ((finiteWinner (fun i : Fin (n + 1) => A i.val) t).val)
  · apply iSup_le
    intro k
    apply le_iSup_of_le k
    apply ENNReal.ofReal_le_ofReal
    exact finiteMaxProfile_ge (fun i : Fin (k + 1) => A i.val) t
      ⟨k, Nat.lt_succ_self k⟩

lemma sectionENorm_eq_iSup_freeFlowPairing
    (φ : SchwartzMap ℝ ℂ) (b : ℕ → SchwartzMap ℝ ℂ)
    (hnorming : ∀ h : Lp ℂ ⊤ (volume : Measure ℝ),
      ENNReal.ofReal ‖h‖ =
        ⨆ k : ℕ, ENNReal.ofReal
          ‖spatialPairing h ((b k).toLp 1 volume)‖) (t : ℝ) :
    sectionENorm volume ⊤ (schwartzFreeFlow φ) t =
      ⨆ k : ℕ, ENNReal.ofReal ‖freeFlowPairing φ (b k) t‖ := by
  let ht := schwartzFreeFlow_section_memLp_top φ t
  have hnorm := hnorming (ht.toLp (fun x => schwartzFreeFlow φ (t, x)))
  have hleft : ENNReal.ofReal
      ‖ht.toLp (fun x => schwartzFreeFlow φ (t, x))‖ =
        sectionENorm volume ⊤ (schwartzFreeFlow φ) t := by
    unfold sectionENorm
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal]
    exact ht.2.ne
  rw [hleft] at hnorm
  calc
    sectionENorm volume ⊤ (schwartzFreeFlow φ) t =
        ⨆ k : ℕ, ENNReal.ofReal
          ‖spatialPairing (ht.toLp (fun x => schwartzFreeFlow φ (t, x)))
            ((b k).toLp 1 volume)‖ := hnorm
    _ = ⨆ k : ℕ, ENNReal.ofReal ‖freeFlowPairing φ (b k) t‖ := by
      apply iSup_congr
      intro k
      rw [freeFlowPairing_eq_spatialPairing φ (b k) t]

lemma natFiniteMax_tendsto (A : ℕ → ℝ → ℂ) (t : ℝ) :
    Tendsto (fun n => ENNReal.ofReal (natFiniteMax A n t)) atTop
      (𝓝 (⨆ k : ℕ, ENNReal.ofReal ‖A k t‖)) := by
  rw [← iSup_natFiniteMax A t]
  exact tendsto_atTop_iSup (natFiniteMax_mono A t)

lemma eLpNorm_ofReal_natFiniteMax (A : ℕ → ℝ → ℂ) (n : ℕ) :
    eLpNorm (fun t => ENNReal.ofReal (natFiniteMax A n t)) 4 volume =
      eLpNorm (natFiniteMax A n) 4 volume := by
  rw [show (fun t => ENNReal.ofReal (natFiniteMax A n t)) =
      ENNReal.ofReal ∘ natFiniteMax A n by rfl]
  exact eLpNorm_ofReal _
    (Filter.Eventually.of_forall fun t => natFiniteMax_nonneg A n t)

lemma eLpNorm_natFiniteMax_limit_le (A : ℕ → ℝ → ℂ) (G : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hAmeas : ∀ k, Measurable (A k))
    (hlim : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n => natFiniteMax A n t) atTop (𝓝 (G t)))
    (hfinite : ∀ n, eLpNorm (natFiniteMax A n) 4 volume ≤ C) :
    eLpNorm G 4 volume ≤ C := by
  refine Lp.eLpNorm_le_of_ae_tendsto
    (u := (atTop : Filter ℕ))
    (f := natFiniteMax A) (g := G) (C := C) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall hfinite
  · intro n
    exact (natFiniteMax_measurable A hAmeas n).aestronglyMeasurable
  · exact hlim

lemma countable_freeFlow_endpoint_bound
    (C : ℝ≥0∞) (b : ℕ → SchwartzMap ℝ ℂ)
    (hb : ∀ k, ‖(b k).toLp 1 volume‖ ≤ 1)
    (hnorming : ∀ h : Lp ℂ ⊤ (volume : Measure ℝ),
      ENNReal.ofReal ‖h‖ =
        ⨆ k : ℕ, ENNReal.ofReal ‖spatialPairing h ((b k).toLp 1 volume)‖)
    (hfinite : ∀ (n : ℕ) (φ : SchwartzMap ℝ ℂ)
      (c : Fin (n + 1) → SchwartzMap ℝ ℂ),
      (∀ i, ‖(c i).toLp 1 volume‖ ≤ 1) →
      eLpNorm (finiteMaxProfile (fun i => freeFlowPairing φ (c i))) 4 volume ≤
        C * ENNReal.ofReal ‖φ.toLp 2 volume‖)
    (φ : SchwartzMap ℝ ℂ) :
    scalarMixedENorm volume volume 4 ⊤ (schwartzFreeFlow φ) ≤
      C * ENNReal.ofReal ‖φ.toLp 2 volume‖ := by
  let A : ℕ → ℝ → ℂ := fun k => freeFlowPairing φ (b k)
  let G : ℝ → ℝ := fun t => (sectionENorm volume ⊤ (schwartzFreeFlow φ) t).toReal
  have hsectop (t : ℝ) : sectionENorm volume ⊤ (schwartzFreeFlow φ) t < ⊤ :=
    (schwartzFreeFlow_section_memLp_top φ t).2
  have hlim : ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun n => natFiniteMax A n t) atTop (𝓝 (G t)) := by
    filter_upwards with t
    have he := natFiniteMax_tendsto A t
    rw [← sectionENorm_eq_iSup_freeFlowPairing φ b hnorming t] at he
    have hr := (ENNReal.tendsto_toReal (ne_of_lt (hsectop t))).comp he
    convert hr using 1
    funext n
    exact (ENNReal.toReal_ofReal (natFiniteMax_nonneg A n t)).symm
  have hreal : eLpNorm G 4 volume ≤
      C * ENNReal.ofReal ‖φ.toLp 2 volume‖ := by
    apply eLpNorm_natFiniteMax_limit_le A G
    · intro k
      exact (freeFlowPairing_continuous φ (b k)).measurable
    · exact hlim
    · intro n
      simpa only [natFiniteMax, A] using
        hfinite n φ (fun i : Fin (n + 1) => b i.val) (fun i => hb i.val)
  unfold scalarMixedENorm
  calc
    eLpNorm (fun t => sectionENorm volume ⊤ (schwartzFreeFlow φ) t) 4 volume =
        eLpNorm G 4 volume := by
      apply eLpNorm_congr_enorm_ae
      filter_upwards with t
      simpa only [enorm_eq_self] using (Real.enorm_toReal (ne_of_lt (hsectop t))).symm
    _ ≤ C * ENNReal.ofReal ‖φ.toLp 2 volume‖ := hreal

theorem schwartz_free_endpoint_estimate :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ φ : SchwartzMap ℝ ℂ,
      scalarMixedENorm volume volume 4 ⊤ (schwartzFreeFlow φ) ≤
        C * ENNReal.ofReal ‖φ.toLp 2 volume‖ := by
  obtain ⟨C, hCtop, hfinite⟩ := finite_max_freeFlow_estimate
  obtain ⟨b, hb, hnorming⟩ := exists_schwartz_spatial_norming_sequence
  exact ⟨C, hCtop, countable_freeFlow_endpoint_bound C b hb hnorming hfinite⟩

end CubicNLSPhaseRetrieval
