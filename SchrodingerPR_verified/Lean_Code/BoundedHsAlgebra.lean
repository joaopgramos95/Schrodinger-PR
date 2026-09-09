import Lean_Code.GagliardoHalf

open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
namespace CubicNLSPhaseRetrieval

def boundedProductL2 (f g : FourierL2)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) : FourierL2 :=
  (MemLp.mul' (p := 2) (q := ∞) (r := 2)
      (⟨Lp.aestronglyMeasurable g, hg⟩ : MemLp (g : ℝ → ℂ) ∞ volume)
      (Lp.memLp f)).toLp
    (fun x => (f : ℝ → ℂ) x * (g : ℝ → ℂ) x)

lemma coe_boundedProductL2 (f g : FourierL2)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    (boundedProductL2 f g hg : ℝ → ℂ) =ᵐ[volume]
      fun x => (f : ℝ → ℂ) x * (g : ℝ → ℂ) x :=
  MemLp.coeFn_toLp _

lemma eLpNorm_translate_top (h : ℝ) (f : FourierL2) :
    eLpNorm (translateL2 h f : ℝ → ℂ) ∞ volume =
      eLpNorm (f : ℝ → ℂ) ∞ volume := by
  rw [eLpNorm_congr_ae (coe_translateL2 h f)]
  simpa [Function.comp_def, add_comm] using
    (eLpNorm_comp_measurePreserving (p := (∞ : ℝ≥0∞))
      (Lp.aestronglyMeasurable f)
      (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h))

lemma continuous_translateL2 (f : FourierL2) :
    Continuous (fun h : ℝ => translateL2 h f) := by
  let g : ℝ → C(ℝ, ℝ) := fun h =>
    ⟨fun x => x + h, continuous_id.add continuous_const⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.add continuous_fst
  have hc : Continuous (fun h : ℝ =>
      Lp.compMeasurePreserving (g h)
        (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h) f) :=
    continuous_const.compMeasurePreservingLp hg
      (fun h => MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h)
      (by norm_num)
  convert hc using 1
  funext h
  exact (translateL2LI_apply h f).symm

lemma norm_boundedProductL2_le (f g : FourierL2)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    ‖boundedProductL2 f g hg‖ₑ ≤
      ‖f‖ₑ * eLpNorm (g : ℝ → ℂ) ∞ volume := by
  rw [boundedProductL2, Lp.enorm_toLp]
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_top 2
    (Lp.aestronglyMeasurable f) (g : ℝ → ℂ) (fun x y : ℂ => x * y) 1
    (Filter.Eventually.of_forall fun x => by simp)
  simpa [Lp.enorm_def] using h

lemma boundedProductL2_sub_same (f₁ f₀ g : FourierL2)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    boundedProductL2 f₁ g hg - boundedProductL2 f₀ g hg =
      boundedProductL2 (f₁ - f₀) g hg := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (boundedProductL2 f₁ g hg)
      (boundedProductL2 f₀ g hg),
    coe_boundedProductL2 f₁ g hg, coe_boundedProductL2 f₀ g hg,
    coe_boundedProductL2 (f₁ - f₀) g hg, Lp.coeFn_sub f₁ f₀]
      with x hout h1 h0 hr hf
  rw [hout, Pi.sub_apply, h1, h0, hr, hf, Pi.sub_apply]
  ring

lemma norm_boundedProductL2_le_real (f g : FourierL2)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    ‖boundedProductL2 f g hg‖ ≤
      ‖f‖ * (eLpNorm (g : ℝ → ℂ) ∞ volume).toReal := by
  have h := norm_boundedProductL2_le f g hg
  have htop : ‖f‖ₑ * eLpNorm (g : ℝ → ℂ) ∞ volume ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top hg.ne
  have hr := ENNReal.toReal_mono htop h
  simpa only [ENNReal.toReal_mul, toReal_enorm] using hr

theorem tendsto_boundedProductL2_left {ι : Type*} {l : Filter ι}
    (fseq : ι → FourierL2) (f g : FourierL2)
    (hf : Tendsto fseq l (nhds f))
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    Tendsto (fun i => boundedProductL2 (fseq i) g hg) l
      (nhds (boundedProductL2 f g hg)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzero : Tendsto (fun i => ‖fseq i - f‖) l (nhds 0) := by
    simpa using (hf.sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => f) l (nhds f))).norm
  refine squeeze_zero (g := fun i => ‖fseq i - f‖ *
      (eLpNorm (g : ℝ → ℂ) ∞ volume).toReal) (fun i => norm_nonneg
    (boundedProductL2 (fseq i) g hg - boundedProductL2 f g hg)) (fun i => ?_) ?_
  ·
    rw [boundedProductL2_sub_same]
    exact norm_boundedProductL2_le_real (fseq i - f) g hg
  · simpa using hzero.mul_const (eLpNorm (g : ℝ → ℂ) ∞ volume).toReal

lemma boundedProductL2_translate (h : ℝ) (f g : FourierL2)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    translateL2 h (boundedProductL2 f g hg) =
      boundedProductL2 (translateL2 h f) (translateL2 h g)
        (by rw [eLpNorm_translate_top]; exact hg) := by
  apply Lp.ext
  have hpShift :=
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae
      (coe_boundedProductL2 f g hg)
  filter_upwards [coe_translateL2 h (boundedProductL2 f g hg),
    hpShift,
    coe_boundedProductL2 (translateL2 h f) (translateL2 h g)
      (by rw [eLpNorm_translate_top]; exact hg),
    coe_translateL2 h f, coe_translateL2 h g] with x hw hp hr hf hgc
  rw [hw, hr, hf, hgc, hp]

lemma boundedProductL2_sub_identity (f₁ f₀ g₁ g₀ : FourierL2)
    (hg₁ : eLpNorm (g₁ : ℝ → ℂ) ∞ volume < ∞)
    (hg₀ : eLpNorm (g₀ : ℝ → ℂ) ∞ volume < ∞)
    (hf₀ : eLpNorm (f₀ : ℝ → ℂ) ∞ volume < ∞) :
    boundedProductL2 f₁ g₁ hg₁ - boundedProductL2 f₀ g₀ hg₀ =
      boundedProductL2 (f₁ - f₀) g₁ hg₁ +
        boundedProductL2 (g₁ - g₀) f₀ hf₀ := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub f₁ f₀, Lp.coeFn_sub g₁ g₀,
    Lp.coeFn_sub (boundedProductL2 f₁ g₁ hg₁)
      (boundedProductL2 f₀ g₀ hg₀),
    Lp.coeFn_add (boundedProductL2 (f₁ - f₀) g₁ hg₁)
      (boundedProductL2 (g₁ - g₀) f₀ hf₀),
    coe_boundedProductL2 f₁ g₁ hg₁,
    coe_boundedProductL2 f₀ g₀ hg₀,
    coe_boundedProductL2 (f₁ - f₀) g₁ hg₁,
    coe_boundedProductL2 (g₁ - g₀) f₀ hf₀]
      with x hfsub hgsub houtl houtr hp11 hp00 hpd1 hp0d
  rw [houtl, houtr]
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [hp11, hp00, hpd1, hp0d, hfsub, hgsub]
  simp only [Pi.sub_apply]
  ring

lemma translationEnergy_Hs_toL2_lt_top (f : Hs (1 / 2 : ℝ)) :
    translationEnergy (Hs.toL2 (by norm_num) f) < ∞ := by
  rw [translationEnergy_eq_fourier]
  exact ENNReal.mul_lt_top halfKernelConstant_lt_top
    (homogeneousFourierEnergy_Hs_toL2_lt_top f)

private lemma sq_div_le_two_mul (n a b A B d : ℝ≥0∞)
    (hn : n ≤ a * A + b * B) :
    n ^ (2 : ℕ) / d ≤
      2 * A ^ (2 : ℕ) * (a ^ (2 : ℕ) / d) +
        2 * B ^ (2 : ℕ) * (b ^ (2 : ℕ) / d) := by
  calc
    n ^ (2 : ℕ) / d ≤ (a * A + b * B) ^ (2 : ℕ) / d := by gcongr
    _ = (a * A + b * B) ^ (2 : ℝ) / d := by norm_num
    _ ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ((a * A) ^ (2 : ℝ) + (b * B) ^ (2 : ℝ)) / d := by
      gcongr
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
    _ = 2 * A ^ (2 : ℕ) * (a ^ (2 : ℕ) / d) +
        2 * B ^ (2 : ℕ) * (b ^ (2 : ℕ) / d) := by
      norm_num [ENNReal.mul_rpow_of_nonneg]
      simp only [div_eq_mul_inv]
      ring

lemma enorm_translate_boundedProduct_sub_le (h : ℝ) (f g : FourierL2)
    (hf : eLpNorm (f : ℝ → ℂ) ∞ volume < ∞)
    (hg : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    ‖translateL2 h (boundedProductL2 f g hg) - boundedProductL2 f g hg‖ₑ ≤
      ‖translateL2 h f - f‖ₑ * eLpNorm (g : ℝ → ℂ) ∞ volume +
        ‖translateL2 h g - g‖ₑ * eLpNorm (f : ℝ → ℂ) ∞ volume := by
  let hgt : eLpNorm (translateL2 h g : ℝ → ℂ) ∞ volume < ∞ := by
    rw [eLpNorm_translate_top]
    exact hg
  rw [boundedProductL2_translate h f g hg]
  rw [boundedProductL2_sub_identity (translateL2 h f) f
    (translateL2 h g) g hgt hg hf]
  calc
    ‖boundedProductL2 (translateL2 h f - f) (translateL2 h g) hgt +
        boundedProductL2 (translateL2 h g - g) f hf‖ₑ ≤
      ‖boundedProductL2 (translateL2 h f - f) (translateL2 h g) hgt‖ₑ +
        ‖boundedProductL2 (translateL2 h g - g) f hf‖ₑ := enorm_add_le _ _
    _ ≤ ‖translateL2 h f - f‖ₑ *
          eLpNorm (translateL2 h g : ℝ → ℂ) ∞ volume +
        ‖translateL2 h g - g‖ₑ *
          eLpNorm (f : ℝ → ℂ) ∞ volume := add_le_add
      (norm_boundedProductL2_le _ _ hgt) (norm_boundedProductL2_le _ _ hf)
    _ = _ := by rw [eLpNorm_translate_top]

set_option maxHeartbeats 1000000 in
/-- Quantitative Gagliardo product estimate in the bounded critical algebra. -/
theorem translationEnergy_boundedProductL2_le (f g : FourierL2)
    (hfTop : eLpNorm (f : ℝ → ℂ) ∞ volume < ∞)
    (hgTop : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    translationEnergy (boundedProductL2 f g hgTop) ≤
      2 * eLpNorm (g : ℝ → ℂ) ∞ volume ^ (2 : ℕ) * translationEnergy f +
        2 * eLpNorm (f : ℝ → ℂ) ∞ volume ^ (2 : ℕ) * translationEnergy g := by
  let A : ℝ≥0∞ := eLpNorm (g : ℝ → ℂ) ∞ volume
  let B : ℝ≥0∞ := eLpNorm (f : ℝ → ℂ) ∞ volume
  have hpoint : ∀ h : ℝ,
      ‖translateL2 h (boundedProductL2 f g hgTop) -
          boundedProductL2 f g hgTop‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)) ≤
        2 * A ^ (2 : ℕ) *
          (‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) +
        2 * B ^ (2 : ℕ) *
          (‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) := by
    intro h
    exact sq_div_le_two_mul _ _ _ A B _
      (by simpa [A, B] using enorm_translate_boundedProduct_sub_le h f g hfTop hgTop)
  unfold translationEnergy
  have hmeasF : AEMeasurable (fun h : ℝ =>
      ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ))) volume := by
    exact (((continuous_translateL2 f).sub continuous_const).aestronglyMeasurable.enorm.pow_const 2).div
      (by fun_prop)
  have hmeasG : AEMeasurable (fun h : ℝ =>
      ‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ))) volume := by
    exact (((continuous_translateL2 g).sub continuous_const).aestronglyMeasurable.enorm.pow_const 2).div
      (by fun_prop)
  have hmeasTermF : AEMeasurable (fun h : ℝ =>
      (2 * A ^ (2 : ℕ)) *
        (‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)))) volume :=
    measurable_const.aemeasurable.mul hmeasF
  calc
    (∫⁻ h : ℝ, ‖translateL2 h (boundedProductL2 f g hgTop) -
        boundedProductL2 f g hgTop‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ))) ≤
      ∫⁻ h : ℝ,
        (2 * A ^ (2 : ℕ)) *
            (‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) +
          (2 * B ^ (2 : ℕ)) *
            (‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) := lintegral_mono hpoint
    _ = (2 * A ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) +
        (2 * B ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) := by
      rw [lintegral_add_left']
      · rw [lintegral_const_mul'' _ hmeasF, lintegral_const_mul'' _ hmeasG]
      · exact hmeasTermF
    _ = _ := by rfl

/-- Fourier form of the quantitative critical product estimate. -/
theorem homogeneousFourierEnergy_boundedProductL2_le (f g : FourierL2)
    (hfTop : eLpNorm (f : ℝ → ℂ) ∞ volume < ∞)
    (hgTop : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞) :
    homogeneousFourierEnergy (1 / 2 : ℝ) (boundedProductL2 f g hgTop) ≤
      2 * eLpNorm (g : ℝ → ℂ) ∞ volume ^ (2 : ℕ) *
          homogeneousFourierEnergy (1 / 2 : ℝ) f +
        2 * eLpNorm (f : ℝ → ℂ) ∞ volume ^ (2 : ℕ) *
          homogeneousFourierEnergy (1 / 2 : ℝ) g := by
  rw [← ENNReal.mul_le_mul_iff_right halfKernelConstant_pos.ne'
    halfKernelConstant_lt_top.ne]
  rw [mul_add]
  have h := translationEnergy_boundedProductL2_le f g hfTop hgTop
  simp only [translationEnergy_eq_fourier] at h
  simpa only [mul_assoc, mul_left_comm] using h

set_option maxHeartbeats 1000000 in
theorem translationEnergy_boundedProductL2_lt_top (f g : FourierL2)
    (hfTop : eLpNorm (f : ℝ → ℂ) ∞ volume < ∞)
    (hgTop : eLpNorm (g : ℝ → ℂ) ∞ volume < ∞)
    (hfEnergy : translationEnergy f < ∞)
    (hgEnergy : translationEnergy g < ∞) :
    translationEnergy (boundedProductL2 f g hgTop) < ∞ := by
  let A : ℝ≥0∞ := eLpNorm (g : ℝ → ℂ) ∞ volume
  let B : ℝ≥0∞ := eLpNorm (f : ℝ → ℂ) ∞ volume
  have hpoint : ∀ h : ℝ,
      ‖translateL2 h (boundedProductL2 f g hgTop) -
          boundedProductL2 f g hgTop‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)) ≤
        2 * A ^ (2 : ℕ) *
          (‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) +
        2 * B ^ (2 : ℕ) *
          (‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) := by
    intro h
    exact sq_div_le_two_mul _ _ _ A B _
      (by simpa [A, B] using enorm_translate_boundedProduct_sub_le h f g hfTop hgTop)
  unfold translationEnergy
  have hmeasF : AEMeasurable (fun h : ℝ =>
      ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ))) volume := by
    exact (((continuous_translateL2 f).sub continuous_const).aestronglyMeasurable.enorm.pow_const 2).div
      (by fun_prop)
  have hmeasG : AEMeasurable (fun h : ℝ =>
      ‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
        ENNReal.ofReal (|h| ^ (2 : ℕ))) volume := by
    exact (((continuous_translateL2 g).sub continuous_const).aestronglyMeasurable.enorm.pow_const 2).div
      (by fun_prop)
  have hmeasTermF : AEMeasurable (fun h : ℝ =>
      (2 * A ^ (2 : ℕ)) *
        (‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ)))) volume :=
    measurable_const.aemeasurable.mul hmeasF
  calc
    (∫⁻ h : ℝ, ‖translateL2 h (boundedProductL2 f g hgTop) -
        boundedProductL2 f g hgTop‖ₑ ^ (2 : ℕ) /
          ENNReal.ofReal (|h| ^ (2 : ℕ))) ≤
      ∫⁻ h : ℝ,
        (2 * A ^ (2 : ℕ)) *
            (‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) +
          (2 * B ^ (2 : ℕ)) *
            (‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
              ENNReal.ofReal (|h| ^ (2 : ℕ))) := lintegral_mono hpoint
    _ = (2 * A ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ‖translateL2 h f - f‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) +
        (2 * B ^ (2 : ℕ)) *
          (∫⁻ h : ℝ, ‖translateL2 h g - g‖ₑ ^ (2 : ℕ) /
            ENNReal.ofReal (|h| ^ (2 : ℕ))) := by
      rw [lintegral_add_left']
      · rw [lintegral_const_mul'' _ hmeasF, lintegral_const_mul'' _ hmeasG]
      · exact hmeasTermF
    _ < ∞ := by
      apply ENNReal.add_lt_top.mpr
      constructor
      · exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hgTop)) hfEnergy
      · exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hfTop)) hgEnergy

/-- The product of two bounded critical Sobolev functions is again in
`H^{1/2}`.  This is the precise Gagliardo algebra statement used by the
zero-safe Wronskian argument. -/
theorem boundedHs_product_exists (f g : Hs (1 / 2 : ℝ))
    (hfTop : eLpNorm (Hs.toL2 (by norm_num) f : ℝ → ℂ) ∞ volume < ∞)
    (hgTop : eLpNorm (Hs.toL2 (by norm_num) g : ℝ → ℂ) ∞ volume < ∞) :
    ∃ p : Hs (1 / 2 : ℝ),
      Hs.toL2 (by norm_num) p =
        boundedProductL2 (Hs.toL2 (by norm_num) f)
          (Hs.toL2 (by norm_num) g) hgTop ∧
      (Hs.toL2 (by norm_num) p : ℝ → ℂ) =ᵐ[volume]
        fun x => (Hs.toL2 (by norm_num) f : ℝ → ℂ) x *
          (Hs.toL2 (by norm_num) g : ℝ → ℂ) x := by
  let F : FourierL2 := Hs.toL2 (by norm_num) f
  let G : FourierL2 := Hs.toL2 (by norm_num) g
  let w : FourierL2 := boundedProductL2 F G hgTop
  have hwEnergy : translationEnergy w < ∞ :=
    translationEnergy_boundedProductL2_lt_top F G hfTop hgTop
      (translationEnergy_Hs_toL2_lt_top f)
      (translationEnergy_Hs_toL2_lt_top g)
  have hwHom : homogeneousFourierEnergy (1 / 2 : ℝ) w < ∞ := by
    by_contra hn
    have htop : homogeneousFourierEnergy (1 / 2 : ℝ) w = ∞ :=
      top_unique (le_of_not_gt hn)
    rw [translationEnergy_eq_fourier, htop,
      ENNReal.mul_top halfKernelConstant_pos.ne'] at hwEnergy
    exact (ne_of_lt hwEnergy) rfl
  obtain ⟨p, hp⟩ := exists_Hs_half_of_homogeneousFourierEnergy_lt_top w hwHom
  refine ⟨p, hp, ?_⟩
  rw [hp]
  exact coe_boundedProductL2 F G hgTop

private def quadraticWeightedSchwartzForHs (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => (((1 + y ^ 2 : ℝ) : ℂ))) φ

private lemma quadraticWeightedSchwartzForHs_apply (φ : SchwartzMap ℝ ℂ) (y : ℝ) :
    quadraticWeightedSchwartzForHs φ y = ((1 + y ^ 2 : ℝ) : ℂ) * φ y := by
  have h := SchwartzMap.smulLeftCLM_apply
    (show (fun y : ℝ => (((1 + y ^ 2 : ℝ) : ℂ))).HasTemperateGrowth by fun_prop) φ
  exact congrFun h y

/-- Every Schwartz function has its canonical physical realization in
`H^{1/2}`. -/
theorem schwartz_Hs_half_exists (φ : SchwartzMap ℝ ℂ) :
    ∃ f : Hs (1 / 2 : ℝ), Hs.toL2 (by norm_num) f = φ.toLp 2 volume := by
  let q : SchwartzMap ℝ ℂ := quadraticWeightedSchwartzForHs (FourierTransform.fourier φ)
  have hfourier :
      (sobolevFourier (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
        fun ξ => (FourierTransform.fourier φ) ξ := by
    have heq : sobolevFourier (φ.toLp 2 volume) =
        (FourierTransform.fourier φ).toLp 2 volume :=
      SchwartzMap.toLp_fourier_eq φ
    rw [heq]
    exact (FourierTransform.fourier φ).coeFn_toLp 2 volume
  have hqfin : (∫⁻ ξ : ℝ, ‖q ξ‖ₑ ^ (2 : ℝ)) < ∞ := by
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (q.memLp 2 volume).2
  have hhom : homogeneousFourierEnergy (1 / 2 : ℝ)
      (φ.toLp 2 volume) < ∞ := by
    rw [homogeneousFourierEnergy]
    apply lt_of_le_of_lt _ hqfin
    apply lintegral_mono_ae
    filter_upwards [hfourier] with ξ hξ
    rw [hξ]
    change ENNReal.ofReal (|ξ| ^ (2 * (1 / 2 : ℝ))) *
        ‖(FourierTransform.fourier φ) ξ‖ₑ ^ (2 : ℕ) ≤
      ‖q ξ‖ₑ ^ (2 : ℝ)
    have hpow : |ξ| ^ (2 * (1 / 2 : ℝ)) = |ξ| := by norm_num
    rw [hpow]
    have hxi : ENNReal.ofReal |ξ| ≤
        (ENNReal.ofReal (1 + ξ ^ 2)) ^ (2 : ℕ) := by
      rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 + ξ ^ 2)]
      apply ENNReal.ofReal_le_ofReal
      have h1 : |ξ| ≤ 1 + ξ ^ 2 := by
        nlinarith [sq_nonneg (|ξ| - 1), sq_abs ξ]
      have h2 : 1 + ξ ^ 2 ≤ (1 + ξ ^ 2) ^ 2 := by
        nlinarith [sq_nonneg ξ]
      exact h1.trans h2
    rw [show q ξ = ((1 + ξ ^ 2 : ℝ) : ℂ) *
        (FourierTransform.fourier φ) ξ by
      exact quadraticWeightedSchwartzForHs_apply _ _]
    rw [enorm_mul, ENNReal.rpow_two]
    calc
      ENNReal.ofReal |ξ| * ‖(FourierTransform.fourier φ) ξ‖ₑ ^ (2 : ℕ) ≤
          (ENNReal.ofReal (1 + ξ ^ 2)) ^ (2 : ℕ) *
            ‖(FourierTransform.fourier φ) ξ‖ₑ ^ (2 : ℕ) := by gcongr
      _ = (‖(((1 + ξ ^ 2 : ℝ) : ℂ))‖ₑ *
          ‖(FourierTransform.fourier φ) ξ‖ₑ) ^ (2 : ℕ) := by
        rw [show ‖(((1 + ξ ^ 2 : ℝ) : ℂ))‖ₑ =
            ENNReal.ofReal (1 + ξ ^ 2) by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]]
        ring
  exact exists_Hs_half_of_homogeneousFourierEnergy_lt_top
    (φ.toLp 2 volume) hhom

end CubicNLSPhaseRetrieval
