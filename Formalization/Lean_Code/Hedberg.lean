import Lean_Code.FractionalDefinitions

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

private lemma hedberg_real_exponents (α : ℝ) (hα1 : α < 1)
    (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq_top : q ≠ ⊤)
    (hexp : q⁻¹ = p⁻¹ - ENNReal.ofReal (1 - α)) :
    let pr := p.toReal
    let qr := q.toReal
    0 < pr ∧ 0 < qr ∧ pr < qr ∧
      qr⁻¹ = pr⁻¹ - (1 - α) ∧
      pr * (1 - α) = 1 - pr / qr := by
  dsimp
  have hp_top : p ≠ ⊤ := ne_top_of_lt hpq
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (lt_trans (by norm_num) hp) hpq)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq_top
  have hprqr : p.toReal < q.toReal := ENNReal.toReal_strict_mono hq_top hpq
  have hqinvpos : 0 < q⁻¹ := ENNReal.inv_pos.mpr hq_top
  have hsubpos : 0 < p⁻¹ - ENNReal.ofReal (1 - α) := by simpa [← hexp]
  have hle : ENNReal.ofReal (1 - α) ≤ p⁻¹ :=
    (tsub_pos_iff_lt.mp hsubpos).le
  have hpinvtop : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hp0
  have hreal := congrArg ENNReal.toReal hexp
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hle hpinvtop,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hα1.le)] at hreal
  refine ⟨hpr, hqr, hprqr, hreal, ?_⟩
  field_simp at hreal ⊢
  nlinarith

private lemma interval_lintegral_le_maximal (F : ℝ → ℂ) (t r : ℝ) (hr : 0 < r) :
    (∫⁻ s in Set.Icc (t - r) (t + r), ‖F s‖ₑ ∂volume) ≤
      ENNReal.ofReal (2 * r) * centeredMaximal F t := by
  let rad : ℝ≥0∞ := ENNReal.ofReal (2 * r)
  have hrpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hr0 : rad ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hrpos
  have hrtop : rad ≠ ⊤ := ENNReal.ofReal_ne_top
  have hterm : rad⁻¹ *
      (∫⁻ s in Set.Icc (t - r) (t + r), ‖F s‖ₑ ∂volume) ≤
        centeredMaximal F t := by
    unfold centeredMaximal
    have hi := le_iSup (fun R : {R : ℝ // 0 < R} =>
      ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
        ∫⁻ s in Set.Icc (t - R) (t + R), ‖F s‖₊ ∂volume) ⟨r, hr⟩
    simpa only [rad, ENNReal.ofReal_inv_of_pos hrpos, enorm_eq_nnnorm] using hi
  calc
    (∫⁻ s in Set.Icc (t - r) (t + r), ‖F s‖ₑ ∂volume) =
        rad * (rad⁻¹ *
          ∫⁻ s in Set.Icc (t - r) (t + r), ‖F s‖ₑ ∂volume) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hr0 hrtop, one_mul]
    _ ≤ rad * centeredMaximal F t := mul_le_mul_left' hterm rad

private lemma lintegral_Ici_rpow_of_lt (exponent R : ℝ) (he : exponent < -1)
    (hR : 0 < R) :
    (∫⁻ u in Set.Ici R, ENNReal.ofReal (u ^ exponent) ∂volume) =
      ENNReal.ofReal (-R ^ (exponent + 1) / (exponent + 1)) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  have hint : IntegrableOn (fun u : ℝ => u ^ exponent) (Set.Ioi R) :=
    integrableOn_Ioi_rpow_of_lt he hR
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi R)]
      (fun u : ℝ => u ^ exponent) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi R))]
      with u hu
    exact Real.rpow_nonneg (hR.trans hu).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_Ioi_rpow_of_lt he hR]

private lemma lintegral_abs_rpow_Iic (exponent R : ℝ) (he : exponent < -1)
    (hR : 0 < R) :
    (∫⁻ u in Set.Iic (-R), ENNReal.ofReal (|u| ^ exponent) ∂volume) =
      ENNReal.ofReal (-R ^ (exponent + 1) / (exponent + 1)) := by
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hf : Measurable (fun u : ℝ => ENNReal.ofReal (|u| ^ exponent)) := by
    fun_prop
  have hchange := hmp.setLIntegral_comp_preimage (measurableSet_Ici :
      MeasurableSet (Set.Ici R)) hf
  have hpre : (fun u : ℝ => -u) ⁻¹' Set.Ici R = Set.Iic (-R) := by
    ext u
    simp
  rw [hpre] at hchange
  calc
    (∫⁻ u in Set.Iic (-R), ENNReal.ofReal (|u| ^ exponent) ∂volume) =
        ∫⁻ u in Set.Ici R, ENNReal.ofReal (|u| ^ exponent) ∂volume := by
      simpa only [abs_neg] using hchange
    _ = ∫⁻ u in Set.Ici R, ENNReal.ofReal (u ^ exponent) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro u hu
      change ENNReal.ofReal (|u| ^ exponent) = ENNReal.ofReal (u ^ exponent)
      rw [abs_of_nonneg (hR.le.trans hu)]
    _ = ENNReal.ofReal (-R ^ (exponent + 1) / (exponent + 1)) :=
      lintegral_Ici_rpow_of_lt exponent R he hR

private lemma lintegral_abs_rpow_exterior (exponent R : ℝ) (he : exponent < -1)
    (hR : 0 < R) :
    (∫⁻ u in {u : ℝ | R ≤ |u|}, ENNReal.ofReal (|u| ^ exponent) ∂volume) =
      2 * ENNReal.ofReal (-R ^ (exponent + 1) / (exponent + 1)) := by
  have hset : {u : ℝ | R ≤ |u|} = Set.Iic (-R) ∪ Set.Ici R := by
    ext u
    simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici]
    constructor
    · intro hu
      rcases le_total u 0 with hu0 | h0u
      · left
        rw [abs_of_nonpos hu0] at hu
        linarith
      · right
        simpa [abs_of_nonneg h0u] using hu
    · intro hu
      rcases hu with hu | hu
      · rw [abs_of_nonpos (le_trans hu (neg_nonpos.mpr hR.le))]
        linarith
      · exact hu.trans_eq (abs_of_nonneg (hR.le.trans hu)).symm
  rw [hset, lintegral_union measurableSet_Ici]
  · rw [lintegral_abs_rpow_Iic exponent R he hR]
    have hpos : ∀ u ∈ Set.Ici R, |u| = u := by
      intro u hu
      exact abs_of_nonneg (hR.le.trans hu)
    rw [setLIntegral_congr_fun measurableSet_Ici (fun u hu => by rw [hpos u hu])]
    rw [lintegral_Ici_rpow_of_lt exponent R he hR]
    ring
  · exact Set.disjoint_left.2 (fun u hu hv => by
      simp only [mem_Iic] at hu
      simp only [mem_Ici] at hv
      linarith)

private lemma lintegral_sub_abs_rpow_exterior (exponent R t : ℝ)
    (he : exponent < -1) (hR : 0 < R) :
    (∫⁻ s in {s : ℝ | R ≤ |t - s|}, ENNReal.ofReal (|t - s| ^ exponent) ∂volume) =
      2 * ENNReal.ofReal (-R ^ (exponent + 1) / (exponent + 1)) := by
  let g : ℝ → ℝ := fun s => t - s
  have hmp : MeasurePreserving g volume volume := by
    convert (measurePreserving_add_left volume t).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ)) using 1 <;>
      funext s <;> simp only [g, Function.comp_apply, sub_eq_add_neg]
  have hf : Measurable (fun u : ℝ => ENNReal.ofReal (|u| ^ exponent)) := by
    fun_prop
  have hchange := hmp.setLIntegral_comp_preimage
    (show MeasurableSet {u : ℝ | R ≤ |u|} by
      exact measurableSet_le measurable_const measurable_abs) hf
  have hpre : g ⁻¹' {u : ℝ | R ≤ |u|} = {s : ℝ | R ≤ |t - s|} := by
    rfl
  rw [hpre] at hchange
  calc
    (∫⁻ s in {s : ℝ | R ≤ |t - s|}, ENNReal.ofReal (|t - s| ^ exponent) ∂volume) =
        ∫⁻ u in {u : ℝ | R ≤ |u|}, ENNReal.ofReal (|u| ^ exponent) ∂volume := by
      simpa only [g] using hchange
    _ = 2 * ENNReal.ofReal (-R ^ (exponent + 1) / (exponent + 1)) :=
      lintegral_abs_rpow_exterior exponent R he hR

private lemma hedberg_far_bound (alpha pconj : ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (hconj : Real.HolderConjugate pconj p.toReal)
    (hexterior : -alpha * pconj < -1)
    (F : ℝ → ℂ) (hF : MemLp F p volume) (t R : ℝ) (hR : 0 < R) :
    (∫⁻ s in {s : ℝ | R ≤ |t - s|},
        ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖F s‖ₑ ∂volume) ≤
      (2 * ENNReal.ofReal (-R ^ ((-alpha * pconj) + 1) /
        ((-alpha * pconj) + 1))) ^ (1 / pconj) * eLpNorm F p volume := by
  let S : Set ℝ := {s : ℝ | R ≤ |t - s|}
  let k : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (|t - s| ^ (-alpha))
  have hk : AEMeasurable k (volume.restrict S) := by
    apply Measurable.aemeasurable
    dsimp [k]
    fun_prop
  have hFnorm : AEMeasurable (fun s : ℝ => ‖F s‖ₑ) (volume.restrict S) :=
    hF.1.enorm.mono_measure Measure.restrict_le_self
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict S) hconj hk hFnorm
  have hkpow : (∫⁻ s in S, k s ^ pconj ∂volume) =
      2 * ENNReal.ofReal (-R ^ ((-alpha * pconj) + 1) /
        ((-alpha * pconj) + 1)) := by
    calc
      (∫⁻ s in S, k s ^ pconj ∂volume) =
          ∫⁻ s in S, ENNReal.ofReal (|t - s| ^ (-alpha * pconj)) ∂volume := by
        apply setLIntegral_congr_fun
          (show MeasurableSet S by
            exact measurableSet_le measurable_const (measurable_abs.comp
              (measurable_const.sub measurable_id)))
        intro s hs
        dsimp [k]
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hconj.nonneg]
        congr 1
        rw [← Real.rpow_mul (abs_nonneg _)]
      _ = 2 * ENNReal.ofReal (-R ^ ((-alpha * pconj) + 1) /
          ((-alpha * pconj) + 1)) := by
        exact lintegral_sub_abs_rpow_exterior (-alpha * pconj) R t hexterior hR
  have hnorm : (∫⁻ s in S, ‖F s‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) ≤
      eLpNorm F p volume := by
    rw [← eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
    exact eLpNorm_mono_measure F Measure.restrict_le_self
  change (∫⁻ s in S, (k * fun s => ‖F s‖ₑ) s ∂volume) ≤ _
  calc
    (∫⁻ s in S, (k * fun s => ‖F s‖ₑ) s ∂volume) ≤
        (∫⁻ s in S, k s ^ pconj ∂volume) ^ (1 / pconj) *
          (∫⁻ s in S, ‖F s‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) := hholder
    _ ≤ (2 * ENNReal.ofReal (-R ^ ((-alpha * pconj) + 1) /
          ((-alpha * pconj) + 1))) ^ (1 / pconj) * eLpNorm F p volume := by
      rw [hkpow]
      exact mul_le_mul_left' hnorm _

private lemma measurable_sub_abs_rpow (alpha t : ℝ) :
    Measurable (fun s : ℝ => |t - s| ^ (-alpha)) := by
  apply (show ContinuousOn (fun s : ℝ => |t - s| ^ (-alpha)) ({t} : Set ℝ)ᶜ by
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro s hs
      left
      exact abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm (by simpa using hs)))).measurable_of_countable_compl
  simpa using Set.countable_singleton t

private lemma withDensity_le_maximal_on_interval (F : ℝ → ℂ)
    (hFm : StronglyMeasurable F) (t r : ℝ) (hr : 0 < r)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Icc (t - r) (t + r)) :
    (volume.withDensity fun s : ℝ => ‖F s‖ₑ) A ≤
      ENNReal.ofReal (2 * r) * centeredMaximal F t := by
  rw [MeasureTheory.withDensity_apply _ hA]
  exact (lintegral_mono_set hsub).trans (interval_lintegral_le_maximal F t r hr)

private lemma hedberg_kernel_distribution (alpha : ℝ) (h_alpha : 0 < alpha)
    (F : ℝ → ℂ) (hFm : StronglyMeasurable F) (t R lambda : ℝ)
    (hR : 0 < R) (hlambda : 0 < lambda) :
    let B := Set.Icc (t - R) (t + R)
    let G : ℝ → ℝ := B.indicator (fun s => |t - s| ^ (-alpha))
    (volume.withDensity fun s : ℝ => ‖F s‖ₑ) {s : ℝ | lambda < G s} ≤
      if lambda ≤ R ^ (-alpha) then
        ENNReal.ofReal (2 * R) * centeredMaximal F t
      else
        ENNReal.ofReal (2 * lambda ^ (-alpha)⁻¹) * centeredMaximal F t := by
  dsimp only
  let B := Set.Icc (t - R) (t + R)
  let G : ℝ → ℝ := B.indicator (fun s => |t - s| ^ (-alpha))
  have hG : Measurable G :=
    (measurable_sub_abs_rpow alpha t).indicator measurableSet_Icc
  have hset : MeasurableSet {s : ℝ | lambda < G s} :=
    measurableSet_lt measurable_const hG
  by_cases hlambdaR : lambda ≤ R ^ (-alpha)
  · rw [if_pos hlambdaR]
    apply withDensity_le_maximal_on_interval F hFm t R hR _ hset
    intro s hs
    by_contra hsB
    have hzero : G s = 0 := Set.indicator_of_notMem hsB _
    have : lambda < 0 := by simpa [hzero] using hs
    linarith
  · rw [if_neg hlambdaR]
    let rho : ℝ := lambda ^ (-alpha)⁻¹
    have hrho : 0 < rho := Real.rpow_pos_of_pos hlambda _
    apply withDensity_le_maximal_on_interval F hFm t rho hrho _ hset
    intro s hs
    have hsB : s ∈ B := by
      by_contra hsB
      have hzero : G s = 0 := Set.indicator_of_notMem hsB _
      have : lambda < 0 := by simpa [hzero] using hs
      linarith
    have hkernel : lambda < |t - s| ^ (-alpha) := by
      change lambda < G s at hs
      simpa [G, hsB] using hs
    have hdpos : 0 < |t - s| := by
      apply lt_of_le_of_ne (abs_nonneg _) ?_
      intro hd0
      rw [hd0.symm, Real.zero_rpow (neg_ne_zero.mpr h_alpha.ne')] at hkernel
      linarith
    have hz : (-alpha)⁻¹ < 0 := inv_neg''.mpr (neg_lt_zero.mpr h_alpha)
    have hdrho : |t - s| < rho := by
      apply (Real.lt_rpow_inv_iff_of_neg hlambda hdpos hz).mp
      simpa only [inv_inv, rho] using hkernel
    constructor <;> dsimp [rho] <;> linarith [neg_lt_of_abs_lt hdrho, lt_of_abs_lt hdrho]

private lemma measurable_rpow_const (z : ℝ) : Measurable (fun x : ℝ => x ^ z) := by
  apply (continuousOn_id.rpow_const (s := ({0} : Set ℝ)ᶜ) ?_).measurable_of_countable_compl
  · simpa using Set.countable_singleton (0 : ℝ)
  · intro x hx
    exact Or.inl (by simpa using hx)

private lemma hedberg_low_real_identity (alpha R : ℝ) (hR : 0 < R) :
    R ^ (-alpha) * (2 * R) = 2 * R ^ (1 - alpha) := by
  rw [show 1 - alpha = -alpha + 1 by ring, Real.rpow_add hR,
    Real.rpow_one]
  ring

private lemma hedberg_high_real_identity (alpha R : ℝ)
    (h_alpha : 0 < alpha) (h_alpha_one : alpha < 1) (hR : 0 < R) :
    -(R ^ (-alpha)) ^ ((-alpha)⁻¹ + 1) / ((-alpha)⁻¹ + 1) =
      alpha / (1 - alpha) * R ^ (1 - alpha) := by
  have ha0 : alpha ≠ 0 := h_alpha.ne'
  have hna0 : -alpha ≠ 0 := neg_ne_zero.mpr ha0
  have hexp : (-alpha) * ((-alpha)⁻¹ + 1) = 1 - alpha := by
    field_simp
    ring
  rw [← Real.rpow_mul hR.le, hexp]
  field_simp
  rw [show -1 + alpha = -(1 - alpha) by ring]
  simp only [one_div, inv_neg, neg_neg]

private lemma hedberg_near_bound (alpha : ℝ) (h_alpha : 0 < alpha)
    (h_alpha_one : alpha < 1) (F : ℝ → ℂ) (hFm : StronglyMeasurable F)
    (t R : ℝ) (hR : 0 < R) :
    (∫⁻ s in Set.Icc (t - R) (t + R),
        ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖F s‖ₑ ∂volume) ≤
      ENNReal.ofReal (2 + 2 * alpha / (1 - alpha)) *
        ENNReal.ofReal (R ^ (1 - alpha)) * centeredMaximal F t := by
  let B : Set ℝ := Set.Icc (t - R) (t + R)
  let G : ℝ → ℝ := B.indicator (fun s => |t - s| ^ (-alpha))
  let nu : Measure ℝ := volume.withDensity fun s : ℝ => ‖F s‖ₑ
  let A : ℝ := R ^ (-alpha)
  let z : ℝ := (-alpha)⁻¹
  let M : ℝ≥0∞ := centeredMaximal F t
  have hA : 0 < A := Real.rpow_pos_of_pos hR _
  have hz : z < -1 := by
    dsimp [z]
    rw [inv_neg, neg_lt_neg_iff]
    exact (one_lt_inv₀ h_alpha).mpr h_alpha_one
  have hG : Measurable G :=
    (measurable_sub_abs_rpow alpha t).indicator measurableSet_Icc
  have hGnonneg : ∀ s, 0 ≤ G s := by
    intro s
    by_cases hs : s ∈ B <;> simp [G, hs, Real.rpow_nonneg]
  have hleft :
      (∫⁻ s in B, ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖F s‖ₑ ∂volume) =
        ∫⁻ s, ENNReal.ofReal (G s) ∂nu := by
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume hFm.enorm hG.ennreal_ofReal]
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ B
    · simp only [Set.indicator_of_mem hs, G, Pi.mul_apply]
      rw [Set.indicator_of_mem hs]
      ac_rfl
    · have hs' : s ∉ Set.Icc (t - R) (t + R) := by simpa [B] using hs
      rw [Set.indicator_of_notMem hs']
      simp [G, hs]
  rw [hleft, MeasureTheory.lintegral_eq_lintegral_meas_lt nu
    (Filter.Eventually.of_forall hGnonneg) hG.aemeasurable]
  let D : ℝ → ℝ≥0∞ := fun lambda => nu {s : ℝ | lambda < G s}
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 A ∪ Set.Ioi A := by
    ext lambda
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hlambda
      rcases le_total lambda A with hle | hge
      · exact Or.inl ⟨hlambda, hle⟩
      · rcases hge.eq_or_lt with heq | hlt
        · exact Or.inl ⟨hlambda, heq.symm.le⟩
        · exact Or.inr hlt
    · rintro (⟨hlambda, _⟩ | hlambda)
      · exact hlambda
      · exact hA.trans hlambda
  have hdisj : Disjoint (Set.Ioc 0 A) (Set.Ioi A) := by
    exact Set.disjoint_left.2 (fun lambda hl hhigh => by
      simp only [mem_Ioc] at hl
      simp only [mem_Ioi] at hhigh
      linarith)
  change (∫⁻ lambda in Set.Ioi (0 : ℝ), D lambda ∂volume) ≤ _
  rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  have hlow : (∫⁻ lambda in Set.Ioc 0 A, D lambda ∂volume) ≤
      ENNReal.ofReal (2 * R) * M * ENNReal.ofReal A := by
    calc
      (∫⁻ lambda in Set.Ioc 0 A, D lambda ∂volume) ≤
          ∫⁻ _lambda in Set.Ioc 0 A, ENNReal.ofReal (2 * R) * M ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict
          (measurableSet_Ioc : MeasurableSet (Set.Ioc 0 A))] with lambda hlambda
        exact (hedberg_kernel_distribution alpha h_alpha F hFm t R lambda hR
          hlambda.1).trans_eq (if_pos hlambda.2)
      _ = ENNReal.ofReal (2 * R) * M * ENNReal.ofReal A := by
        rw [setLIntegral_const, Real.volume_Ioc]
        simp only [sub_zero]
  have hhigh : (∫⁻ lambda in Set.Ioi A, D lambda ∂volume) ≤
      2 * ENNReal.ofReal (-A ^ (z + 1) / (z + 1)) * M := by
    calc
      (∫⁻ lambda in Set.Ioi A, D lambda ∂volume) ≤
          ∫⁻ lambda in Set.Ioi A,
            ENNReal.ofReal (2 * lambda ^ z) * M ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict
          (measurableSet_Ioi : MeasurableSet (Set.Ioi A))] with lambda hlambda
        have hlambda0 : 0 < lambda := hA.trans hlambda
        have hb := hedberg_kernel_distribution alpha h_alpha F hFm t R lambda hR hlambda0
        rw [if_neg (not_le.mpr hlambda)] at hb
        simpa only [z, M] using hb
      _ = 2 * ENNReal.ofReal (-A ^ (z + 1) / (z + 1)) * M := by
        have hmeas : Measurable (fun lambda : ℝ => ENNReal.ofReal (2 * lambda ^ z)) :=
          ENNReal.continuous_ofReal.measurable.comp
            (measurable_const.mul (measurable_rpow_const z))
        rw [lintegral_mul_const M hmeas]
        have hpoint : ∀ lambda ∈ Set.Ioi A,
            ENNReal.ofReal (2 * lambda ^ z) =
              2 * ENNReal.ofReal (lambda ^ z) := by
          intro lambda hlambda
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [setLIntegral_congr_fun measurableSet_Ioi hpoint]
        have hpowmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ z)) :=
          ENNReal.continuous_ofReal.measurable.comp (measurable_rpow_const z)
        rw [@lintegral_const_mul ℝ _ (volume.restrict (Set.Ioi A)) 2 _ hpowmeas]
        rw [restrict_Ioi_eq_restrict_Ici]
        rw [lintegral_Ici_rpow_of_lt z A hz hA]
  calc
    (∫⁻ lambda in Set.Ioc 0 A, D lambda ∂volume) +
        ∫⁻ lambda in Set.Ioi A, D lambda ∂volume ≤
      ENNReal.ofReal (2 * R) * M * ENNReal.ofReal A +
        2 * ENNReal.ofReal (-A ^ (z + 1) / (z + 1)) * M := add_le_add hlow hhigh
    _ = ENNReal.ofReal (2 + 2 * alpha / (1 - alpha)) *
        ENNReal.ofReal (R ^ (1 - alpha)) * M := by
      dsimp [A, z, M]
      rw [hedberg_high_real_identity alpha R h_alpha h_alpha_one hR]
      have hP : 0 ≤ R ^ (1 - alpha) := Real.rpow_nonneg hR.le _
      have hcoef : 0 ≤ alpha / (1 - alpha) := by positivity
      have hloweq : ENNReal.ofReal (2 * R) * ENNReal.ofReal (R ^ (-alpha)) =
          ENNReal.ofReal (2 * R ^ (1 - alpha)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * R)]
        congr 1
        rw [← hedberg_low_real_identity alpha R hR]
        ring
      have hhigheq : 2 * ENNReal.ofReal
          (alpha / (1 - alpha) * R ^ (1 - alpha)) =
          ENNReal.ofReal ((2 * alpha / (1 - alpha)) * R ^ (1 - alpha)) := by
        rw [← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [show ENNReal.ofReal (2 * R) * centeredMaximal F t *
          ENNReal.ofReal (R ^ (-alpha)) =
          (ENNReal.ofReal (2 * R) * ENNReal.ofReal (R ^ (-alpha))) *
            centeredMaximal F t by ac_rfl, hloweq, hhigheq]
      rw [← add_mul]
      congr 1
      rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hP)
        (mul_nonneg (by positivity) hP)]
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ 2 + 2 * alpha / (1 - alpha))]
      congr 1
      ring

private lemma hedberg_conjugate_facts (alpha pr qr : ℝ)
    (hpr : 1 < pr) (hqr : 0 < qr)
    (hrel : qr⁻¹ = pr⁻¹ - (1 - alpha)) :
    let pconj := pr / (pr - 1)
    Real.HolderConjugate pconj pr ∧
      -alpha * pconj < -1 ∧
      pconj⁻¹ - alpha = -qr⁻¹ := by
  dsimp
  have hprm0 : pr - 1 ≠ 0 := sub_ne_zero.mpr hpr.ne'
  have hholder : Real.HolderConjugate (pr / (pr - 1)) pr := by
    exact (Real.HolderConjugate.conjExponent hpr).symm
  have hinv : (pr / (pr - 1))⁻¹ = 1 - pr⁻¹ := by
    field_simp
  have hlast : (pr / (pr - 1))⁻¹ - alpha = -qr⁻¹ := by
    rw [hinv]
    linarith
  have hpconjpos : 0 < pr / (pr - 1) := div_pos (lt_trans (by norm_num) hpr) (sub_pos.mpr hpr)
  have halpha_conj : 1 < alpha * (pr / (pr - 1)) := by
    have hqinv : 0 < qr⁻¹ := inv_pos.mpr hqr
    have hbase : (pr / (pr - 1))⁻¹ < alpha := by linarith [hlast]
    have := mul_lt_mul_of_pos_right hbase hpconjpos
    rw [inv_mul_cancel₀ hpconjpos.ne'] at this
    exact this
  refine ⟨hholder, ?_, hlast⟩
  nlinarith

private lemma hedberg_far_kernel_normalize (alpha pconj qr R : ℝ)
    (hpconj : 0 < pconj) (hR : 0 < R)
    (hexterior : -alpha * pconj < -1)
    (hexp : pconj⁻¹ - alpha = -qr⁻¹) :
    (2 * ENNReal.ofReal (-R ^ ((-alpha * pconj) + 1) /
        ((-alpha * pconj) + 1))) ^ (1 / pconj) =
      ENNReal.ofReal ((2 / (alpha * pconj - 1)) ^ (1 / pconj)) *
        ENNReal.ofReal (R ^ (-qr⁻¹)) := by
  have hden : 0 < alpha * pconj - 1 := by nlinarith
  have hinside : -R ^ ((-alpha * pconj) + 1) /
      ((-alpha * pconj) + 1) =
      R ^ (1 - alpha * pconj) / (alpha * pconj - 1) := by
    rw [show (-alpha * pconj) + 1 = -(alpha * pconj - 1) by ring]
    rw [show -(alpha * pconj - 1) = 1 - alpha * pconj by ring]
    rw [show alpha * pconj - 1 = -(1 - alpha * pconj) by ring, div_neg]
    rw [neg_div]
  rw [hinside]
  have hbase : 0 ≤ 2 / (alpha * pconj - 1) := by positivity
  have hpow : 0 ≤ R ^ (1 - alpha * pconj) := Real.rpow_nonneg hR.le _
  have hprod : 2 * (R ^ (1 - alpha * pconj) / (alpha * pconj - 1)) =
      (2 / (alpha * pconj - 1)) * R ^ (1 - alpha * pconj) := by ring
  rw [← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hprod]
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hbase hpow)
    (by positivity : (0 : ℝ) ≤ 1 / pconj)]
  rw [Real.mul_rpow hbase hpow]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hbase _)]
  congr 1
  rw [← Real.rpow_mul hR.le]
  have hepow : (1 - alpha * pconj) * (1 / pconj) = -qr⁻¹ := by
    calc
      (1 - alpha * pconj) * (1 / pconj) = pconj⁻¹ - alpha := by
        field_simp
      _ = -qr⁻¹ := hexp
  rw [hepow]

private lemma hedberg_balance_near (alpha pr theta m n : ℝ)
    (hm : 0 < m) (hn : 0 < n)
    (hexp : pr * (1 - alpha) = 1 - theta) :
    (((n / m) ^ pr) ^ (1 - alpha)) * m =
      m ^ theta * n ^ (1 - theta) := by
  rw [← Real.rpow_mul (div_pos hn hm).le, hexp]
  rw [Real.div_rpow hn.le hm.le]
  have hmdecomp : m = m ^ (1 - theta) * m ^ theta := by
    rw [← Real.rpow_add hm]
    norm_num
  nth_rw 2 [hmdecomp]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hm (1 - theta))]

private lemma hedberg_balance_far (pr qr theta m n : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hqr : 0 < qr)
    (htheta : theta = pr / qr) :
    (((n / m) ^ pr) ^ (-qr⁻¹)) * n =
      m ^ theta * n ^ (1 - theta) := by
  rw [← Real.rpow_mul (div_pos hn hm).le]
  have hexp : pr * (-qr⁻¹) = -theta := by
    rw [htheta]
    field_simp
  rw [hexp, Real.div_rpow hn.le hm.le]
  rw [Real.rpow_neg hn.le, Real.rpow_neg hm.le]
  have hndecomp : n = n ^ theta * n ^ (1 - theta) := by
    rw [← Real.rpow_add hn]
    norm_num
  nth_rw 2 [hndecomp]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hn theta),
    ne_of_gt (Real.rpow_pos_of_pos hm theta)]

private lemma hedberg_balance_near_ennreal (alpha pr theta : ℝ)
    (M N : ℝ≥0∞) (hM0 : M ≠ 0) (hMtop : M ≠ ⊤)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hexp : pr * (1 - alpha) = 1 - theta) :
    let R := (N.toReal / M.toReal) ^ pr
    ENNReal.ofReal (R ^ (1 - alpha)) * M =
      M ^ theta * N ^ (1 - theta) := by
  dsimp
  have hm : 0 < M.toReal := ENNReal.toReal_pos hM0 hMtop
  have hn : 0 < N.toReal := ENNReal.toReal_pos hN0 hNtop
  rw [← ENNReal.ofReal_toReal hMtop, ← ENNReal.ofReal_toReal hNtop]
  simp only [ENNReal.toReal_ofReal hm.le, ENNReal.toReal_ofReal hn.le]
  rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg htheta0.le,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr htheta1.le)]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ (((N.toReal / M.toReal) ^ pr) ^ (1 - alpha)))]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg theta)]
  congr 1
  exact hedberg_balance_near alpha pr theta M.toReal N.toReal hm hn hexp

private lemma hedberg_balance_far_ennreal (pr qr theta : ℝ)
    (M N : ℝ≥0∞) (hM0 : M ≠ 0) (hMtop : M ≠ ⊤)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hqr : 0 < qr) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (htheta : theta = pr / qr) :
    let R := (N.toReal / M.toReal) ^ pr
    ENNReal.ofReal (R ^ (-qr⁻¹)) * N =
      M ^ theta * N ^ (1 - theta) := by
  dsimp
  have hm : 0 < M.toReal := ENNReal.toReal_pos hM0 hMtop
  have hn : 0 < N.toReal := ENNReal.toReal_pos hN0 hNtop
  rw [← ENNReal.ofReal_toReal hMtop, ← ENNReal.ofReal_toReal hNtop]
  simp only [ENNReal.toReal_ofReal hm.le, ENNReal.toReal_ofReal hn.le]
  rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg htheta0.le,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr htheta1.le)]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ (((N.toReal / M.toReal) ^ pr) ^ (-qr⁻¹)))]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg theta)]
  congr 1
  exact hedberg_balance_far pr qr theta M.toReal N.toReal hm hn hqr htheta

private lemma fractionalIntegral_le_near_add_far (alpha : ℝ) (F : ℝ → ℂ)
    (t R : ℝ) (hR : 0 < R) :
    fractionalIntegral alpha F t ≤
      (∫⁻ s in Set.Icc (t - R) (t + R),
        ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖F s‖ₑ ∂volume) +
      (∫⁻ s in {s : ℝ | R ≤ |t - s|},
        ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖F s‖ₑ ∂volume) := by
  let B : Set ℝ := Set.Icc (t - R) (t + R)
  let E : Set ℝ := {s : ℝ | R ≤ |t - s|}
  let f : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖F s‖ₑ
  have hcover : Set.univ ⊆ B ∪ E := by
    intro s hs
    rcases le_total |t - s| R with hle | hge
    · left
      change s ∈ Set.Icc (t - R) (t + R)
      constructor <;> linarith [neg_le_of_abs_le hle, le_of_abs_le hle]
    · exact Or.inr hge
  unfold fractionalIntegral
  simp only [enorm_eq_nnnorm]
  change (∫⁻ s, f s ∂volume) ≤ _
  calc
    (∫⁻ s, f s ∂volume) = ∫⁻ s in Set.univ, f s ∂volume := by
      rw [Measure.restrict_univ]
    _ ≤ ∫⁻ s in B ∪ E, f s ∂volume := lintegral_mono_set hcover
    _ ≤ (∫⁻ s in B, f s ∂volume) + ∫⁻ s in E, f s ∂volume :=
      lintegral_union_le f B E

private lemma fractionalIntegral_congr_ae (alpha : ℝ) {F G : ℝ → ℂ}
    (hFG : F =ᵐ[volume] G) :
    fractionalIntegral alpha F = fractionalIntegral alpha G := by
  funext t
  unfold fractionalIntegral
  apply lintegral_congr_ae
  filter_upwards [hFG] with s hs
  rw [hs]

private lemma centeredMaximal_zero_implies_eLpNorm_zero (p : ℝ≥0∞) (hp0 : p ≠ 0)
    (F : ℝ → ℂ) (hFm : StronglyMeasurable F) (t : ℝ)
    (hM : centeredMaximal F t = 0) :
    eLpNorm F p volume = 0 := by
  let S : ℕ → Set ℝ := fun n =>
    Set.Icc (t - (n + 1 : ℝ)) (t + (n + 1 : ℝ))
  have hSint : ∀ n : ℕ, (∫⁻ s in S n, ‖F s‖ₑ ∂volume) = 0 := by
    intro n
    have hr : 0 < (n + 1 : ℝ) := by positivity
    have hb := interval_lintegral_le_maximal F t (n + 1 : ℝ) hr
    rw [hM, mul_zero] at hb
    exact bot_unique hb
  have hcover : (⋃ n : ℕ, S n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt |t - s|
    apply Set.mem_iUnion.2
    refine ⟨n, ?_⟩
    change s ∈ Set.Icc (t - (n + 1 : ℝ)) (t + (n + 1 : ℝ))
    constructor <;> linarith [neg_lt_of_abs_lt hn, lt_of_abs_lt hn]
  have hglobal : (∫⁻ s : ℝ, ‖F s‖ₑ ∂volume) = 0 := by
    apply bot_unique
    calc
      (∫⁻ s : ℝ, ‖F s‖ₑ ∂volume) =
          ∫⁻ s in ⋃ n : ℕ, S n, ‖F s‖ₑ ∂volume := by
        rw [hcover, Measure.restrict_univ]
      _ ≤ ∑' n : ℕ, ∫⁻ s in S n, ‖F s‖ₑ ∂volume :=
        lintegral_iUnion_le S (fun s => ‖F s‖ₑ)
      _ = 0 := by simp [hSint]
  have hzero_ae : F =ᵐ[volume] 0 := by
    have hnormzero : (fun s : ℝ => ‖F s‖ₑ) =ᵐ[volume] 0 :=
      (lintegral_eq_zero_iff' hFm.enorm.aemeasurable).mp hglobal
    filter_upwards [hnormzero] with s hs
    simpa only [Pi.zero_apply, enorm_eq_zero] using hs
  exact eLpNorm_eq_zero_of_ae_zero hzero_ae

private lemma centeredMaximal_congr_ae_local {F G : ℝ → ℂ}
    (hFG : F =ᵐ[volume] G) :
    centeredMaximal F = centeredMaximal G := by
  funext t
  unfold centeredMaximal
  apply iSup_congr
  intro R
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hFG] with s hs
  rw [hs]

/-- `lem:hedberg`: pointwise interpolation between the maximal function and `L^p`. -/
theorem hedberg (alpha : ℝ) (h_alpha : 0 < alpha) (h_alpha_one : alpha < 1)
    (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq_top : q ≠ ⊤)
    (hexp : q⁻¹ = p⁻¹ - ENNReal.ofReal (1 - alpha)) :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ F : ℝ → ℂ, MemLp F p volume → ∀ t : ℝ,
    fractionalIntegral alpha F t ≤ C *
      (centeredMaximal F t) ^ (p.toReal / q.toReal) *
      (eLpNorm F p volume) ^ (1 - p.toReal / q.toReal) := by
  have hp_top : p ≠ ⊤ := ne_top_of_lt hpq
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  obtain ⟨hpr0, hqr0, hprqr, hreal, hbalance⟩ :=
    hedberg_real_exponents alpha h_alpha_one p q hp hpq hq_top hexp
  let pr : ℝ := p.toReal
  let qr : ℝ := q.toReal
  let theta : ℝ := pr / qr
  let pconj : ℝ := pr / (pr - 1)
  have hpr : 1 < pr := by
    dsimp [pr]
    simpa using ENNReal.toReal_strict_mono hp_top hp
  have htheta0 : 0 < theta := div_pos hpr0 hqr0
  have htheta1 : theta < 1 := by
    dsimp [theta, pr, qr]
    rw [div_lt_one hqr0]
    exact hprqr
  obtain ⟨hconj, hexterior, hfar_exp⟩ :=
    hedberg_conjugate_facts alpha pr qr hpr hqr0 hreal
  have hpconj0 : 0 < pconj := hconj.pos
  let Cnear : ℝ≥0∞ := ENNReal.ofReal (2 + 2 * alpha / (1 - alpha))
  let Cfar : ℝ≥0∞ :=
    ENNReal.ofReal ((2 / (alpha * pconj - 1)) ^ (1 / pconj))
  let C : ℝ≥0∞ := Cnear + Cfar
  have hCtop : C < ⊤ := by
    dsimp [C, Cnear, Cfar]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  refine ⟨C, hCtop, ?_⟩
  intro F hF t
  let Fm : ℝ → ℂ := hF.1.mk F
  have hFm : StronglyMeasurable Fm := hF.1.stronglyMeasurable_mk
  have hFeq : F =ᵐ[volume] Fm := hF.1.ae_eq_mk
  have hFmlp : MemLp Fm p volume := hF.ae_eq hFeq
  let N : ℝ≥0∞ := eLpNorm Fm p volume
  let M : ℝ≥0∞ := centeredMaximal Fm t
  have hNtop : N ≠ ⊤ := hFmlp.eLpNorm_lt_top.ne
  have hmain : fractionalIntegral alpha Fm t ≤
      C * M ^ theta * N ^ (1 - theta) := by
    by_cases hN0 : N = 0
    · have hzero : Fm =ᵐ[volume] 0 :=
        (eLpNorm_eq_zero_iff hFm.aestronglyMeasurable hp0).mp hN0
      have hfraczero : fractionalIntegral alpha Fm t = 0 := by
        have hfuneq := fractionalIntegral_congr_ae alpha hzero
        rw [congrFun hfuneq t]
        simp [fractionalIntegral]
      rw [hfraczero, hN0, ENNReal.zero_rpow_of_pos (sub_pos.mpr htheta1)]
      simp
    · by_cases hM0 : M = 0
      · have hNz := centeredMaximal_zero_implies_eLpNorm_zero p hp0 Fm hFm t hM0
        exact False.elim (hN0 (by simpa only [N] using hNz))
      · by_cases hMtop : M = ⊤
        · have hC0 : C ≠ 0 := by
            have hcnear : 0 < Cnear := by
              apply ENNReal.ofReal_pos.mpr
              have : 0 < 1 - alpha := sub_pos.mpr h_alpha_one
              positivity
            exact ne_of_gt (lt_of_lt_of_le hcnear (show Cnear ≤ C by simp [C]))
          have hNpow0 : N ^ (1 - theta) ≠ 0 := by
            intro hpowzero
            exact hN0 ((ENNReal.rpow_eq_zero_iff_of_pos
              (sub_pos.mpr htheta1)).mp hpowzero)
          rw [hMtop, ENNReal.top_rpow_of_pos htheta0]
          simp [hC0, hNpow0]
        · let R : ℝ := (N.toReal / M.toReal) ^ pr
          have hMreal : 0 < M.toReal := ENNReal.toReal_pos hM0 hMtop
          have hNreal : 0 < N.toReal := ENNReal.toReal_pos hN0 hNtop
          have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hNreal hMreal) _
          have hsplit := fractionalIntegral_le_near_add_far alpha Fm t R hR
          have hnear := hedberg_near_bound alpha h_alpha h_alpha_one Fm hFm t R hR
          have hfar := hedberg_far_bound alpha pconj p hp0 hp_top hconj hexterior
            Fm hFmlp t R hR
          have hnormalize := hedberg_far_kernel_normalize alpha pconj qr R hpconj0 hR
            hexterior hfar_exp
          have hnear_balance : ENNReal.ofReal (R ^ (1 - alpha)) * M =
              M ^ theta * N ^ (1 - theta) := by
            exact hedberg_balance_near_ennreal alpha pr theta M N hM0 hMtop hN0 hNtop
              htheta0 htheta1 hbalance
          have hfar_balance : ENNReal.ofReal (R ^ (-qr⁻¹)) * N =
              M ^ theta * N ^ (1 - theta) := by
            exact hedberg_balance_far_ennreal pr qr theta M N hM0 hMtop hN0 hNtop
              hqr0 htheta0 htheta1 rfl
          calc
            fractionalIntegral alpha Fm t ≤
                (∫⁻ s in Set.Icc (t - R) (t + R),
                  ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖Fm s‖ₑ ∂volume) +
                (∫⁻ s in {s : ℝ | R ≤ |t - s|},
                  ENNReal.ofReal (|t - s| ^ (-alpha)) * ‖Fm s‖ₑ ∂volume) := hsplit
            _ ≤ Cnear * ENNReal.ofReal (R ^ (1 - alpha)) * M +
                (2 * ENNReal.ofReal (-R ^ ((-alpha * pconj) + 1) /
                  ((-alpha * pconj) + 1))) ^ (1 / pconj) * N := by
              exact add_le_add hnear hfar
            _ = Cnear * (M ^ theta * N ^ (1 - theta)) +
                Cfar * (M ^ theta * N ^ (1 - theta)) := by
              rw [hnormalize]
              rw [show Cnear * ENNReal.ofReal (R ^ (1 - alpha)) * M =
                Cnear * (ENNReal.ofReal (R ^ (1 - alpha)) * M) by ac_rfl,
                hnear_balance]
              rw [show ENNReal.ofReal ((2 / (alpha * pconj - 1)) ^ (1 / pconj)) *
                  ENNReal.ofReal (R ^ (-qr⁻¹)) * N =
                Cfar * (ENNReal.ofReal (R ^ (-qr⁻¹)) * N) by
                  dsimp [Cfar]
                  ac_rfl,
                hfar_balance]
            _ = C * M ^ theta * N ^ (1 - theta) := by
              dsimp [C]
              ring
  have hfrac_eq := congrFun (fractionalIntegral_congr_ae alpha hFeq) t
  have hmax_eq := congrFun (centeredMaximal_congr_ae_local hFeq) t
  have hnorm_eq := eLpNorm_congr_ae (p := p) hFeq
  change fractionalIntegral alpha F t ≤
    C * (centeredMaximal F t) ^ theta * (eLpNorm F p volume) ^ (1 - theta)
  rw [hfrac_eq, hmax_eq, hnorm_eq]
  exact hmain

end CubicNLSPhaseRetrieval
