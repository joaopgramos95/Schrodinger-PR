import Lean_Code.Hedberg

/-!
# Interpolation and fractional integration

Blueprint chapter: `chap:frac-int` (module 3).
Imports: module 2 (`FreeSchrodinger`).
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- Closed vertical strip used by Hadamard's three-lines theorem. -/
def closedUnitStrip : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1}

/-- Boundary supremum on the vertical line `Re z = j`. -/
def stripBoundarySup (F : ℂ → ℂ) (j : ℝ) : ℝ≥0∞ :=
  ⨆ y : ℝ, ‖F ((j : ℂ) + Complex.I * (y : ℂ))‖₊

/-- `lem:three-lines-explicit`: Hadamard's estimate with explicit boundary suprema. -/
theorem three_lines_explicit (F : ℂ → ℂ)
    (hcont : ContinuousOn F closedUnitStrip)
    (hholo : DifferentiableOn ℂ F {z | 0 < z.re ∧ z.re < 1})
    (hbounded : ∃ C : ℝ, ∀ z ∈ closedUnitStrip, ‖F z‖ ≤ C)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
  ‖F θ‖₊ ≤
    (stripBoundarySup F 0) ^ (1 - θ) * (stripBoundarySup F 1) ^ θ := by
  open Complex.HadamardThreeLines in
    obtain ⟨C, hC⟩ := hbounded
    have hd : DiffContOnCl ℂ F (verticalStrip 0 1) := by
      constructor
      · change DifferentiableOn ℂ F {z | 0 < z.re ∧ z.re < 1}
        exact hholo
      · rw [verticalStrip, Complex.closure_preimage_re, closure_Ioo zero_ne_one]
        change ContinuousOn F {z | 0 ≤ z.re ∧ z.re ≤ 1}
        exact hcont
    have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hC z (by simpa [verticalClosedStrip, closedUnitStrip] using hz)
    have hsup0le : stripBoundarySup F 0 ≤ ENNReal.ofReal C := by
      rw [stripBoundarySup]
      refine iSup_le fun y => ?_
      simpa only [ofReal_norm, enorm_eq_nnnorm] using
        ENNReal.ofReal_le_ofReal (hC _ (by simp [closedUnitStrip]))
    have hsup1le : stripBoundarySup F 1 ≤ ENNReal.ofReal C := by
      rw [stripBoundarySup]
      refine iSup_le fun y => ?_
      simpa only [ofReal_norm, enorm_eq_nnnorm] using
        ENNReal.ofReal_le_ofReal (hC _ (by simp [closedUnitStrip]))
    have hsup0 : stripBoundarySup F 0 < ⊤ :=
      hsup0le.trans_lt ENNReal.ofReal_lt_top
    have hsup1 : stripBoundarySup F 1 < ⊤ :=
      hsup1le.trans_lt ENNReal.ofReal_lt_top
    have ha : ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ (stripBoundarySup F 0).toReal := by
      intro z hz
      have hzre : z.re = 0 := by simpa using hz
      have hzform : z = (0 : ℂ) + Complex.I * (z.im : ℂ) := by
        apply Complex.ext
        · simp [hzre]
        · simp
      have hn : (‖F z‖₊ : ℝ≥0∞) ≤ stripBoundarySup F 0 := by
        rw [hzform, stripBoundarySup]
        exact le_iSup (fun y : ℝ =>
          (‖F ((0 : ℂ) + Complex.I * (y : ℂ))‖₊ : ℝ≥0∞)) z.im
      simpa using ENNReal.toReal_mono hsup0.ne hn
    have hb : ∀ z ∈ Complex.re ⁻¹' {1}, ‖F z‖ ≤ (stripBoundarySup F 1).toReal := by
      intro z hz
      have hzre : z.re = 1 := by simpa using hz
      have hzform : z = (1 : ℂ) + Complex.I * (z.im : ℂ) := by
        apply Complex.ext
        · simp [hzre]
        · simp
      have hn : (‖F z‖₊ : ℝ≥0∞) ≤ stripBoundarySup F 1 := by
        rw [hzform, stripBoundarySup]
        exact le_iSup (fun y : ℝ =>
          (‖F ((1 : ℂ) + Complex.I * (y : ℂ))‖₊ : ℝ≥0∞)) z.im
      simpa using ENNReal.toReal_mono hsup1.ne hn
    have hzθ : (θ : ℂ) ∈ verticalClosedStrip 0 1 := by
      simp [verticalClosedStrip, hθ0, hθ1]
    have hreal : ‖F (θ : ℂ)‖ ≤
        (stripBoundarySup F 0).toReal ^ (1 - θ) *
          (stripBoundarySup F 1).toReal ^ θ := by
      simpa using norm_le_interp_of_mem_verticalClosedStrip₀₁' F hzθ hd hB ha hb
    have hcast := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr hθ1),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ0,
      ENNReal.ofReal_toReal hsup0.ne, ENNReal.ofReal_toReal hsup1.ne] at hcast
    simpa only [ofReal_norm, enorm_eq_nnnorm] using hcast

private def maximalAverage (F : ℝ → ℂ) (t r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * r)⁻¹) *
    ∫⁻ s in Set.Icc (t - r) (t + r), ‖F s‖ₑ ∂volume

private lemma maximalAverage_le_norm (F : ℝ → ℂ) (t r : ℝ) :
    maximalAverage F t r ≤
      ENNReal.ofReal ((2 * r)⁻¹) * eLpNorm F 1 volume := by
  apply mul_le_mul_left'
  calc
    (∫⁻ s in Set.Icc (t - r) (t + r), ‖F s‖ₑ ∂volume) ≤
        ∫⁻ s : ℝ, ‖F s‖ₑ ∂volume :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = eLpNorm F 1 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm]

private lemma exists_maximal_radius (F : ℝ → ℂ) (level t : ℝ)
    (ht : ENNReal.ofReal level < centeredMaximal F t) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal level < maximalAverage F t r := by
  rw [centeredMaximal] at ht
  by_contra h
  push_neg at h
  have hle : (⨆ R : {R : ℝ // 0 < R},
      ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
        ∫⁻ s in Set.Icc (t - R) (t + R), ‖F s‖₊ ∂volume) ≤
      ENNReal.ofReal level := by
    refine iSup_le fun R => ?_
    simpa [maximalAverage, enorm_eq_nnnorm] using h R R.property
  exact (not_le_of_gt ht) hle

private lemma selected_radius_bounded (F : ℝ → ℂ) (hF : MemLp F 1 volume)
    (level t r : ℝ) (hlevel : 0 < level) (hr : 0 < r)
    (havg : ENNReal.ofReal level < maximalAverage F t r) :
    r ≤ (eLpNorm F 1 volume).toReal / (2 * level) := by
  have hNtop : eLpNorm F 1 volume ≠ ⊤ := hF.eLpNorm_ne_top
  have hscalar_top : ENNReal.ofReal ((2 * r)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have havg_le := maximalAverage_le_norm F t r
  have havg_top : maximalAverage F t r ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hscalar_top hNtop) havg_le
  have hreal : level < ((2 * r)⁻¹) * (eLpNorm F 1 volume).toReal := by
    have hlt : ENNReal.ofReal level <
        ENNReal.ofReal ((2 * r)⁻¹) * eLpNorm F 1 volume := havg.trans_le havg_le
    have hprod_top : ENNReal.ofReal ((2 * r)⁻¹) * eLpNorm F 1 volume ≠ ⊤ :=
      ENNReal.mul_ne_top hscalar_top hNtop
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hprod_top).2 hlt
    have hinv_nonneg : 0 ≤ (2 * r)⁻¹ :=
      (inv_pos.mpr (mul_pos (by norm_num) hr)).le
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlevel.le,
      ENNReal.toReal_ofReal hinv_nonneg] at h
    exact h
  have hden : 0 < 2 * level := mul_pos (by norm_num) hlevel
  have hr2 : 0 < 2 * r := mul_pos (by norm_num) hr
  have hquot : level < (eLpNorm F 1 volume).toReal / (2 * r) := by
    simpa [div_eq_mul_inv, mul_comm] using hreal
  have hmul : level * (2 * r) < (eLpNorm F 1 volume).toReal :=
    (lt_div_iff₀ hr2).1 hquot
  apply le_of_lt
  apply (lt_div_iff₀ hden).2
  rw [show r * (2 * level) = level * (2 * r) by ring]
  exact hmul

/-- `lem:maximal-weak11`: centered weak `(1,1)`.  Mathlib's Vitali
enlargement theorem gives the harmless finite constant four. -/
theorem maximal_weak11 (F : ℝ → ℂ) (hF : MemLp F 1 volume)
    (level : ℝ) (hlevel : 0 < level) :
  volume {t | ENNReal.ofReal level < centeredMaximal F t} ≤
    4 * (ENNReal.ofReal level)⁻¹ * eLpNorm F 1 volume := by
  let E : Set ℝ := {t | ENNReal.ofReal level < centeredMaximal F t}
  choose r hrpos hravg using fun t : E =>
    exists_maximal_radius F level t.1 t.2
  let radius : ℝ → ℝ := fun t => if ht : t ∈ E then r ⟨t, ht⟩ else 1
  have hradius_pos : ∀ t ∈ E, 0 < radius t := by
    intro t ht
    simp only [radius, dif_pos ht]
    exact hrpos ⟨t, ht⟩
  have hradius_avg : ∀ t ∈ E,
      ENNReal.ofReal level < maximalAverage F t (radius t) := by
    intro t ht
    simp only [radius, dif_pos ht]
    exact hravg ⟨t, ht⟩
  have hradius_bdd : ∀ t ∈ E,
      radius t ≤ (eLpNorm F 1 volume).toReal / (2 * level) := by
    intro t ht
    exact selected_radius_bounded F hF level t (radius t) hlevel
      (hradius_pos t ht) (hradius_avg t ht)
  obtain ⟨u, huE, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall E
      (fun t : ℝ => t) radius ((eLpNorm F 1 volume).toReal / (2 * level))
      hradius_bdd 4 (by norm_num)
  have hu_countable : u.Countable := by
    apply hdisj.countable_of_nonempty_interior
    intro t ht
    rw [interior_closedBall _ (hradius_pos t (huE ht)).ne']
    exact ⟨t, mem_ball_self (hradius_pos t (huE ht))⟩
  have hEcover : E ⊆ ⋃ t ∈ u, closedBall t (4 * radius t) := by
    intro t ht
    obtain ⟨b, hb, hsub⟩ := hcover t ht
    exact mem_iUnion_of_mem b
      (mem_iUnion_of_mem hb (hsub (mem_closedBall_self (hradius_pos t ht).le)))
  change volume E ≤ _
  calc
    volume E ≤ volume (⋃ t ∈ u, closedBall t (4 * radius t)) := measure_mono hEcover
    _ ≤ ∑' t : u, volume (closedBall (t : ℝ) (4 * radius t)) :=
      measure_biUnion_le volume hu_countable _
    _ = ∑' t : u, 4 * volume (closedBall (t : ℝ) (radius t)) := by
      apply tsum_congr
      intro t
      simp only [Real.volume_closedBall]
      rw [show (2 : ℝ) * (4 * radius t) = 4 * (2 * radius t) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ ≤ ∑' t : u,
        4 * (ENNReal.ofReal level)⁻¹ *
          ∫⁻ s in closedBall (t : ℝ) (radius t), ‖F s‖ₑ ∂volume := by
      apply ENNReal.tsum_le_tsum
      intro t
      have htE : (t : ℝ) ∈ E := huE t.property
      have havg := hradius_avg t htE
      rw [maximalAverage] at havg
      have hlevel_ne : ENNReal.ofReal level ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr hlevel
      have hscale : ENNReal.ofReal ((2 * radius t)⁻¹) =
          (ENNReal.ofReal (2 * radius t))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (mul_pos (by norm_num) (hradius_pos t htE))]
      rw [hscale] at havg
      have hrad_ne : ENNReal.ofReal (2 * radius t) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr (mul_pos (by norm_num) (hradius_pos t htE))
      have hrad_top : ENNReal.ofReal (2 * radius t) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hmul : ENNReal.ofReal level * ENNReal.ofReal (2 * radius t) <
          ∫⁻ s in Set.Icc ((t : ℝ) - radius t) ((t : ℝ) + radius t), ‖F s‖ₑ ∂volume := by
        calc
          ENNReal.ofReal level * ENNReal.ofReal (2 * radius t) =
              (ENNReal.ofReal (2 * radius t)) * ENNReal.ofReal level := by ac_rfl
          _ < ENNReal.ofReal (2 * radius t) *
              ((ENNReal.ofReal (2 * radius t))⁻¹ *
                ∫⁻ s in Set.Icc ((t : ℝ) - radius t) ((t : ℝ) + radius t), ‖F s‖ₑ ∂volume) := by
                simpa [mul_comm] using
                  (ENNReal.mul_lt_mul_left hrad_ne hrad_top havg)
          _ = _ := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hrad_ne hrad_top]
            simp
      have hvol : volume (closedBall (t : ℝ) (radius t)) ≤
            (ENNReal.ofReal level)⁻¹ *
              ∫⁻ s in Set.Icc ((t : ℝ) - radius t) ((t : ℝ) + radius t), ‖F s‖ₑ ∂volume := by
          rw [Real.volume_closedBall]
          exact (ENNReal.mul_le_iff_le_inv hlevel_ne ENNReal.ofReal_ne_top).1 hmul.le
      calc
        4 * volume (closedBall (t : ℝ) (radius t)) ≤
            4 * ((ENNReal.ofReal level)⁻¹ *
              ∫⁻ s in Set.Icc ((t : ℝ) - radius t) ((t : ℝ) + radius t), ‖F s‖ₑ ∂volume) :=
          mul_le_mul_left' hvol 4
        _ = 4 * (ENNReal.ofReal level)⁻¹ *
              ∫⁻ s in closedBall (t : ℝ) (radius t), ‖F s‖ₑ ∂volume := by
          rw [Real.closedBall_eq_Icc]
          ac_rfl
    _ = 4 * (ENNReal.ofReal level)⁻¹ *
        ∑' t : u, ∫⁻ s in closedBall (t : ℝ) (radius t), ‖F s‖ₑ ∂volume := by
      rw [← ENNReal.tsum_mul_left]
    _ = 4 * (ENNReal.ofReal level)⁻¹ *
        ∫⁻ s in ⋃ t ∈ u, closedBall (t : ℝ) (radius t), ‖F s‖ₑ ∂volume := by
      congr 1
      rw [lintegral_biUnion hu_countable
        (fun t _ => measurableSet_closedBall) hdisj]
    _ ≤ 4 * (ENNReal.ofReal level)⁻¹ * ∫⁻ s : ℝ, ‖F s‖ₑ ∂volume := by
      gcongr
      exact Measure.restrict_le_self
    _ = 4 * (ENNReal.ofReal level)⁻¹ * eLpNorm F 1 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm]

private lemma locallyIntegrable_intervalIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ a b : ℝ, IntervalIntegrable f volume a b := by
  intro a b
  rcases le_total a b with hab | hba
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (hf.integrableOn_isCompact isCompact_Icc)
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hba).2
      (hf.integrableOn_isCompact isCompact_Icc)).symm

private lemma maximalAverage_eq_interval (F : ℝ → ℂ)
    (hloc : LocallyIntegrable (fun s => ‖F s‖) volume)
    (t R : ℝ) (hR : 0 < R) :
    maximalAverage F t R = ENNReal.ofReal ((2 * R)⁻¹) *
      ENNReal.ofReal (∫ s in (t - R)..(t + R), ‖F s‖ ∂volume) := by
  rw [maximalAverage]
  congr 1
  have hab : t - R ≤ t + R := by linarith
  have hint : Integrable (fun s => ‖F s‖)
      (volume.restrict (Set.Icc (t - R) (t + R))) :=
    hloc.integrableOn_isCompact isCompact_Icc
  calc
    (∫⁻ s in Set.Icc (t - R) (t + R), ‖F s‖ₑ ∂volume) =
        ENNReal.ofReal (∫ s in Set.Icc (t - R) (t + R), ‖F s‖ ∂volume) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun s => norm_nonneg (F s))]
      apply lintegral_congr
      intro s
      rw [ofReal_norm]
    _ = ENNReal.ofReal (∫ s in (t - R)..(t + R), ‖F s‖ ∂volume) := by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

private lemma continuous_maximalAverage (F : ℝ → ℂ)
    (hloc : LocallyIntegrable (fun s => ‖F s‖) volume)
    (R : ℝ) (hR : 0 < R) :
    Continuous (fun t => maximalAverage F t R) := by
  have hint := locallyIntegrable_intervalIntegrable hloc
  have hprim : Continuous (fun b => ∫ s in (0 : ℝ)..b, ‖F s‖ ∂volume) :=
    intervalIntegral.continuous_primitive hint 0
  have hreal : Continuous (fun t => ∫ s in (t - R)..(t + R), ‖F s‖ ∂volume) := by
    have hsub : Continuous (fun t =>
        (∫ s in (0 : ℝ)..(t + R), ‖F s‖ ∂volume) -
          ∫ s in (0 : ℝ)..(t - R), ‖F s‖ ∂volume) := by
      fun_prop
    convert hsub using 1
    funext t
    exact (intervalIntegral.integral_interval_sub_left (hint 0 (t + R))
      (hint 0 (t - R))).symm
  have hofReal : Continuous (fun t =>
      ENNReal.ofReal (∫ s in (t - R)..(t + R), ‖F s‖ ∂volume)) :=
    ENNReal.continuous_ofReal.comp hreal
  convert ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hofReal) using 1
  funext t
  exact maximalAverage_eq_interval F hloc t R hR

/-- The centered maximal function is measurable for locally integrable data. -/
theorem measurable_centeredMaximal (F : ℝ → ℂ)
    (hloc : LocallyIntegrable (fun s => ‖F s‖) volume) :
    Measurable (centeredMaximal F) := by
  apply LowerSemicontinuous.measurable
  unfold centeredMaximal
  exact lowerSemicontinuous_iSup fun R =>
    (continuous_maximalAverage F hloc R R.property).lowerSemicontinuous

private lemma centeredMaximal_congr_ae {F G : ℝ → ℂ} (hFG : F =ᵐ[volume] G) :
    centeredMaximal F = centeredMaximal G := by
  funext t
  unfold centeredMaximal
  apply iSup_congr
  intro R
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hFG] with s hs
  rw [hs]

private lemma highPart_memLp_one (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p ≠ ⊤)
    (F : ℝ → ℂ) (hF : MemLp F p volume) (hFm : StronglyMeasurable F)
    (level : ℝ) (hlevel : 0 < level) :
    MemLp ({x : ℝ | level / 2 < ‖F x‖}.indicator F) 1 volume := by
  let A : Set ℝ := {x : ℝ | level / 2 < ‖F x‖}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const hFm.norm.measurable
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hc0 : ENNReal.ofReal (level / 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (div_pos hlevel (by norm_num))
  have hAfin : volume A < ⊤ := by
    have hbig : A ⊆ {x : ℝ | ENNReal.ofReal (level / 2) ≤ ‖F x‖ₑ} := by
      intro x hx
      change ENNReal.ofReal (level / 2) ≤ ‖F x‖ₑ
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx.le
    exact (measure_mono hbig).trans_lt
      (hF.meas_ge_lt_top'_enorm hp0 hp_top hc0 (by simp))
  have hmeas : AEStronglyMeasurable (A.indicator F) volume :=
    hFm.aestronglyMeasurable.indicator hA
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hA]
  calc
    eLpNorm F 1 (volume.restrict A) ≤
        eLpNorm F p (volume.restrict A) *
          (volume.restrict A) Set.univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp.le hFm.aestronglyMeasurable.restrict
    _ < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact (hF.restrict A).eLpNorm_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg
        · have hpreal : 1 < p.toReal := by
            simpa using ENNReal.toReal_strict_mono hp_top hp
          norm_num
          exact inv_le_one_of_one_le₀ hpreal.le
        · simpa [Measure.restrict_apply hA] using hAfin.ne

private lemma maximal_le_highPart_add (F : ℝ → ℂ) (hFm : StronglyMeasurable F)
    (level : ℝ) (hlevel : 0 < level) (t : ℝ) :
    centeredMaximal F t ≤
      centeredMaximal ({x : ℝ | level / 2 < ‖F x‖}.indicator F) t +
        ENNReal.ofReal (level / 2) := by
  let A : Set ℝ := {x : ℝ | level / 2 < ‖F x‖}
  let B : ℝ → ℂ := A.indicator F
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const hFm.norm.measurable
  have hBm : StronglyMeasurable B := hFm.indicator hA
  have hpoint : ∀ x : ℝ, ‖F x‖ₑ ≤ ‖B x‖ₑ + ENNReal.ofReal (level / 2) := by
    intro x
    by_cases hx : x ∈ A
    · simp [B, Set.indicator_of_mem hx]
    · have hxle : ‖F x‖ ≤ level / 2 := le_of_not_gt hx
      simp only [B, Set.indicator_of_notMem hx, enorm_zero, zero_add]
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hxle
  unfold centeredMaximal
  refine iSup_le fun R => ?_
  let rad : ℝ≥0∞ := ENNReal.ofReal (2 * (R : ℝ))
  have hradpos : 0 < 2 * (R : ℝ) := mul_pos (by norm_num) R.property
  have hrad0 : rad ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hradpos
  have hradtop : rad ≠ ⊤ := ENNReal.ofReal_ne_top
  have hscale : ENNReal.ofReal ((2 * (R : ℝ))⁻¹) = rad⁻¹ :=
    ENNReal.ofReal_inv_of_pos hradpos
  have hint :
      (∫⁻ s in Set.Icc (t - R) (t + R), ‖F s‖ₑ ∂volume) ≤
        (∫⁻ s in Set.Icc (t - R) (t + R), ‖B s‖ₑ ∂volume) +
          ENNReal.ofReal (level / 2) * rad := by
    calc
      _ ≤ ∫⁻ s in Set.Icc (t - R) (t + R),
          (‖B s‖ₑ + ENNReal.ofReal (level / 2)) ∂volume :=
        lintegral_mono hpoint
      _ = (∫⁻ s in Set.Icc (t - R) (t + R), ‖B s‖ₑ ∂volume) +
          ∫⁻ _s in Set.Icc (t - R) (t + R), ENNReal.ofReal (level / 2) ∂volume := by
        rw [lintegral_add_left hBm.enorm]
      _ = _ := by
        rw [setLIntegral_const, Real.volume_Icc]
        congr 2
        simp only [rad]
        congr 1
        ring
  calc
    ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
        ∫⁻ s in Set.Icc (t - R) (t + R), ‖F s‖₊ ∂volume ≤
      ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
        ((∫⁻ s in Set.Icc (t - R) (t + R), ‖B s‖ₑ ∂volume) +
          ENNReal.ofReal (level / 2) * rad) := by
      gcongr
      simpa only [enorm_eq_nnnorm] using hint
    _ = ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
          (∫⁻ s in Set.Icc (t - R) (t + R), ‖B s‖₊ ∂volume) +
        ENNReal.ofReal (level / 2) := by
      simp only [enorm_eq_nnnorm]
      rw [mul_add, hscale]
      congr 1
      calc
        rad⁻¹ * (ENNReal.ofReal (level / 2) * rad) =
            (rad⁻¹ * rad) * ENNReal.ofReal (level / 2) := by ac_rfl
        _ = ENNReal.ofReal (level / 2) := by
          rw [ENNReal.inv_mul_cancel hrad0 hradtop, one_mul]
    _ ≤ (⨆ R : {R : ℝ // 0 < R},
          ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
            ∫⁻ s in Set.Icc (t - R) (t + R), ‖B s‖₊ ∂volume) +
        ENNReal.ofReal (level / 2) := by
      gcongr
      exact le_iSup (fun R : {R : ℝ // 0 < R} =>
        ENNReal.ofReal ((2 * (R : ℝ))⁻¹) *
          ∫⁻ s in Set.Icc (t - R) (t + R), ‖B s‖₊ ∂volume) R

private lemma maximal_distribution_bound (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p ≠ ⊤)
    (F : ℝ → ℂ) (hF : MemLp F p volume) (hFm : StronglyMeasurable F)
    (level : ℝ) (hlevel : 0 < level) :
    volume {t | ENNReal.ofReal level < centeredMaximal F t} ≤
      4 * (ENNReal.ofReal (level / 2))⁻¹ *
        ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖}, ‖F x‖ₑ ∂volume := by
  let A : Set ℝ := {x : ℝ | level / 2 < ‖F x‖}
  let B : ℝ → ℂ := A.indicator F
  have hB1 : MemLp B 1 volume :=
    highPart_memLp_one p hp hp_top F hF hFm level hlevel
  have hcadd : ENNReal.ofReal level =
      ENNReal.ofReal (level / 2) + ENNReal.ofReal (level / 2) := by
    rw [← ENNReal.ofReal_add (div_nonneg hlevel.le (by norm_num))
      (div_nonneg hlevel.le (by norm_num))]
    congr 1
    ring
  have hsub : {t | ENNReal.ofReal level < centeredMaximal F t} ⊆
      {t | ENNReal.ofReal (level / 2) < centeredMaximal B t} := by
    intro t ht
    have hle := maximal_le_highPart_add F hFm level hlevel t
    change centeredMaximal F t ≤ centeredMaximal B t + ENNReal.ofReal (level / 2) at hle
    rw [hcadd] at ht
    exact (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).1 (ht.trans_le hle)
  calc
    volume {t | ENNReal.ofReal level < centeredMaximal F t} ≤
        volume {t | ENNReal.ofReal (level / 2) < centeredMaximal B t} := measure_mono hsub
    _ ≤ 4 * (ENNReal.ofReal (level / 2))⁻¹ * eLpNorm B 1 volume :=
      maximal_weak11 B hB1 (level / 2) (div_pos hlevel (by norm_num))
    _ = 4 * (ENNReal.ofReal (level / 2))⁻¹ *
        ∫⁻ x in A, ‖F x‖ₑ ∂volume := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      congr 1
      rw [show (fun x => ‖B x‖ₑ) = A.indicator (fun x => ‖F x‖ₑ) by
        funext x
        by_cases hx : x ∈ A <;> simp [B, hx]]
      rw [lintegral_indicator (measurableSet_lt measurable_const hFm.norm.measurable)]

private lemma lintegral_rpow_Ioo (a exponent : ℝ) (ha : 0 ≤ a)
    (hexponent : -1 < exponent) :
    ∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal (t ^ exponent) ∂volume =
      ENNReal.ofReal (a ^ (exponent + 1) / (exponent + 1)) := by
  rw [restrict_Ioo_eq_restrict_Ioc]
  have hint : IntervalIntegrable (fun t : ℝ => t ^ exponent) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' hexponent
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 a)]
      (fun t : ℝ => t ^ exponent) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc : MeasurableSet (Set.Ioc 0 a))]
      with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1 hnonneg]
  rw [← intervalIntegral.integral_of_le ha]
  rw [integral_rpow (Or.inl hexponent)]
  simp only [Real.zero_rpow (by linarith : exponent + 1 ≠ 0), sub_zero]

private lemma weighted_distribution_bound (p : ℝ≥0∞) (hp : 1 < p)
    (hp_top : p ≠ ⊤) (F : ℝ → ℂ) (hF : MemLp F p volume)
    (hFm : StronglyMeasurable F) (level : ℝ) (hlevel : 0 < level) :
    volume {t | ENNReal.ofReal level < centeredMaximal F t} *
        ENNReal.ofReal (level ^ (p.toReal - 1)) ≤
      8 * ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
        ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume := by
  have hdist := maximal_distribution_bound p hp hp_top F hF hFm level hlevel
  have hscalar :
      4 * (ENNReal.ofReal (level / 2))⁻¹ *
          ENNReal.ofReal (level ^ (p.toReal - 1)) =
        8 * ENNReal.ofReal (level ^ (p.toReal - 2)) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp)
          (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr
            (div_pos hlevel (by norm_num)))))
        ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)).1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal (div_nonneg hlevel.le (by norm_num)),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hlevel.le _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hlevel.le _)]
    norm_num
    rw [show p.toReal - 1 = (p.toReal - 2) + 1 by ring,
      Real.rpow_add hlevel, Real.rpow_one]
    field_simp
    ring
  calc
    volume {t | ENNReal.ofReal level < centeredMaximal F t} *
        ENNReal.ofReal (level ^ (p.toReal - 1)) ≤
      (4 * (ENNReal.ofReal (level / 2))⁻¹ *
        ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖}, ‖F x‖ₑ ∂volume) *
          ENNReal.ofReal (level ^ (p.toReal - 1)) := by
      gcongr
    _ = 8 * ENNReal.ofReal (level ^ (p.toReal - 2)) *
        ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖}, ‖F x‖ₑ ∂volume := by
      rw [← hscalar]
      ac_rfl
    _ = 8 * ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
        ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume := by
      rw [lintegral_mul_const _ hFm.enorm]
      ac_rfl

private lemma weighted_highPart_lintegral (p : ℝ≥0∞) (hp : 1 < p)
    (hp_top : p ≠ ⊤) (F : ℝ → ℂ) (hFm : StronglyMeasurable F) :
    (∫⁻ level in Set.Ioi (0 : ℝ),
      ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
        ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume ∂volume) =
      ∫⁻ x : ℝ, ‖F x‖ₑ *
        ENNReal.ofReal ((2 * ‖F x‖) ^ (p.toReal - 1) / (p.toReal - 1)) ∂volume := by
  let S : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ z.1 < 2 * ‖F z.2‖}
  let H : ℝ × ℝ → ℝ≥0∞ := fun z =>
    ‖F z.2‖ₑ * ENNReal.ofReal (z.1 ^ (p.toReal - 2))
  have hS : MeasurableSet S := by
    apply (measurableSet_lt measurable_const measurable_fst).inter
    exact measurableSet_lt measurable_fst
      (measurable_const.mul (hFm.norm.measurable.comp measurable_snd))
  have hrpow_meas : Measurable (fun level : ℝ => level ^ (p.toReal - 2)) := by
    apply (continuousOn_id.rpow_const (s := ({0} : Set ℝ)ᶜ) ?_).measurable_of_countable_compl
    · simpa using Set.countable_singleton (0 : ℝ)
    · intro level hlevel
      exact Or.inl (by simpa using hlevel)
  have hH : Measurable H :=
    (hFm.enorm.comp measurable_snd).mul
      (ENNReal.continuous_ofReal.measurable.comp
        (hrpow_meas.comp measurable_fst))
  have hSH : Measurable (S.indicator H) := hH.indicator hS
  have hleft :
      (∫⁻ level in Set.Ioi (0 : ℝ),
        ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
          ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume ∂volume) =
        ∫⁻ level : ℝ, ∫⁻ x : ℝ, S.indicator H (level, x) ∂volume ∂volume := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro level
    by_cases hlevel : 0 < level
    · rw [Set.indicator_of_mem (show level ∈ Set.Ioi (0 : ℝ) from hlevel)]
      rw [← lintegral_indicator
        (measurableSet_lt measurable_const hFm.norm.measurable)]
      apply lintegral_congr
      intro x
      have heq : level / 2 < ‖F x‖ ↔ level < 2 * ‖F x‖ := by
        constructor
        · intro hx
          simpa [mul_comm] using (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).1 hx
        · intro hx
          apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          simpa [mul_comm] using hx
      by_cases hx : level / 2 < ‖F x‖
      · have hs : (level, x) ∈ S := ⟨hlevel, heq.mp hx⟩
        rw [Set.indicator_of_mem
          (show x ∈ {a : ℝ | level / 2 < ‖F a‖} from hx), Set.indicator_of_mem hs]
      · have hs : (level, x) ∉ S := by
          intro hs
          exact hx (heq.mpr hs.2)
        rw [Set.indicator_of_notMem
          (show x ∉ {a : ℝ | level / 2 < ‖F a‖} from hx), Set.indicator_of_notMem hs]
    · have hnmem : level ∉ Set.Ioi (0 : ℝ) := hlevel
      simp only [Set.indicator_of_notMem hnmem]
      simp [S, hlevel]
  rw [hleft, lintegral_lintegral_swap
    (f := fun level x => S.indicator H (level, x)) hSH.aemeasurable]
  apply lintegral_congr
  intro x
  have hxnonneg : 0 ≤ 2 * ‖F x‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  calc
    (∫⁻ level : ℝ, S.indicator H (level, x) ∂volume) =
        ∫⁻ level in Set.Ioo 0 (2 * ‖F x‖),
          ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro level
      by_cases hmem : level ∈ Set.Ioo 0 (2 * ‖F x‖)
      · have hs : (level, x) ∈ S := by simpa [S] using hmem
        rw [Set.indicator_of_mem hs, Set.indicator_of_mem hmem]
      · have hs : (level, x) ∉ S := by simpa [S] using hmem
        rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hmem]
    _ = ‖F x‖ₑ * ∫⁻ level in Set.Ioo 0 (2 * ‖F x‖),
          ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume := by
      have hw : Measurable (fun level : ℝ =>
          ENNReal.ofReal (level ^ (p.toReal - 2))) :=
        ENNReal.continuous_ofReal.measurable.comp hrpow_meas
      exact lintegral_const_mul ‖F x‖ₑ hw
    _ = _ := by
      rw [lintegral_rpow_Ioo (2 * ‖F x‖) (p.toReal - 2) hxnonneg]
      · ring_nf
      · have hpreal : 1 < p.toReal := by
          simpa using ENNReal.toReal_strict_mono hp_top hp
        linarith

private lemma weighted_highPart_lintegral_eq (p : ℝ≥0∞) (hp : 1 < p)
    (hp_top : p ≠ ⊤) (F : ℝ → ℂ) (hFm : StronglyMeasurable F) :
    (∫⁻ level in Set.Ioi (0 : ℝ),
      ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
        ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume ∂volume) =
      ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1)) *
        ∫⁻ x : ℝ, ‖F x‖ₑ ^ p.toReal ∂volume := by
  rw [weighted_highPart_lintegral p hp hp_top F hFm]
  have hpreal : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp_top hp
  have hconst_nonneg : 0 ≤ 2 ^ (p.toReal - 1) / (p.toReal - 1) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hpreal.le)
  have hpoint : ∀ x : ℝ,
      ‖F x‖ₑ * ENNReal.ofReal
          ((2 * ‖F x‖) ^ (p.toReal - 1) / (p.toReal - 1)) =
        ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1)) *
          ‖F x‖ₑ ^ p.toReal := by
    intro x
    rw [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (norm_nonneg (F x))]
    rw [ENNReal.ofReal_rpow_of_nonneg (p := p.toReal)
        (norm_nonneg (F x)) (le_trans (by norm_num) hpreal.le),
      ← ENNReal.ofReal_mul hconst_nonneg]
    congr 1
    by_cases hx : ‖F x‖ = 0
    · simp [hx, Real.zero_rpow (sub_pos.mpr hpreal).ne',
        Real.zero_rpow (lt_trans (by norm_num) hpreal).ne']
    · have hxpos : 0 < ‖F x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxpos.le]
      rw [show p.toReal = 1 + (p.toReal - 1) by ring,
        Real.rpow_add hxpos, Real.rpow_one]
      field_simp
      ring
  simp_rw [hpoint]
  have hg : Measurable (fun x : ℝ => ‖F x‖ₑ ^ p.toReal) :=
    ENNReal.continuous_rpow_const.measurable.comp hFm.enorm
  exact lintegral_const_mul _ hg

private lemma truncated_maximal_power_bound (p : ℝ≥0∞) (hp : 1 < p)
    (hp_top : p ≠ ⊤) (F : ℝ → ℂ) (hF : MemLp F p volume)
    (hFm : StronglyMeasurable F) (cap : ℝ) (_hcap : 0 < cap) :
    (∫⁻ t : ℝ, (min (centeredMaximal F t) (ENNReal.ofReal cap)) ^ p.toReal ∂volume) ≤
      (ENNReal.ofReal p.toReal * 8 *
        ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1))) *
          ∫⁻ x : ℝ, ‖F x‖ₑ ^ p.toReal ∂volume := by
  let G : ℝ → ℝ := fun t =>
    (min (centeredMaximal F t) (ENNReal.ofReal cap)).toReal
  have hloc : LocallyIntegrable (fun s => ‖F s‖) volume :=
    locallyIntegrableOn_univ.mp
      ((hF.locallyIntegrable hp.le).locallyIntegrableOn Set.univ).norm
  have hM : Measurable (centeredMaximal F) := measurable_centeredMaximal F hloc
  have hmin : Measurable (fun t => min (centeredMaximal F t) (ENNReal.ofReal cap)) :=
    hM.min measurable_const
  have hG : Measurable G := hmin.ennreal_toReal
  have hGnonneg : ∀ t, 0 ≤ G t := fun _t => ENNReal.toReal_nonneg
  have hpreal : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp_top hp
  have hp_real_pos : 0 < p.toReal := lt_trans (by norm_num) hpreal
  have hcapmin : ∀ t : ℝ,
      min (centeredMaximal F t) (ENNReal.ofReal cap) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  have hleft :
      (∫⁻ t : ℝ, (min (centeredMaximal F t) (ENNReal.ofReal cap)) ^ p.toReal ∂volume) =
        ∫⁻ t : ℝ, ENNReal.ofReal (G t ^ p.toReal) ∂volume := by
    apply lintegral_congr
    intro t
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp_real_pos.le,
      ENNReal.ofReal_toReal (hcapmin t)]
  have hlayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (Filter.Eventually.of_forall hGnonneg) hG.aemeasurable hp_real_pos
  rw [hleft, hlayer]
  calc
    ENNReal.ofReal p.toReal *
        ∫⁻ level in Set.Ioi (0 : ℝ),
          volume {t : ℝ | level < G t} *
            ENNReal.ofReal (level ^ (p.toReal - 1)) ∂volume ≤
      ENNReal.ofReal p.toReal *
        ∫⁻ level in Set.Ioi (0 : ℝ),
          8 * ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
            ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume ∂volume := by
      apply mul_le_mul_left'
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with level hlevel
      have hlevelpos : 0 < level := hlevel
      have hsub : {t : ℝ | level < G t} ⊆
          {t : ℝ | ENNReal.ofReal level < centeredMaximal F t} := by
        intro t ht
        have hlt : ENNReal.ofReal level < ENNReal.ofReal (G t) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlevelpos.le).2 ht
        rw [ENNReal.ofReal_toReal (hcapmin t)] at hlt
        exact hlt.trans_le (min_le_left _ _)
      calc
        volume {t : ℝ | level < G t} *
            ENNReal.ofReal (level ^ (p.toReal - 1)) ≤
          volume {t : ℝ | ENNReal.ofReal level < centeredMaximal F t} *
            ENNReal.ofReal (level ^ (p.toReal - 1)) := by
          gcongr
        _ ≤ _ := weighted_distribution_bound p hp hp_top F hF hFm level hlevelpos
    _ = ENNReal.ofReal p.toReal * 8 *
        (∫⁻ level in Set.Ioi (0 : ℝ),
          ∫⁻ x in {x : ℝ | level / 2 < ‖F x‖},
            ‖F x‖ₑ * ENNReal.ofReal (level ^ (p.toReal - 2)) ∂volume ∂volume) := by
      rw [lintegral_const_mul' 8 _ (by norm_num)]
      ac_rfl
    _ = _ := by
      rw [weighted_highPart_lintegral_eq p hp hp_top F hFm]
      ac_rfl

private lemma maximal_power_bound (p : ℝ≥0∞) (hp : 1 < p)
    (hp_top : p ≠ ⊤) (F : ℝ → ℂ) (hF : MemLp F p volume)
    (hFm : StronglyMeasurable F) :
    (∫⁻ t : ℝ, centeredMaximal F t ^ p.toReal ∂volume) ≤
      (ENNReal.ofReal p.toReal * 8 *
        ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1))) *
          ∫⁻ x : ℝ, ‖F x‖ₑ ^ p.toReal ∂volume := by
  let trunc : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    (min (centeredMaximal F t) (ENNReal.ofReal ((n + 1 : ℕ) : ℝ))) ^ p.toReal
  have hloc : LocallyIntegrable (fun s => ‖F s‖) volume :=
    locallyIntegrableOn_univ.mp
      ((hF.locallyIntegrable hp.le).locallyIntegrableOn Set.univ).norm
  have hM : Measurable (centeredMaximal F) := measurable_centeredMaximal F hloc
  have htrunc_meas : ∀ n, Measurable (trunc n) := fun n =>
    ENNReal.continuous_rpow_const.measurable.comp (hM.min measurable_const)
  have hpreal : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp_top hp
  have hcap_tendsto : Tendsto
      (fun n : ℕ => ENNReal.ofReal ((n + 1 : ℕ) : ℝ)) atTop (𝓝 ⊤) := by
    convert ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    rw [Nat.cast_add, Nat.cast_one,
      ENNReal.ofReal_add (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have htrunc_mono : ∀ t : ℝ, Monotone fun n => trunc n t := by
    intro t n m hnm
    apply ENNReal.rpow_le_rpow
    · apply min_le_min_left
      apply ENNReal.ofReal_le_ofReal
      norm_num
      omega
    · exact (le_trans (by norm_num) hpreal.le)
  have htrunc_tendsto : ∀ t : ℝ, Tendsto (fun n => trunc n t) atTop
      (𝓝 (centeredMaximal F t ^ p.toReal)) := by
    intro t
    apply ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
    simpa using (tendsto_const_nhds.min hcap_tendsto)
  have hint_tendsto := lintegral_tendsto_of_tendsto_of_monotone
    (μ := volume) (fun n => (htrunc_meas n).aemeasurable)
    (Filter.Eventually.of_forall htrunc_mono)
    (Filter.Eventually.of_forall htrunc_tendsto)
  apply le_of_tendsto hint_tendsto
  exact Filter.Eventually.of_forall fun n => by
    simpa only [trunc] using truncated_maximal_power_bound p hp hp_top F hF hFm
      (((n + 1 : ℕ) : ℝ)) (by positivity)

private lemma maximal_eLpNorm_bound_stronglyMeasurable (p : ℝ≥0∞) (hp : 1 < p)
    (hp_top : p ≠ ⊤) (F : ℝ → ℂ) (hF : MemLp F p volume)
    (hFm : StronglyMeasurable F) :
    eLpNorm (centeredMaximal F) p volume ≤
      ((ENNReal.ofReal p.toReal * 8 *
        ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1))) ^
          (1 / p.toReal)) * eLpNorm F p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hpreal : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp_top hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
  simp only [enorm_eq_self]
  calc
    (∫⁻ a : ℝ, centeredMaximal F a ^ p.toReal ∂volume) ^ (1 / p.toReal) ≤
      (((ENNReal.ofReal p.toReal * 8 *
          ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1))) *
            ∫⁻ x : ℝ, ‖F x‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal)) := by
        apply ENNReal.rpow_le_rpow
        · exact maximal_power_bound p hp hp_top F hF hFm
        · exact div_nonneg (by norm_num) (le_trans (by norm_num) hpreal.le)
    _ = ((ENNReal.ofReal p.toReal * 8 *
          ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1))) ^
            (1 / p.toReal)) *
          (∫⁻ x : ℝ, ‖F x‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) := by
      rw [ENNReal.mul_rpow_of_nonneg]
      exact div_nonneg (by norm_num) (le_trans (by norm_num) hpreal.le)

/-- `lem:maximal-strongp`: strong `(p,p)` boundedness. -/
theorem maximal_strongp (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p ≠ ⊤) :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ F : ℝ → ℂ, MemLp F p volume →
    eLpNorm (centeredMaximal F) p volume ≤ C * eLpNorm F p volume := by
  let K : ℝ≥0∞ := ENNReal.ofReal p.toReal * 8 *
    ENNReal.ofReal (2 ^ (p.toReal - 1) / (p.toReal - 1))
  let C : ℝ≥0∞ := K ^ (1 / p.toReal)
  have hpreal : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp_top hp
  have hKtop : K ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
    · exact ENNReal.ofReal_ne_top
  have hCtop : C < ⊤ := by
    apply ENNReal.rpow_lt_top_of_nonneg
    · exact div_nonneg (by norm_num) (le_trans (by norm_num) hpreal.le)
    · exact hKtop
  refine ⟨C, hCtop, ?_⟩
  intro F hF
  let Fm : ℝ → ℂ := hF.1.mk F
  have hFm : StronglyMeasurable Fm := hF.1.stronglyMeasurable_mk
  have hFeq : F =ᵐ[volume] Fm := hF.1.ae_eq_mk
  have hFmlp : MemLp Fm p volume := hF.ae_eq hFeq
  have hbound := maximal_eLpNorm_bound_stronglyMeasurable p hp hp_top Fm hFmlp hFm
  change eLpNorm (centeredMaximal F) p volume ≤
    (K ^ (1 / p.toReal)) * eLpNorm F p volume
  rw [centeredMaximal_congr_ae hFeq, eLpNorm_congr_ae hFeq]
  simpa only [K] using hbound

private lemma eLpNorm_ennreal_const_mul
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (g : ι → ℝ≥0∞)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrtop : r ≠ ⊤) :
    eLpNorm (fun x => c * g x) r μ = c * eLpNorm g r μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop]
  simp only [enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
  rw [lintegral_const_mul' _ _
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hc).ne,
    ENNReal.mul_rpow_of_nonneg]
  · rw [← ENNReal.rpow_mul]
    field_simp [ENNReal.toReal_ne_zero.mpr ⟨hr0, hrtop⟩]
    simp only [ENNReal.rpow_one]
  · positivity

/-- `lem:HLS-time`: one-dimensional Hardy–Littlewood–Sobolev estimate. -/
theorem HLS_time (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq_top : q ≠ ⊤)
    (hexp : q⁻¹ = p⁻¹ - ENNReal.ofReal (1 - α)) :
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ F : ℝ → ℂ, MemLp F p volume →
    eLpNorm (fractionalIntegral α F) q volume ≤ C * eLpNorm F p volume := by
  have hp_top : p ≠ ⊤ := ne_top_of_lt hpq
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ≥0∞) < 1) hp)
  have hq0 : q ≠ 0 := ne_of_gt
    (lt_trans (by norm_num : (0 : ℝ≥0∞) < 1) (lt_trans hp hpq))
  have hp_real : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hq_real : 0 < q.toReal := ENNReal.toReal_pos hq0 hq_top
  let θ : ℝ := p.toReal / q.toReal
  have hθ0 : 0 < θ := div_pos hp_real hq_real
  have hθ1 : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one hq_real]
    exact ENNReal.toReal_strict_mono hq_top hpq
  obtain ⟨Ch, hCh, hhedberg⟩ := hedberg α hα0 hα1 p q hp hpq hq_top hexp
  obtain ⟨Cm, hCm, hmax⟩ := maximal_strongp p hp hp_top
  refine ⟨Ch * Cm ^ θ, ENNReal.mul_lt_top hCh
    (ENNReal.rpow_lt_top_of_nonneg hθ0.le hCm.ne), ?_⟩
  intro F hF
  let N : ℝ≥0∞ := eLpNorm F p volume
  have hNtop : N ≠ ⊤ := hF.eLpNorm_ne_top
  have hpoint : ∀ t : ℝ,
      fractionalIntegral α F t ≤
        Ch * (centeredMaximal F t) ^ θ * N ^ (1 - θ) := by
    intro t
    simpa [θ, N] using hhedberg F hF t
  have hnorm :
      eLpNorm (fractionalIntegral α F) q volume ≤
        eLpNorm (fun t => Ch * (centeredMaximal F t) ^ θ * N ^ (1 - θ)) q volume := by
    apply eLpNorm_mono_enorm
    intro t
    simpa only [enorm_eq_self] using hpoint t
  have hscale :
      eLpNorm (fun t => Ch * (centeredMaximal F t) ^ θ * N ^ (1 - θ)) q volume =
        Ch * N ^ (1 - θ) *
          eLpNorm (fun t => (centeredMaximal F t) ^ θ) q volume := by
    rw [show (fun t => Ch * (centeredMaximal F t) ^ θ * N ^ (1 - θ)) =
        fun t => (Ch * N ^ (1 - θ)) * ((centeredMaximal F t) ^ θ) by
      funext t
      ring]
    exact eLpNorm_ennreal_const_mul volume _
      (ENNReal.mul_ne_top hCh.ne
        (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ1.le) hNtop).ne)
      _ q hq0 hq_top
  have hpower :
      eLpNorm (fun t => (centeredMaximal F t) ^ θ) q volume =
        eLpNorm (centeredMaximal F) p volume ^ θ := by
    change eLpNorm (fun t => ‖centeredMaximal F t‖ₑ ^ θ) q volume = _
    rw [eLpNorm_enorm_rpow (centeredMaximal F) hθ0]
    have hqp : q * ENNReal.ofReal θ = p := by
      have hre : (q * ENNReal.ofReal θ).toReal = p.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0.le]
        dsimp [θ]
        field_simp
      rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hre with heq | hbad | hbad
      · exact heq
      · exact (hp_top hbad.2).elim
      · exact ((ENNReal.mul_ne_top hq_top ENNReal.ofReal_ne_top) hbad.1).elim
    rw [hqp]
  calc
    eLpNorm (fractionalIntegral α F) q volume ≤
        Ch * N ^ (1 - θ) * eLpNorm (centeredMaximal F) p volume ^ θ := by
      calc
        _ ≤ eLpNorm (fun t => Ch * (centeredMaximal F t) ^ θ * N ^ (1 - θ))
            q volume := hnorm
        _ = _ := by rw [hscale, hpower]
    _ ≤ Ch * N ^ (1 - θ) * (Cm * N) ^ θ := by
      gcongr
      exact hmax F hF
    _ = (Ch * Cm ^ θ) * N := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0.le]
      by_cases hN0 : N = 0
      · simp [hN0, sub_pos.mpr hθ1]
      calc
        Ch * N ^ (1 - θ) * (Cm ^ θ * N ^ θ) =
            Ch * Cm ^ θ * (N ^ (1 - θ) * N ^ θ) := by ac_rfl
        _ = Ch * Cm ^ θ * N ^ ((1 - θ) + θ) := by
          rw [ENNReal.rpow_add (1 - θ) θ hN0 hNtop]
        _ = _ := by norm_num

end CubicNLSPhaseRetrieval
