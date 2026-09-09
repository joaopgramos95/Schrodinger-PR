import Lean_Code.Carleman2D
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open Filter MeasureTheory
open scoped Convolution ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

private def weakODEPrimitive (lam : ℂ) (phi : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(Complex.exp (-lam * (t : ℂ)) *
    ∫ s in (0 : ℝ)..t, Complex.exp (lam * (s : ℂ)) * phi s)

private lemma weakODEPrimitive_hasDerivAt (lam : ℂ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) (t : ℝ) :
    HasDerivAt (weakODEPrimitive lam phi)
      (-lam * weakODEPrimitive lam phi t - phi t) t := by
  let A : ℝ → ℂ := fun r =>
    ∫ s in (0 : ℝ)..r, Complex.exp (lam * (s : ℂ)) * phi s
  have hA : HasDerivAt A (Complex.exp (lam * (t : ℂ)) * phi t) t := by
    exact intervalIntegral.integral_hasDerivAt_right
      ((by fun_prop : Continuous (fun s : ℝ =>
        Complex.exp (lam * (s : ℂ)) * phi s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (fun s : ℝ =>
        Complex.exp (lam * (s : ℂ)) * phi s)).stronglyMeasurableAtFilter
          (μ := volume) (l := 𝓝 t))
      (by simpa using (by fun_prop : ContinuousAt (fun s : ℝ =>
        Complex.exp (lam * (s : ℂ)) * phi s) t))
  have hlin : HasDerivAt (fun r : ℝ => -lam * (r : ℂ)) (-lam) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using!
      (hasDerivAt_id t).ofReal_comp.const_mul (-lam)
  have hexp := hlin.cexp
  have hmul := hexp.mul hA
  change HasDerivAt
    (fun r : ℝ => -(Complex.exp (-lam * (r : ℂ)) * A r))
    (-lam * -(Complex.exp (-lam * (t : ℂ)) * A t) - phi t) t
  apply hmul.neg.congr_deriv
  dsimp [A]
  have hcancel : Complex.exp (-lam * (t : ℂ)) *
      (Complex.exp (lam * (t : ℂ)) * phi t) = phi t := by
    rw [← mul_assoc, ← Complex.exp_add]
    rw [show -lam * (t : ℂ) + lam * (t : ℂ) = 0 by ring, Complex.exp_zero,
      one_mul]
  rw [hcancel]
  ring

private lemma weakODEPrimitive_deriv (lam : ℂ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) :
    deriv (weakODEPrimitive lam phi) =
      fun t => -lam * weakODEPrimitive lam phi t - phi t := by
  funext t
  exact (weakODEPrimitive_hasDerivAt lam phi hphi t).deriv

private lemma weakODEPrimitive_contDiff (lam : ℂ) (phi : ℝ → ℂ)
    (hphi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weakODEPrimitive lam phi) := by
  rw [contDiff_infty]
  intro n
  have hdiff : Differentiable ℝ (weakODEPrimitive lam phi) := fun t =>
    (weakODEPrimitive_hasDerivAt lam phi hphi.continuous t).differentiableAt
  induction n with
  | zero =>
      exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
      apply (contDiff_succ_iff_deriv (n := n)).2
      refine ⟨hdiff,
        ?_, ?_⟩
      · intro hn
        exact (WithTop.natCast_ne_top n hn).elim
      · rw [weakODEPrimitive_deriv lam phi hphi.continuous]
        have hnle : (((n : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
            ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
        exact (contDiff_const.mul ih).sub (hphi.of_le hnle)

private def weakODEPlateau (a b : ℝ) (t : ℝ) : ℂ :=
  (Real.smoothTransition (t - (a - 1)) : ℂ) *
    (Real.smoothTransition ((b + 1) - t) : ℂ)

private lemma weakODEPlateau_contDiff (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weakODEPlateau a b) := by
  unfold weakODEPlateau
  exact (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ _
      (fun t : ℝ => Real.smoothTransition (t - (a - 1))))).mul
    (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ _
      (fun t : ℝ => Real.smoothTransition ((b + 1) - t))))

private lemma weakODEPlateau_hasCompactSupport (a b : ℝ) :
    HasCompactSupport (weakODEPlateau a b) := by
  refine HasCompactSupport.intro (K := Set.Icc (a - 1) (b + 1)) isCompact_Icc ?_
  intro t ht
  by_cases hleft : t ≤ a - 1
  · simp [weakODEPlateau, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hleft)]
  · have hright : b + 1 ≤ t := by
      by_contra hn
      exact ht ⟨le_of_not_ge hleft, le_of_not_ge hn⟩
    have hz : Real.smoothTransition ((b + 1) - t) = 0 :=
      Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hright)
    simp [weakODEPlateau, hz]

private lemma weakODEPlateau_eventually_one {a b t : ℝ}
    (ht : t ∈ Set.Ioo a b) :
    weakODEPlateau a b =ᶠ[𝓝 t] fun _ => 1 := by
  have hopen : Set.Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  filter_upwards [hopen] with s hs
  have hl : 1 ≤ s - (a - 1) := by linarith [hs.1]
  have hr : 1 ≤ (b + 1) - s := by linarith [hs.2]
  simp [weakODEPlateau, Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr]

private def weakODEAdjointTest (lam : ℂ) (phi : ℝ → ℂ) (a b : ℝ) (t : ℝ) : ℂ :=
  weakODEPlateau a b t * weakODEPrimitive lam phi t

private lemma weakODEAdjointTest_contDiff (lam : ℂ) (phi : ℝ → ℂ)
    (a b : ℝ) (hphi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weakODEAdjointTest lam phi a b) := by
  exact (weakODEPlateau_contDiff a b).mul
    (weakODEPrimitive_contDiff lam phi hphi)

private lemma weakODEAdjointTest_hasCompactSupport (lam : ℂ) (phi : ℝ → ℂ)
    (a b : ℝ) : HasCompactSupport (weakODEAdjointTest lam phi a b) := by
  change HasCompactSupport (weakODEPlateau a b * weakODEPrimitive lam phi)
  exact (weakODEPlateau_hasCompactSupport a b).mul_right

private lemma weakODEAdjointTest_equation_on_Ioo (lam : ℂ) (phi : ℝ → ℂ)
    (a b t : ℝ) (hphi : Continuous phi) (ht : t ∈ Set.Ioo a b) :
    -deriv (weakODEAdjointTest lam phi a b) t -
        lam * weakODEAdjointTest lam phi a b t = phi t := by
  have hevent := weakODEPlateau_eventually_one ht
  have hfun : weakODEAdjointTest lam phi a b =ᶠ[𝓝 t]
      weakODEPrimitive lam phi := by
    filter_upwards [hevent] with s hs
    simp [weakODEAdjointTest, hs]
  rw [hfun.deriv_eq, hfun.eq_of_nhds]
  rw [(weakODEPrimitive_hasDerivAt lam phi hphi t).deriv]
  ring

/-- A locally integrable homogeneous weak scalar ODE cannot have bounded time
support.  The proof uses a compactly supported adjoint solution on the support
interval and Mathlib's fundamental lemma of distributions. -/
theorem weakFirstOrderODE_eq_zero_of_boundedSupport
    (y : ℝ → ℂ) (lam : ℂ) (a b : ℝ)
    (hy : LocallyIntegrable y volume)
    (hsupp : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → y t = 0)
    (hweak : IsWeakFirstOrderODE y lam 0) :
    ∀ᵐ t ∂volume, y t = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hy
  intro phi hphi hphic
  let phiC : ℝ → ℂ := fun t => (phi t : ℂ)
  let eta : 𝓢(ℝ, ℂ) :=
    (weakODEAdjointTest_hasCompactSupport lam phiC a b).toSchwartzMap
      (weakODEAdjointTest_contDiff lam phiC a b (by
        exact Complex.ofRealCLM.contDiff.comp hphi))
  have hODE := hweak eta
  simp only [Pi.zero_apply, zero_mul, integral_zero] at hODE
  rw [← hODE]
  apply integral_congr_ae
  have hendpoints : ∀ᵐ t : ℝ ∂volume, t ≠ a ∧ t ≠ b := by
    filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b] with t hta htb
    exact ⟨hta, htb⟩
  filter_upwards [hsupp, hendpoints] with t hs htend
  by_cases ht : t ∈ Set.Icc a b
  · have ht' : t ∈ Set.Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm htend.1),
        lt_of_le_of_ne ht.2 htend.2⟩
    have heq := weakODEAdjointTest_equation_on_Ioo lam phiC a b t
      (by exact Complex.ofRealCLM.continuous.comp hphi.continuous) ht'
    change (phi t : ℂ) • y t = y t *
      (-deriv (weakODEAdjointTest lam phiC a b) t -
        lam * weakODEAdjointTest lam phiC a b t)
    rw [heq]
    simp [smul_eq_mul, phiC, mul_comm]
  · rw [hs ht]
    simp

/-- The source of a weak first-order ODE has the same exterior support as a
bounded-support solution.  This is the elementary locality statement needed
before using a branch-selected adjoint test. -/
theorem weakFirstOrderODE_source_eq_zero_off_boundedSupport
    (y g : ℝ → ℂ) (lam : ℂ) (a b : ℝ)
    (hy : LocallyIntegrable y volume) (hg : LocallyIntegrable g volume)
    (hsupp : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → y t = 0)
    (hweak : IsWeakFirstOrderODE y lam g) :
    ∀ᵐ t ∂volume, t ∉ Set.Icc a b → g t = 0 := by
  have hleft : ∀ᵐ t ∂volume, t ∈ Set.Iio a → g t = 0 := by
    apply isOpen_Iio.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (fun x hx => (hg x).filter_mono inf_le_left)
    intro phi hphi hphic hphisub
    let phiC : ℝ → ℂ := fun t => (phi t : ℂ)
    have hphiCc : HasCompactSupport phiC := by
      change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ phi)
      exact hphic.comp_left (by norm_num)
    let eta : 𝓢(ℝ, ℂ) := hphiCc.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hphi)
    have hODE := hweak eta
    have hyderiv : ∀ᵐ t ∂volume,
        y t * (-deriv (eta : ℝ → ℂ) t - lam * eta t) = 0 := by
      filter_upwards [hsupp] with t hs
      by_cases ht : t < a
      · rw [hs (by simp [ht])]
        simp
      · have hevent : phiC =ᶠ[𝓝 t] fun _ => 0 := by
          have htout : t ∉ tsupport phi := by
            intro hts
            exact (not_lt_of_ge (le_of_not_gt ht)) (hphisub hts)
          have hopen : (tsupport phi)ᶜ ∈ 𝓝 t :=
            (isClosed_tsupport phi).isOpen_compl.mem_nhds htout
          filter_upwards [hopen] with s hso
          apply Complex.ofReal_eq_zero.mpr
          by_contra hn
          exact hso (subset_tsupport _ hn)
        have heta : (eta : ℝ → ℂ) = phiC := rfl
        rw [heta, hevent.deriv_eq, hevent.eq_of_nhds]
        simp
    rw [integral_congr_ae hyderiv, integral_zero] at hODE
    have hz : ∫ t, g t * eta t = 0 := hODE.symm
    simpa [eta, phiC, smul_eq_mul, mul_comm] using hz
  have hright : ∀ᵐ t ∂volume, t ∈ Set.Ioi b → g t = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (fun x hx => (hg x).filter_mono inf_le_left)
    intro phi hphi hphic hphisub
    let phiC : ℝ → ℂ := fun t => (phi t : ℂ)
    have hphiCc : HasCompactSupport phiC := by
      change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ phi)
      exact hphic.comp_left (by norm_num)
    let eta : 𝓢(ℝ, ℂ) := hphiCc.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hphi)
    have hODE := hweak eta
    have hyderiv : ∀ᵐ t ∂volume,
        y t * (-deriv (eta : ℝ → ℂ) t - lam * eta t) = 0 := by
      filter_upwards [hsupp] with t hs
      by_cases ht : b < t
      · rw [hs (by simp [ht])]
        simp
      · have hevent : phiC =ᶠ[𝓝 t] fun _ => 0 := by
          have htout : t ∉ tsupport phi := by
            intro hts
            exact (not_lt_of_ge (le_of_not_gt ht)) (hphisub hts)
          have hopen : (tsupport phi)ᶜ ∈ 𝓝 t :=
            (isClosed_tsupport phi).isOpen_compl.mem_nhds htout
          filter_upwards [hopen] with s hso
          apply Complex.ofReal_eq_zero.mpr
          by_contra hn
          exact hso (subset_tsupport _ hn)
        have heta : (eta : ℝ → ℂ) = phiC := rfl
        rw [heta, hevent.deriv_eq, hevent.eq_of_nhds]
        simp
    rw [integral_congr_ae hyderiv, integral_zero] at hODE
    have hz : ∫ t, g t * eta t = 0 := hODE.symm
    simpa [eta, phiC, smul_eq_mul, mul_comm] using hz
  filter_upwards [hleft, hright] with t hl hr ht
  have hout : t < a ∨ b < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using ht
  rcases hout with hta | hbt
  · exact hl hta
  · exact hr hbt

private def weakODEAdjointFrom (lam : ℂ) (phi : ℝ → ℂ) (c t : ℝ) : ℂ :=
  -(Complex.exp (-lam * (t : ℂ)) *
    ∫ s in c..t, Complex.exp (lam * (s : ℂ)) * phi s)

private lemma weakODEAdjointFrom_hasDerivAt (lam : ℂ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) (c t : ℝ) :
    HasDerivAt (weakODEAdjointFrom lam phi c)
      (-lam * weakODEAdjointFrom lam phi c t - phi t) t := by
  let A : ℝ → ℂ := fun r =>
    ∫ s in c..r, Complex.exp (lam * (s : ℂ)) * phi s
  have hcont : Continuous (fun s : ℝ =>
      Complex.exp (lam * (s : ℂ)) * phi s) := by fun_prop
  have hA : HasDerivAt A (Complex.exp (lam * (t : ℂ)) * phi t) t := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable c t)
      (hcont.stronglyMeasurableAtFilter (μ := volume) (l := 𝓝 t))
      hcont.continuousAt
  have hlin : HasDerivAt (fun r : ℝ => -lam * (r : ℂ)) (-lam) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using!
      (hasDerivAt_id t).ofReal_comp.const_mul (-lam)
  have hmul := hlin.cexp.mul hA
  change HasDerivAt
    (fun r : ℝ => -(Complex.exp (-lam * (r : ℂ)) * A r))
    (-lam * -(Complex.exp (-lam * (t : ℂ)) * A t) - phi t) t
  apply hmul.neg.congr_deriv
  dsimp [A]
  have hcancel : Complex.exp (-lam * (t : ℂ)) *
      (Complex.exp (lam * (t : ℂ)) * phi t) = phi t := by
    rw [← mul_assoc, ← Complex.exp_add]
    rw [show -lam * (t : ℂ) + lam * (t : ℂ) = 0 by ring, Complex.exp_zero,
      one_mul]
  rw [hcancel]
  ring

private lemma weakODEAdjointFrom_deriv (lam : ℂ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) (c : ℝ) :
    deriv (weakODEAdjointFrom lam phi c) =
      fun t => -lam * weakODEAdjointFrom lam phi c t - phi t := by
  funext t
  exact (weakODEAdjointFrom_hasDerivAt lam phi hphi c t).deriv

private lemma weakODEAdjointFrom_contDiff (lam : ℂ) (phi : ℝ → ℂ) (c : ℝ)
    (hphi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (weakODEAdjointFrom lam phi c) := by
  rw [contDiff_infty]
  intro n
  have hdiff : Differentiable ℝ (weakODEAdjointFrom lam phi c) := fun t =>
    (weakODEAdjointFrom_hasDerivAt lam phi hphi.continuous c t).differentiableAt
  induction n with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
      apply (contDiff_succ_iff_deriv (n := n)).2
      refine ⟨hdiff, ?_, ?_⟩
      · intro hn
        exact (WithTop.natCast_ne_top n hn).elim
      · rw [weakODEAdjointFrom_deriv lam phi hphi.continuous c]
        have hnle : (((n : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
            ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
        exact (contDiff_const.mul ih).sub (hphi.of_le hnle)

private lemma weakODEAdjointFrom_norm_le_of_pos
    (lam : ℂ) (phi : ℝ → ℂ) (a t : ℝ)
    (hat : a ≤ t) (hlam : 0 ≤ lam.re)
    (hphi : Continuous phi) :
    ‖weakODEAdjointFrom lam phi a t‖ ≤ ∫ s in a..t, ‖phi s‖ := by
  unfold weakODEAdjointFrom
  have hrewrite : Complex.exp (-lam * (t : ℂ)) *
      (∫ s in a..t, Complex.exp (lam * (s : ℂ)) * phi s) =
      ∫ s in a..t, Complex.exp (-lam * ((t - s : ℝ) : ℂ)) * phi s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change Complex.exp (-lam * (t : ℂ)) *
        (Complex.exp (lam * (s : ℂ)) * phi s) =
      Complex.exp (-lam * ((t - s : ℝ) : ℂ)) * phi s
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [norm_neg, hrewrite]
  apply intervalIntegral.norm_integral_le_of_norm_le hat
  · filter_upwards with s hs
    rw [norm_mul, Complex.norm_exp]
    have hre : (-lam * ((t - s : ℝ) : ℂ)).re = -lam.re * (t - s) := by simp
    have hnonneg : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hexp : Real.exp (-lam * ((t - s : ℝ) : ℂ)).re ≤ 1 := by
      rw [hre, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) hnonneg
    exact mul_le_of_le_one_left (norm_nonneg _) hexp
  · exact hphi.norm.intervalIntegrable _ _

private lemma weakODEAdjointFrom_norm_le_of_neg
    (lam : ℂ) (phi : ℝ → ℂ) (t b : ℝ)
    (htb : t ≤ b) (hlam : lam.re ≤ 0)
    (hphi : Continuous phi) :
    ‖weakODEAdjointFrom lam phi b t‖ ≤ ∫ s in t..b, ‖phi s‖ := by
  have horient : weakODEAdjointFrom lam phi b t =
      Complex.exp (-lam * (t : ℂ)) *
        ∫ s in t..b, Complex.exp (lam * (s : ℂ)) * phi s := by
    unfold weakODEAdjointFrom
    rw [intervalIntegral.integral_symm]
    ring
  rw [horient]
  have hrewrite : Complex.exp (-lam * (t : ℂ)) *
      (∫ s in t..b, Complex.exp (lam * (s : ℂ)) * phi s) =
      ∫ s in t..b, Complex.exp (-lam * ((t - s : ℝ) : ℂ)) * phi s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change Complex.exp (-lam * (t : ℂ)) *
        (Complex.exp (lam * (s : ℂ)) * phi s) =
      Complex.exp (-lam * ((t - s : ℝ) : ℂ)) * phi s
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrewrite]
  apply intervalIntegral.norm_integral_le_of_norm_le htb
  · filter_upwards with s hs
    rw [norm_mul, Complex.norm_exp]
    have hre : (-lam * ((t - s : ℝ) : ℂ)).re = -lam.re * (t - s) := by simp
    have hnonpos : t - s ≤ 0 := sub_nonpos.mpr hs.1.le
    have hexp : Real.exp (-lam * ((t - s : ℝ) : ℂ)).re ≤ 1 := by
      rw [hre, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hlam) hnonpos
    exact mul_le_of_le_one_left (norm_nonneg _) hexp
  · exact hphi.norm.intervalIntegrable _ _

private def weakODECutoffAdjoint (lam : ℂ) (phi : ℝ → ℂ)
    (c a b t : ℝ) : ℂ :=
  weakODEPlateau (a - 1) (b + 1) t * weakODEAdjointFrom lam phi c t

private lemma weakODECutoffAdjoint_contDiff (lam : ℂ) (phi : ℝ → ℂ)
    (c a b : ℝ) (hphi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (weakODECutoffAdjoint lam phi c a b) := by
  exact (weakODEPlateau_contDiff (a - 1) (b + 1)).mul
    (weakODEAdjointFrom_contDiff lam phi c hphi)

private lemma weakODECutoffAdjoint_hasCompactSupport (lam : ℂ)
    (phi : ℝ → ℂ) (c a b : ℝ) :
    HasCompactSupport (weakODECutoffAdjoint lam phi c a b) := by
  change HasCompactSupport
    (weakODEPlateau (a - 1) (b + 1) * weakODEAdjointFrom lam phi c)
  exact (weakODEPlateau_hasCompactSupport (a - 1) (b + 1)).mul_right

private lemma weakODECutoffAdjoint_equation_on_Icc {lam : ℂ}
    {phi : ℝ → ℂ} {c a b t : ℝ} (hphi : Continuous phi)
    (ht : t ∈ Set.Icc a b) :
    -deriv (weakODECutoffAdjoint lam phi c a b) t -
        lam * weakODECutoffAdjoint lam phi c a b t = phi t := by
  have ht' : t ∈ Set.Ioo (a - 1) (b + 1) := by
    constructor <;> linarith [ht.1, ht.2]
  have hevent := weakODEPlateau_eventually_one ht'
  have hfun : weakODECutoffAdjoint lam phi c a b =ᶠ[𝓝 t]
      weakODEAdjointFrom lam phi c := by
    filter_upwards [hevent] with s hs
    simp [weakODECutoffAdjoint, hs]
  rw [hfun.deriv_eq, hfun.eq_of_nhds,
    (weakODEAdjointFrom_hasDerivAt lam phi hphi c t).deriv]
  ring

private lemma intervalIntegral_norm_le_integral_norm
    (phi : ℝ → ℂ) (hphi : Integrable phi) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖phi t‖) ≤ ∫ t, ‖phi t‖ := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun _ => norm_nonneg _)
    hphi.norm

private theorem weakFirstOrderODE_test_bound_of_boundedSupport
    (y g : ℝ → ℂ) (lam : ℂ) (a b : ℝ)
    (hab : a ≤ b)
    (hy : LocallyIntegrable y volume) (hg : LocallyIntegrable g volume)
    (hsuppy : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → y t = 0)
    (hsuppg : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → g t = 0)
    (hweak : IsWeakFirstOrderODE y lam g) :
    ∀ phi : ℝ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi → HasCompactSupport phi →
      ‖∫ t, y t * phi t‖ ≤
        (∫ t in a..b, ‖g t‖) * ∫ t, ‖phi t‖ := by
  intro phi hphi hphic
  have hphiInt : Integrable phi volume :=
    hphi.continuous.integrable_of_hasCompactSupport hphic
  have hgIcc : IntegrableOn g (Set.Icc a b) volume :=
    hg.integrableOn_isCompact isCompact_Icc
  by_cases hlam : 0 ≤ lam.re
  · let etaFun := weakODECutoffAdjoint lam phi a a b
    let eta : 𝓢(ℝ, ℂ) :=
      (weakODECutoffAdjoint_hasCompactSupport lam phi a a b).toSchwartzMap
        (weakODECutoffAdjoint_contDiff lam phi a a b hphi)
    have heta : (eta : ℝ → ℂ) = etaFun := rfl
    have hpair : (∫ t, y t * phi t) = ∫ t, g t * eta t := by
      rw [← hweak eta]
      apply integral_congr_ae
      filter_upwards [hsuppy] with t hyt
      by_cases ht : t ∈ Set.Icc a b
      · rw [heta]
        change y t * phi t = y t *
          (-deriv etaFun t - lam * etaFun t)
        rw [weakODECutoffAdjoint_equation_on_Icc hphi.continuous ht]
      · rw [hyt ht]
        simp
    rw [hpair]
    have hetaBound : ∀ t ∈ Set.Icc a b,
        ‖eta t‖ ≤ ∫ s, ‖phi s‖ := by
      intro t ht
      rw [heta]
      have hplateau : weakODEPlateau (a - 1) (b + 1) t = 1 :=
        (weakODEPlateau_eventually_one (by
          constructor <;> linarith [ht.1, ht.2])).eq_of_nhds
      change ‖weakODEPlateau (a - 1) (b + 1) t *
        weakODEAdjointFrom lam phi a t‖ ≤ _
      rw [hplateau, one_mul]
      exact (weakODEAdjointFrom_norm_le_of_pos lam phi a t ht.1 hlam
        hphi.continuous).trans
          (intervalIntegral_norm_le_integral_norm phi hphiInt ht.1)
    have hnorm : ∀ᵐ t ∂volume,
        ‖g t * eta t‖ ≤
          (Set.indicator (Set.Icc a b) (fun t => ‖g t‖) t) *
            ∫ s, ‖phi s‖ := by
      filter_upwards [hsuppg] with t hgt
      by_cases ht : t ∈ Set.Icc a b
      · simp only [Set.indicator_of_mem ht, norm_mul]
        exact mul_le_mul_of_nonneg_left (hetaBound t ht) (norm_nonneg _)
      · rw [hgt ht]
        simp [ht]
    have hmajor : Integrable (fun t =>
        Set.indicator (Set.Icc a b) (fun t => ‖g t‖) t *
          ∫ s, ‖phi s‖) volume := by
      exact ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).2
        hgIcc.norm).mul_const _
    refine (MeasureTheory.norm_integral_le_of_norm_le hmajor hnorm).trans_eq ?_
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  · have hlam' : lam.re ≤ 0 := le_of_not_ge hlam
    let etaFun := weakODECutoffAdjoint lam phi b a b
    let eta : 𝓢(ℝ, ℂ) :=
      (weakODECutoffAdjoint_hasCompactSupport lam phi b a b).toSchwartzMap
        (weakODECutoffAdjoint_contDiff lam phi b a b hphi)
    have heta : (eta : ℝ → ℂ) = etaFun := rfl
    have hpair : (∫ t, y t * phi t) = ∫ t, g t * eta t := by
      rw [← hweak eta]
      apply integral_congr_ae
      filter_upwards [hsuppy] with t hyt
      by_cases ht : t ∈ Set.Icc a b
      · rw [heta]
        change y t * phi t = y t *
          (-deriv etaFun t - lam * etaFun t)
        rw [weakODECutoffAdjoint_equation_on_Icc hphi.continuous ht]
      · rw [hyt ht]
        simp
    rw [hpair]
    have hetaBound : ∀ t ∈ Set.Icc a b,
        ‖eta t‖ ≤ ∫ s, ‖phi s‖ := by
      intro t ht
      rw [heta]
      have hplateau : weakODEPlateau (a - 1) (b + 1) t = 1 :=
        (weakODEPlateau_eventually_one (by
          constructor <;> linarith [ht.1, ht.2])).eq_of_nhds
      change ‖weakODEPlateau (a - 1) (b + 1) t *
        weakODEAdjointFrom lam phi b t‖ ≤ _
      rw [hplateau, one_mul]
      exact (weakODEAdjointFrom_norm_le_of_neg lam phi t b ht.2 hlam'
        hphi.continuous).trans
          (intervalIntegral_norm_le_integral_norm phi hphiInt ht.2)
    have hnorm : ∀ᵐ t ∂volume,
        ‖g t * eta t‖ ≤
          (Set.indicator (Set.Icc a b) (fun t => ‖g t‖) t) *
            ∫ s, ‖phi s‖ := by
      filter_upwards [hsuppg] with t hgt
      by_cases ht : t ∈ Set.Icc a b
      · simp only [Set.indicator_of_mem ht, norm_mul]
        exact mul_le_mul_of_nonneg_left (hetaBound t ht) (norm_nonneg _)
      · rw [hgt ht]
        simp [ht]
    have hmajor : Integrable (fun t =>
        Set.indicator (Set.Icc a b) (fun t => ‖g t‖) t *
          ∫ s, ‖phi s‖) volume := by
      exact ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).2
        hgIcc.norm).mul_const _
    refine (MeasureTheory.norm_integral_le_of_norm_le hmajor hnorm).trans_eq ?_
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]

private def weakODEApproxBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := ((1 : ℝ) / (n + 1)) / 2
  rOut := (1 : ℝ) / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply half_lt_self
    positivity

private lemma weakODEApproxBump_rOut_tendsto :
    Tendsto (fun n => (weakODEApproxBump n).rOut) atTop (𝓝 0) := by
  simpa [weakODEApproxBump] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma weakODEApproxBump_ratio :
    ∀ n, (weakODEApproxBump n).rOut ≤
      2 * (weakODEApproxBump n).rIn := by
  intro n
  change (1 : ℝ) / (n + 1) ≤ 2 * ((1 : ℝ) / (n + 1) / 2)
  ring_nf
  exact le_rfl

/-- A locally integrable complex function whose distributional pairing with
every compactly supported smooth test is bounded by its `L¹` norm is bounded
pointwise almost everywhere.  This is the approximate-identity form of the
`L¹`--`L∞` duality statement, avoiding any choice of an `L∞` representative. -/
private theorem ae_norm_le_of_smooth_test_bound
    (y : ℝ → ℂ) (M : ℝ) (hy : LocallyIntegrable y volume)
    (htest : ∀ phi : ℝ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi → HasCompactSupport phi →
      ‖∫ t, y t * phi t‖ ≤ M * ∫ t, ‖phi t‖) :
    ∀ᵐ t ∂volume, ‖y t‖ ≤ M := by
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := weakODEApproxBump)
    weakODEApproxBump_rOut_tendsto
    (Eventually.of_forall (weakODEApproxBump_ratio)) hy
  filter_upwards [hconv] with t ht
  apply le_of_tendsto ht.norm
  apply Eventually.of_forall
  intro n
  let psiR : ℝ → ℝ := fun s =>
    (weakODEApproxBump n).normed volume (t - s)
  let psi : ℝ → ℂ := fun s => (psiR s : ℂ)
  have hpsiDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi := by
    exact Complex.ofRealCLM.contDiff.comp
      ((weakODEApproxBump n).contDiff_normed.comp (by fun_prop))
  have hpsiComp : HasCompactSupport psiR := by
    change HasCompactSupport
      ((weakODEApproxBump n).normed volume ∘ (Homeomorph.subLeft t : ℝ → ℝ))
    exact (weakODEApproxBump n).hasCompactSupport_normed.comp_homeomorph
      (Homeomorph.subLeft t)
  have hpsiSupp : HasCompactSupport psi := by
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ psiR)
    exact hpsiComp.comp_left (by simp)
  have hb := htest psi hpsiDiff hpsiSupp
  have hleft :
      ((weakODEApproxBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] y) t =
        ∫ s, y s * psi s := by
    rw [MeasureTheory.convolution_lsmul_swap]
    apply integral_congr_ae
    filter_upwards with s
    simp only [ContinuousLinearMap.lsmul_apply, psi, psiR, smul_eq_mul]
    exact mul_comm _ _
  rw [hleft]
  refine hb.trans_eq ?_
  have hnorm : (fun s => ‖psi s‖) = fun s =>
      (weakODEApproxBump n).normed volume (t - s) := by
    funext s
    simp only [psi, psiR, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg ((weakODEApproxBump n).nonneg_normed _)]
  rw [hnorm, MeasureTheory.integral_sub_left_eq_self,
    (weakODEApproxBump n).integral_normed, mul_one]

/-- Sharp scalar weak-ODE estimate on a bounded-support solution.  No
regularity of the solution or source beyond local integrability is used. -/
theorem weakFirstOrderODE_ae_norm_le_of_boundedSupport
    (y g : ℝ → ℂ) (lam : ℂ) (a b : ℝ) (hab : a ≤ b)
    (hy : LocallyIntegrable y volume) (hg : LocallyIntegrable g volume)
    (hsupp : ∀ᵐ t ∂volume, t ∉ Set.Icc a b → y t = 0)
    (hweak : IsWeakFirstOrderODE y lam g) :
    ∀ᵐ t ∂volume, ‖y t‖ ≤ ∫ s in a..b, ‖g s‖ := by
  have hsuppg := weakFirstOrderODE_source_eq_zero_off_boundedSupport
    y g lam a b hy hg hsupp hweak
  exact ae_norm_le_of_smooth_test_bound y (∫ s in a..b, ‖g s‖) hy
    (weakFirstOrderODE_test_bound_of_boundedSupport
      y g lam a b hab hy hg hsupp hsuppg hweak)

end CubicNLSPhaseRetrieval
