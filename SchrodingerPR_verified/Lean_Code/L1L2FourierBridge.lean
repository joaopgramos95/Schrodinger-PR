import Mathlib

/-!
# Compatibility of the `L¹` and `L²` inverse Fourier transforms

Mathlib provides the integral Fourier transform on `L¹` and the Plancherel
transform on `L²`.  This file records that the two representatives agree when
both hypotheses are available.  The statement is useful when an `L²` identity
has first been proved by Plancherel and continuity of the integral
representative is needed afterwards.
-/

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section

set_option maxHeartbeats 2000000

namespace CubicNLSPhaseRetrieval

def inverseIntegral (b : ℝ → ℂ) (t : ℝ) : ℂ := 𝓕⁻ b t

lemma inverseIntegral_continuous {b : ℝ → ℂ} (hb : Integrable b) :
    Continuous (inverseIntegral b) := by
  unfold inverseIntegral
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hb

lemma inverseIntegral_locallyIntegrable {b : ℝ → ℂ} (hb : Integrable b) :
    LocallyIntegrable (inverseIntegral b) volume :=
  (inverseIntegral_continuous hb).locallyIntegrable

lemma inverseIntegral_bounded {b : ℝ → ℂ} (hb : Integrable b) :
    ∃ C : ℝ, ∀ t : ℝ, ‖inverseIntegral b t‖ ≤ C := by
  refine ⟨∫ x, ‖b x‖, fun t => ?_⟩
  unfold inverseIntegral
  rw [Real.fourierInv_eq']
  calc
    _ ≤ ∫ x, ‖Complex.exp
        (((2 * Real.pi * @inner ℝ ℝ _ x t : ℝ) : ℂ) * Complex.I) • b x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The Plancherel inverse agrees a.e. with the ordinary inverse Fourier
integral on `L¹ ∩ L²`. -/
theorem l1_l2_fourierInv_bridge {b : ℝ → ℂ}
    (hb1 : MemLp b 1 volume) (hb2 : MemLp b 2 volume) :
    ((𝓕⁻ (hb2.toLp b) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
      inverseIntegral b := by
  let B : Lp ℂ 2 volume := hb2.toLp b
  have hleft : LocallyIntegrable
      ((𝓕⁻ B : Lp ℂ 2 volume) : ℝ → ℂ) volume :=
    (Lp.memLp (𝓕⁻ B : Lp ℂ 2 volume)).locallyIntegrable (by norm_num)
  have hright : LocallyIntegrable (inverseIntegral b) volume :=
    inverseIntegral_locallyIntegrable (memLp_one_iff_integrable.mp hb1)
  apply ae_eq_of_integral_contDiff_smul_eq hleft hright
  intro g hgdiff hgc
  let gC : ℝ → ℂ := fun x => (g x : ℂ)
  have hgCdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gC :=
    Complex.ofRealCLM.contDiff.comp hgdiff
  have hgCc : HasCompactSupport gC := by
    change HasCompactSupport ((fun r : ℝ => (r : ℂ)) ∘ g)
    exact hgc.comp_left (by simp)
  let gs : 𝓢(ℝ, ℂ) := hgCc.toSchwartzMap hgCdiff
  have hBdist := MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq B
  have heval := congrFun (congrArg DFunLike.coe hBdist) gs
  rw [TemperedDistribution.fourierInv_apply] at heval
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply] at heval
  have hBcoe : (B : ℝ → ℂ) =ᵐ[volume] b := hb2.coeFn_toLp
  have hleftrewrite :
      (∫ x : ℝ, (gs : ℝ → ℂ) x •
          ((𝓕⁻ B : Lp ℂ 2 volume) : ℝ → ℂ) x) =
        ∫ x : ℝ, g x •
          ((𝓕⁻ B : Lp ℂ 2 volume) : ℝ → ℂ) x := by
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have hfreqrewrite :
      (∫ x : ℝ, (𝓕⁻ gs) x • (B : ℝ → ℂ) x) =
        ∫ x : ℝ, (𝓕⁻ gs) x * b x := by
    apply integral_congr_ae
    filter_upwards [hBcoe] with x hx
    rw [hx]
    simp [smul_eq_mul]
  rw [← hleftrewrite, ← heval, hfreqrewrite]
  have hbint : Integrable b := memLp_one_iff_integrable.mp hb1
  have hgsint : Integrable (gs : ℝ → ℂ) := gs.integrable
  rw [show (∫ x : ℝ, g x • inverseIntegral b x) =
      ∫ x : ℝ, inverseIntegral b x * (gs : ℝ → ℂ) x by
    apply integral_congr_ae
    filter_upwards with x
    simp [gC, gs, smul_eq_mul, mul_comm]]
  unfold inverseIntegral
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by
    ext x y
    simp [real_inner_comm]
  have hswap :=
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := -innerₗ ℝ) Real.continuous_fourierChar
      (by fun_prop) hbint hgsint)
  rw [hflip] at hswap
  have hgsraw (x : ℝ) : (𝓕⁻ gs) x =
      VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ)
        (gs : ℝ → ℂ) x := by
    rw [congrFun (SchwartzMap.fourierInv_coe gs) x]
    rfl
  have hbraw (x : ℝ) : (𝓕⁻ b) x =
      VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) b x := rfl
  simp_rw [hgsraw, hbraw]
  exact (by simpa only [smul_eq_mul, mul_comm] using hswap.symm)

end CubicNLSPhaseRetrieval
