import Lean_Code.BoundedHsAlgebra
import Lean_Code.CriticalQuadraticForms

/-!
# Bounded critical slices and their quadratic currents

The endpoint argument only multiplies localized `H^{1/2}` functions.  Such
localizations are bounded as physical functions, so the proved bounded
Gagliardo algebra is the precise product interface needed here.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- An `H^{1/2}` element whose physical representative is essentially
bounded. -/
structure BoundedCritical where
  val : Hs (1 / 2 : ℝ)
  bounded : eLpNorm (Hs.toL2 (by norm_num) val : ℝ → ℂ) ⊤ volume < ⊤

instance : Coe BoundedCritical (Hs (1 / 2 : ℝ)) := ⟨BoundedCritical.val⟩

/-- The physical representative of a bounded critical element. -/
def BoundedCritical.toL2 (f : BoundedCritical) : FourierL2 :=
  Hs.toL2 (by norm_num) f.val

/-- Complex conjugation preserves bounded critical regularity. -/
def BoundedCritical.conj (f : BoundedCritical) : BoundedCritical := by
  let hLip : LipschitzWith (1 : NNReal) (starRingEnd ℂ) :=
    Complex.isometry_conj.lipschitz
  let hzero : (starRingEnd ℂ) 0 = 0 := map_zero _
  let g : Hs (1 / 2 : ℝ) := Classical.choose
    (lipschitz_composition_exists (starRingEnd ℂ) 1 hLip hzero f.val)
  have hg : Hs.toL2 (by norm_num) g =
      lipschitzMapL2 (starRingEnd ℂ) 1 hLip hzero
        (Hs.toL2 (by norm_num) f.val) :=
    Classical.choose_spec
      (lipschitz_composition_exists (starRingEnd ℂ) 1 hLip hzero f.val)
  refine ⟨g, ?_⟩
  have hcoe : (Hs.toL2 (by norm_num) g : ℝ → ℂ) =ᵐ[volume]
      fun x => starRingEnd ℂ
        ((Hs.toL2 (by norm_num) f.val : ℝ → ℂ) x) := by
    rw [hg]
    exact coe_lipschitzMapL2 (starRingEnd ℂ) 1 hLip hzero _
  have hnorm : ∀ᵐ x : ℝ ∂volume,
      ‖(Hs.toL2 (by norm_num) g : ℝ → ℂ) x‖ =
        ‖(Hs.toL2 (by norm_num) f.val : ℝ → ℂ) x‖ := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    exact Complex.norm_conj _
  rw [eLpNorm_congr_norm_ae hnorm]
  exact f.bounded

lemma BoundedCritical.conj_toL2_ae (f : BoundedCritical) :
    (f.conj.toL2 : ℝ → ℂ) =ᵐ[volume]
      fun x => starRingEnd ℂ ((f.toL2 : ℝ → ℂ) x) := by
  unfold BoundedCritical.conj BoundedCritical.toL2
  dsimp only
  rw [Classical.choose_spec
    (lipschitz_composition_exists (starRingEnd ℂ) 1
      Complex.isometry_conj.lipschitz (map_zero _) f.val)]
  exact coe_lipschitzMapL2 (starRingEnd ℂ) 1
    Complex.isometry_conj.lipschitz (map_zero _) _

/-- Pointwise multiplication in `H^{1/2} ∩ L∞`. -/
def BoundedCritical.mul (f g : BoundedCritical) : BoundedCritical := by
  let p : Hs (1 / 2 : ℝ) := Classical.choose
    (boundedHs_product_exists f.val g.val f.bounded g.bounded)
  have hp := Classical.choose_spec
    (boundedHs_product_exists f.val g.val f.bounded g.bounded)
  refine ⟨p, ?_⟩
  have hpoint : (Hs.toL2 (by norm_num) p : ℝ → ℂ) =ᵐ[volume]
      fun x => (f.toL2 : ℝ → ℂ) x * (g.toL2 : ℝ → ℂ) x := hp.2
  have hle : eLpNorm (Hs.toL2 (by norm_num) p : ℝ → ℂ) ⊤ volume ≤
      eLpNorm (f.toL2 : ℝ → ℂ) ⊤ volume *
        eLpNorm (g.toL2 : ℝ → ℂ) ⊤ volume := by
    rw [eLpNorm_congr_ae hpoint]
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_top ⊤
      (Lp.aestronglyMeasurable f.toL2) (g.toL2 : ℝ → ℂ)
      (fun x y : ℂ => x * y) 1
      (Filter.Eventually.of_forall fun x => by simp)
  exact hle.trans_lt (ENNReal.mul_lt_top f.bounded g.bounded)

lemma BoundedCritical.mul_toL2_ae (f g : BoundedCritical) :
    (f.mul g).toL2 =ᵐ[volume]
      fun x => (f.toL2 : ℝ → ℂ) x * (g.toL2 : ℝ → ℂ) x := by
  unfold BoundedCritical.mul BoundedCritical.toL2
  exact (Classical.choose_spec
    (boundedHs_product_exists f.val g.val f.bounded g.bounded)).2

/-- A Schwartz function, viewed as a bounded critical element. -/
def schwartzBoundedCritical (φ : SchwartzMap ℝ ℂ) : BoundedCritical := by
  let f : Hs (1 / 2 : ℝ) := Classical.choose (schwartz_Hs_half_exists φ)
  have hf : Hs.toL2 (by norm_num) f = φ.toLp 2 volume :=
    Classical.choose_spec (schwartz_Hs_half_exists φ)
  refine ⟨f, ?_⟩
  rw [hf, eLpNorm_congr_ae (φ.coeFn_toLp 2 volume)]
  exact (φ.memLp ⊤ volume).2

lemma schwartzBoundedCritical_toL2 (φ : SchwartzMap ℝ ℂ) :
    (schwartzBoundedCritical φ).toL2 = φ.toLp 2 volume := by
  exact Classical.choose_spec (schwartz_Hs_half_exists φ)

lemma schwartzBoundedCritical_toL2_ae (φ : SchwartzMap ℝ ℂ) :
    ((schwartzBoundedCritical φ).toL2 : ℝ → ℂ) =ᵐ[volume] φ := by
  rw [schwartzBoundedCritical_toL2]
  exact φ.coeFn_toLp 2 volume

/-- The distributional derivative selected by the proved translation
difference-quotient theorem. -/
def criticalDerivative :
    Hs (1 / 2 : ℝ) →L[ℂ] Hs (-(1 / 2 : ℝ)) :=
  Classical.choose translation_dq

theorem criticalDerivative_toTempered (f : Hs (1 / 2 : ℝ)) :
    Hs.toTempered (-(1 / 2 : ℝ)) (criticalDerivative f) =
      LineDeriv.lineDerivOp (1 : ℝ)
        (Hs.toTempered (1 / 2 : ℝ) f) :=
  (Classical.choose_spec (Classical.choose_spec translation_dq)).1 f

private theorem hsPairIntegrable (T : Hs (-(1 / 2 : ℝ)))
    (φ : Hs (1 / 2 : ℝ)) :
    Integrable (fun x : ℝ => (T : ℝ → ℂ) x * (φ : ℝ → ℂ) x) volume := by
  rw [← memLp_one_iff_integrable]
  simpa [mul_comm] using (Lp.memLp T).mul' (r := 1) (Lp.memLp φ)

/-- The critical dual pairing as a continuous bilinear map. -/
def criticalPairingLinear :
    Hs (-(1 / 2 : ℝ)) →ₗ[ℂ] Hs (1 / 2 : ℝ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ hsNegPairing
    (fun T₁ T₂ φ => by
      rw [hsNegPairing, hsNegPairing, hsNegPairing,
        ← integral_add (hsPairIntegrable T₁ φ) (hsPairIntegrable T₂ φ)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add T₁ T₂] with x hx
      rw [hx]
      simp only [Pi.add_apply]
      ring)
    (fun c T φ => by
      rw [hsNegPairing, hsNegPairing]
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c T] with x hx
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (fun T φ₁ φ₂ => by
      rw [hsNegPairing, hsNegPairing, hsNegPairing,
        ← integral_add (hsPairIntegrable T φ₁) (hsPairIntegrable T φ₂)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add φ₁ φ₂] with x hx
      rw [hx]
      simp only [Pi.add_apply]
      ring)
    (fun c T φ => by
      rw [hsNegPairing, hsNegPairing]
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c φ] with x hx
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)

/-- Continuous version of the critical dual pairing. -/
def criticalPairingCLM :
    Hs (-(1 / 2 : ℝ)) →L[ℂ] Hs (1 / 2 : ℝ) →L[ℂ] ℂ :=
  criticalPairingLinear.mkContinuous₂ 1 (fun T φ => by
    change ‖hsNegPairing T φ‖ ≤ 1 * ‖T‖ * ‖φ‖
    simpa using hsNegPairing_bound T φ)

/-- The localized complex quadratic current `conj(f) f_x`. -/
def boundedQuadraticCurrent (f : BoundedCritical)
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  criticalPairingCLM (criticalDerivative f.val)
    ((schwartzBoundedCritical φ).mul f.conj).val

/-- The holomorphic Wronskian form `g f_x - f g_x`. -/
def boundedWronskianForm (f g : BoundedCritical)
    (φ : SchwartzMap ℝ ℂ) : ℂ :=
  criticalPairingCLM (criticalDerivative f.val)
      ((schwartzBoundedCritical φ).mul g).val -
    criticalPairingCLM (criticalDerivative g.val)
      ((schwartzBoundedCritical φ).mul f).val

end CubicNLSPhaseRetrieval
