import Lean_Code.CriticalWeakConvergence

/-!
# Extension of recovered currents to bounded critical coefficients

The recovered current is initially known on admissible smooth coefficients.
This file isolates the exact simultaneous approximation property needed to
pass to a rough coefficient.  The passage itself is axiom-free and uses the
critical weak-convergence theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

noncomputable section
namespace CubicNLSPhaseRetrieval

private lemma schwartz_mul_conj_val
    (f : BoundedCritical) (phi : SchwartzMap ℝ ℂ) :
    ((schwartzBoundedCritical phi).mul f.conj).val =
      schwartzHsMultiplier phi (criticalConj f.val) := by
  apply Hs.toL2_injective (s := (1 / 2 : ℝ)) (by norm_num)
  apply Lp.ext
  filter_upwards [BoundedCritical.mul_toL2_ae
      (schwartzBoundedCritical phi) f.conj,
    schwartzBoundedCritical_toL2_ae phi,
    BoundedCritical.conj_toL2_ae f,
    schwartzHsMultiplier_toL2_ae phi (criticalConj f.val),
    criticalConj_toL2_ae f.val] with x hp hphi hfc hr hc
  change (((schwartzBoundedCritical phi).mul f.conj).toL2 : ℝ → ℂ) x =
    (Hs.toL2 (by norm_num)
      (schwartzHsMultiplier phi (criticalConj f.val)) : ℝ → ℂ) x
  rw [hp, hphi, hfc, hr, hc]
  simp only [BoundedCritical.toL2]
  rw [mul_comm]

lemma criticalQuadraticCurrent_eq_boundedAgainst_schwartz
    (f : BoundedCritical) (phi : SchwartzMap ℝ ℂ) :
    criticalQuadraticCurrent f.val phi =
      boundedQuadraticCurrentAgainst f (schwartzBoundedCritical phi) := by
  unfold criticalQuadraticCurrent boundedQuadraticCurrentAgainst
  rw [schwartz_mul_conj_val]

/-- A rough coefficient is simultaneously approximable for the two currents
if admissible smooth coefficients converge after multiplication by each
conjugated slice, with uniform critical bounds. -/
def IsSimultaneousCurrentApproximation
    (chi : SchwartzMap ℝ ℂ) (f g a : BoundedCritical) : Prop :=
  ∃ phi : ℕ → SchwartzMap ℝ ℂ,
    (∀ n, IsAdmissibleCurrentTest chi (phi n)) ∧
    Tendsto (fun n => Hs.toL2 (by norm_num)
        (((schwartzBoundedCritical (phi n)).mul f.conj).val)) atTop
      (nhds (Hs.toL2 (by norm_num) ((a.mul f.conj).val))) ∧
    Tendsto (fun n => Hs.toL2 (by norm_num)
        (((schwartzBoundedCritical (phi n)).mul g.conj).val)) atTop
      (nhds (Hs.toL2 (by norm_num) ((a.mul g.conj).val))) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n, ‖((schwartzBoundedCritical (phi n)).mul f.conj).val‖ ≤ C) ∧
      (∀ n, ‖((schwartzBoundedCritical (phi n)).mul g.conj).val‖ ≤ C)

/-- Equality on all admissible smooth tests extends to every coefficient
with a simultaneous critical approximation. -/
theorem boundedQuadraticCurrentAgainst_eq_of_approximation
    (chi : SchwartzMap ℝ ℂ) (f g a : BoundedCritical)
    (hsmooth : ∀ phi : SchwartzMap ℝ ℂ, IsAdmissibleCurrentTest chi phi →
      criticalQuadraticCurrent f.val phi =
        criticalQuadraticCurrent g.val phi)
    (ha : IsSimultaneousCurrentApproximation chi f g a) :
    boundedQuadraticCurrentAgainst f a =
      boundedQuadraticCurrentAgainst g a := by
  rcases ha with ⟨phi, hadm, htoF, htoG, C, hC, hbF, hbG⟩
  have hpairF := criticalPairing_derivative_tendsto_of_toL2_of_bounded
    f.val (a.mul f.conj).val
    (fun n => ((schwartzBoundedCritical (phi n)).mul f.conj).val)
    htoF C hC hbF
  have hpairG := criticalPairing_derivative_tendsto_of_toL2_of_bounded
    g.val (a.mul g.conj).val
    (fun n => ((schwartzBoundedCritical (phi n)).mul g.conj).val)
    htoG C hC hbG
  have heq (n : ℕ) :
      criticalPairingCLM (criticalDerivative f.val)
          (((schwartzBoundedCritical (phi n)).mul f.conj).val) =
        criticalPairingCLM (criticalDerivative g.val)
          (((schwartzBoundedCritical (phi n)).mul g.conj).val) := by
    simpa only [criticalQuadraticCurrent_eq_boundedAgainst_schwartz,
      boundedQuadraticCurrentAgainst] using hsmooth (phi n) (hadm n)
  have hleft : Tendsto (fun n =>
      criticalPairingCLM (criticalDerivative f.val)
        (((schwartzBoundedCritical (phi n)).mul f.conj).val)) atTop
      (nhds (boundedQuadraticCurrentAgainst f a)) := by
    simpa only [boundedQuadraticCurrentAgainst] using hpairF
  have hright : Tendsto (fun n =>
      criticalPairingCLM (criticalDerivative g.val)
        (((schwartzBoundedCritical (phi n)).mul g.conj).val)) atTop
      (nhds (boundedQuadraticCurrentAgainst g a)) := by
    simpa only [boundedQuadraticCurrentAgainst] using hpairG
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

end CubicNLSPhaseRetrieval
