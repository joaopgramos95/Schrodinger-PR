import Lean_Code.ScalarMixedNorms
import Lean_Code.FreeSchrodinger

/-!
# Cubic NLS setup and canonical solution interface

Blueprint chapter: `chap:setup`, plus the canonical `L2`, `freeProp`, and
`GlobalSolution` interface shared with `showcase.lean`.
Imports: modules 0 and 2.
-/

open MeasureTheory

noncomputable section

namespace CubicNLSPhaseRetrieval

/-- The scalar cubic nonlinearity `σ |z|² z` from `def:cubic-nls`. -/
def cubicNonlinearity (σ : ℝ) (z : ℂ) : ℂ := ((σ * ‖z‖ ^ 2 : ℝ) : ℂ) * z

/--
The canonical global mild-solution interface, definitionally parallel to the structure in
`showcase.lean`. It records continuity, the local L⁶ bound, the cubic representative,
Bochner integrability, and the global Duhamel formula.
-/
structure GlobalSolution (σ : ℝ) where
  u : ℝ → L2
  continuous : Continuous u
  memL6_loc : ∀ T : ℝ,
      (∫⁻ t in Set.Icc (-T) T, (eLpNorm (⇑(u t)) 6 volume) ^ 6 ∂volume) < ⊤
  nonlin : ℝ → L2
  nonlin_eq : ∀ᵐ t ∂(volume : Measure ℝ),
      (⇑(nonlin t) : ℝ → ℂ) =ᵐ[volume]
        fun x => ((‖(u t) x‖ ^ 2 : ℝ) : ℂ) * (u t) x
  forcing_integrable : ∀ t₀ t : ℝ,
      IntervalIntegrable (fun s => freeProp (t - s) (nonlin s)) volume t₀ t
  mild : ∀ t t₀ : ℝ,
      u t = freeProp (t - t₀) (u t₀)
        - (Complex.I * (σ : ℂ)) • ∫ s in t₀..t, freeProp (t - s) (nonlin s)

private lemma multSymbol_zero (t : ℝ) : multSymbol t (0 : L2) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_multSymbol t (0 : L2),
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx h0
  rw [hx, h0]
  simp

private lemma freeProp_zero (t : ℝ) : freeProp t (0 : L2) = 0 := by
  unfold freeProp
  rw [map_zero, multSymbol_zero, map_zero]

/-- The canonical solution class is nonempty: the zero solution satisfies all
recorded spacetime and Duhamel requirements. -/
def zeroGlobalSolution (σ : ℝ) : GlobalSolution σ where
  u := fun _ => 0
  continuous := continuous_const
  memL6_loc := by
    intro T
    have hz : eLpNorm (⇑(0 : L2)) 6 volume = 0 := by
      rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)), eLpNorm_zero]
    rw [hz, zero_pow (by norm_num : (6 : ℕ) ≠ 0)]
    rw [lintegral_zero]
    exact ENNReal.zero_lt_top
  nonlin := fun _ => 0
  nonlin_eq := by
    filter_upwards with t
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    simp
  forcing_integrable := by
    intro t₀ t
    have hzero : (fun s : ℝ => freeProp (t - s) (0 : L2)) =
        (0 : ℝ → L2) := by
      funext s
      exact freeProp_zero _
    rw [hzero]
    exact (integrable_zero ℝ L2 (volume : Measure ℝ)).intervalIntegrable
  mild := by
    intro t t₀
    simp only [freeProp_zero, intervalIntegral.integral_zero, smul_zero,
      sub_zero]

instance (σ : ℝ) : Nonempty (GlobalSolution σ) := ⟨zeroGlobalSolution σ⟩

/-- Equality of physical moduli on a measurable spacetime region. -/
def SameModulusOnSet (I : Set ℝ) (u v : ℝ → L2) : Prop :=
  ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
    p.1 ∈ I → ‖(u p.1 : ℝ → ℂ) p.2‖ = ‖(v p.1 : ℝ → ℂ) p.2‖

end CubicNLSPhaseRetrieval
