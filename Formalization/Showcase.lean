/-
  showcase.lean  —  self-contained Lean 4 / Mathlib SHOWCASE for the main result of

      "Phase Retrieval for the One-Dimensional Cubic NLS"  (paper.tex).

  ┌────────────────────────────────────────────────────────────────────────────┐
  │  PRIMARY TARGET — Corollary `cor:interval-version` ("Equality on any time    │
  │  interval").  Fix σ ∈ ℝ.  Let u, v be global mild solutions of               │
  │        i ∂_t u + ∂ₓ² u = σ |u|² u.                                           │
  │  If |u| = |v| almost everywhere on (a,b) × ℝ for one nonempty open time       │
  │  interval (a,b), then there is ζ ∈ ℂ with |ζ| = 1 and v(t) = ζ · u(t) in      │
  │  L²(ℝ) for every t ∈ ℝ.                                                       │
  │                                                                              │
  │  Theorem 1.1 (`thm:main`, spacetime-a.e. modulus) is the special case         │
  │  (a,b) = (0,1) and is PROVED here from the interval statement.                │
  └────────────────────────────────────────────────────────────────────────────┘

  This file compiles against the audited Lake project; every definition in this showcase
  remains explicit, and the interval theorem is discharged by the project proof.
  It mirrors the Lake project modules `CubicNLS/{Propagator,Solution,PhaseRetrieval}.lean`
  and the human-readable statement in the paper; the free propagator `S(t)=e^{it∂ₓ²}` is
  CONSTRUCTED from Mathlib's L²-Fourier transform and identified with the paper's `S(t)`
  by the proved bridge lemma `fourier_freeProp` (its defining property `eq:free-group`).
-/
import Mathlib
import CubicNLSPhaseRetrieval

open MeasureTheory

noncomputable section

namespace CubicNLS

/-! ### The free Schrödinger propagator `S(t) = e^{i t ∂ₓ²}`, constructed from `𝓕` -/

/-- The complex Hilbert space `L²(ℝ)` (paper §1.1). -/
abbrev L2 : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- The Fourier transform `𝓕` on `L²(ℝ)` as a unitary (Plancherel, §2.1).  Mathlib
convention: `𝓕 f (ξ) = ∫ e^{-2π i x ξ} f`. -/
def fourierL2 : L2 ≃ₗᵢ[ℂ] L2 := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-- The free Schrödinger multiplier `e^{-4π² i t ξ²}` — the symbol of `S(t)=e^{it∂ₓ²}` in
Mathlib's Fourier convention (paper eq. (3.1) `eq:free-group`, `e^{-itξ²}`). -/
def schrodingerSymbol (t ξ : ℝ) : ℂ :=
  Complex.exp (((-(4 * Real.pi ^ 2 * t * ξ ^ 2) : ℝ) : ℂ) * Complex.I)

lemma norm_schrodingerSymbol (t ξ : ℝ) : ‖schrodingerSymbol t ξ‖ = 1 := by
  unfold schrodingerSymbol; exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_schrodingerSymbol (t : ℝ) : Continuous (schrodingerSymbol t) := by
  unfold schrodingerSymbol; fun_prop

/-- Multiplication by the (bounded, unit-modulus) symbol sends `L²` to `L²`. -/
def multSymbol (t : ℝ) (g : L2) : L2 :=
  MemLp.toLp (fun ξ => schrodingerSymbol t ξ * (⇑g) ξ) (by
    have hmeas : AEStronglyMeasurable (fun ξ => schrodingerSymbol t ξ * (⇑g) ξ) volume :=
      (continuous_schrodingerSymbol t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)
    refine ((Lp.memLp g).norm).mono' hmeas ?_
    filter_upwards with ξ
    rw [norm_mul, norm_schrodingerSymbol, one_mul])

/-- The **free 1-D Schrödinger propagator** `S(t) = e^{i t ∂ₓ²}`, built as
`𝓕⁻¹ ∘ (· e^{-4π² i t ξ²}) ∘ 𝓕` (paper §3.1). -/
def freeProp (t : ℝ) (f : L2) : L2 := fourierL2.symm (multSymbol t (fourierL2 f))

lemma coeFn_multSymbol (t : ℝ) (g : L2) :
    (⇑(multSymbol t g) : ℝ → ℂ) =ᵐ[volume] fun ξ => schrodingerSymbol t ξ * (⇑g) ξ := by
  unfold multSymbol; exact MemLp.coeFn_toLp _

/-- **BRIDGE (proved): `freeProp` is the free group `S(t) = e^{i t ∂ₓ²}`.**  It acts as the
Fourier multiplier `e^{-4π² i t ξ²}`, which is exactly the paper's defining property
`eq:free-group`, `𝓕(S(t)f)(ξ) = e^{-i t ξ²} 𝓕f(ξ)` (in Mathlib's convention). -/
lemma fourier_freeProp (t : ℝ) (f : L2) :
    (⇑(fourierL2 (freeProp t f)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => schrodingerSymbol t ξ * (⇑(fourierL2 f)) ξ := by
  unfold freeProp
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact coeFn_multSymbol t (fourierL2 f)

lemma norm_multSymbol (t : ℝ) (g : L2) : ‖multSymbol t g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [coeFn_multSymbol t g] with ξ hξ
  rw [hξ, norm_mul, norm_schrodingerSymbol, one_mul]

/-- **`S(t) = freeProp t` is unitary** (an `L²`-isometry). -/
lemma norm_freeProp (t : ℝ) (f : L2) : ‖freeProp t f‖ = ‖f‖ := by
  unfold freeProp
  rw [LinearIsometryEquiv.norm_map, norm_multSymbol, LinearIsometryEquiv.norm_map]

/-! ### The global mild solution class -/

/--
A **global mild solution** of `i ∂_t u + ∂ₓ² u = σ |u|² u` on `ℝ × ℝ`, with the good
spacetime bounds of the paper's solution class (§1.1, Ch. 3).
-/
structure GlobalSolution (σ : ℝ) where
  /-- The solution curve `t ↦ u(t) ∈ L²`; `u ∈ C(ℝ; L²(ℝ))`. -/
  u : ℝ → L2
  continuous : Continuous u
  /-- **Good bound.** `u ∈ L⁶_loc(ℝ²)` (paper `thm:GWP`; forces `|u|²u ∈ L¹_loc(ℝ; L²)`). -/
  memL6_loc : ∀ T : ℝ,
      (∫⁻ t in Set.Icc (-T) T, (eLpNorm (⇑(u t)) 6 volume) ^ 6 ∂volume) < ⊤
  /-- The cubic forcing `|u|²u` as an `L²`-valued curve, identified a.e. in `t`. -/
  nonlin : ℝ → L2
  nonlin_eq : ∀ᵐ t ∂(volume : Measure ℝ),
      (⇑(nonlin t) : ℝ → ℂ) =ᵐ[volume]
        fun x => ((‖(u t) x‖ ^ 2 : ℝ) : ℂ) * (u t) x
  /-- **Good bound.** The Duhamel integrand is Bochner-integrable (`eq:forcing-L1L2`). -/
  forcing_integrable : ∀ t₀ t : ℝ,
      IntervalIntegrable (fun s => freeProp (t - s) (nonlin s)) volume t₀ t
  /-- **Duhamel** (paper eq. (1.2) `eq:mild-main`):
      `u(t) = S(t−t₀) u(t₀) − i σ ∫_{t₀}^{t} S(t−s) (|u|² u)(s) ds`. -/
  mild : ∀ t t₀ : ℝ,
      u t = freeProp (t - t₀) (u t₀)
        - (Complex.I * (σ : ℂ)) • ∫ s in t₀..t, freeProp (t - s) (nonlin s)

/-! ### The showcase theorem (and Theorem 1.1 as its special case) -/

/--
**PRIMARY TARGET — Corollary `cor:interval-version` of paper.tex.**

Fix `σ ∈ ℝ`.  Let `u, v` be global mild solutions.  If their moduli agree almost everywhere
on `(a,b) × ℝ` for one nonempty open time interval `(a,b)` (`a < b`), then there is a
unimodular `ζ ∈ ℂ`, `|ζ| = 1`, with `v(t) = ζ · u(t)` in `L²(ℝ)` for **every** `t`.
-/
theorem phase_retrieval_interval (σ : ℝ) (u v : GlobalSolution σ)
    (a b : ℝ) (hab : a < b)
    (hJ : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
        p.1 ∈ Set.Ioo a b → ‖(u.u p.1) p.2‖ = ‖(v.u p.1) p.2‖) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ t : ℝ, v.u t = ζ • u.u t := by
  let up : CubicNLSPhaseRetrieval.GlobalSolution σ :=
    { u := u.u
      continuous := u.continuous
      memL6_loc := u.memL6_loc
      nonlin := u.nonlin
      nonlin_eq := u.nonlin_eq
      forcing_integrable := u.forcing_integrable
      mild := u.mild }
  let vp : CubicNLSPhaseRetrieval.GlobalSolution σ :=
    { u := v.u
      continuous := v.continuous
      memL6_loc := v.memL6_loc
      nonlin := v.nonlin
      nonlin_eq := v.nonlin_eq
      forcing_integrable := v.forcing_integrable
      mild := v.mild }
  have hJp : CubicNLSPhaseRetrieval.SameModulusOn a b up.u vp.u := hJ
  simpa [up, vp] using
    (CubicNLSPhaseRetrieval.phase_retrieval_interval σ up vp a b hab hJp)

/--
**Theorem 1.1 (Main phase-retrieval theorem, `thm:main`)** of paper.tex.

Equal modulus almost everywhere in ALL of spacetime forces the global unimodular relation.
This is the special case `(a,b) = (0,1)` of `phase_retrieval_interval`; verifying the
interval theorem verifies this automatically. -/
theorem phase_retrieval_cubic_NLS (σ : ℝ) (u v : GlobalSolution σ)
    (hmod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
        ‖(u.u p.1) p.2‖ = ‖(v.u p.1) p.2‖) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ t : ℝ, v.u t = ζ • u.u t :=
  phase_retrieval_interval σ u v 0 1 (by norm_num) (hmod.mono (fun _ hp _ => hp))

end CubicNLS

#print axioms CubicNLS.phase_retrieval_interval
#print axioms CubicNLS.phase_retrieval_cubic_NLS
