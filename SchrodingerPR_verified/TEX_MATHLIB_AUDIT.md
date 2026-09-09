# paper.tex → Lean/Mathlib readiness audit

**Manuscript:** `paper.tex` — "Phase Retrieval for the One-Dimensional Cubic NLS"
**Target:** Lean 4 / Mathlib **v4.32.0**, commit `81a5d257c8e410db227a6665ed08f64fea08e997` (dated **2026‑07‑13**).
**Main result audited:** `thm:main` (paper.tex:4181‑4197), `cor:interval-version` (4201‑4211), `cor:H1-case` (4213‑4221).
**Method:** direct primary-source checks of the pinned Mathlib commit (curl of raw source) + a 44‑agent
chapter-by-chapter self-containment audit with adversarial verification of every flagged gap.

---

## TL;DR — the three questions

| # | Question | Verdict |
|---|---|---|
| Q1 | Fully self-contained proof of the main result? | **YES** — zero surviving genuine gaps on the `thm:main` path; all PDE machinery proved in-document; acyclic; bottoms out only at the declared foundational layer (4624‑4651). |
| Q2 | Split in a Lean-friendly way? | **MOSTLY** (medium–high) — ~90 discrete numbered results, backward-only deps; but two infra layers (mixed norms; H^{±1/2} calculus) have **APIs specified only in prose**, one appendix lemma is forward-referenced, and the C2 mixed-norm chapter has no slot in the 15‑module order. |
| Q3 | Only uses things available in Mathlib v4.32.0? | **YES for the leaves, NO for "little code."** Every main-path leaf is a confirmed-present Mathlib v4.32.0 fact or an earlier in-paper result. Exactly **one** genuinely-missing foundational leaf (variable-coefficient integral Grönwall), and it is **off the main path**. But "leaves in Mathlib" ≠ "little new code": this is a ~15‑module, ~90‑result from-scratch build of 1D dispersive PDE theory. |

**One-line bottom line:** You will **not** be forced to build analytic infrastructure that lives neither in Mathlib
nor in the paper — the paper is genuinely self-contained down to Mathlib v4.32.0 foundations. But formalizing it is a
**large** project (Strichartz, well-posedness, local smoothing, H^{±1/2} calculus, traces, a full self-contained
Carleman/unique-continuation theorem), not a thin wrapper over existing Mathlib.

---

## PRIMARY-SOURCE Mathlib v4.32.0 verification (checked directly at commit 81a5d25)

The paper's pinned commit `81a5d25` was confirmed to be the real v4.32.0 tag commit (`81a5d257c8e...`).

### The 8 named "bootstrap Fourier/Sobolev entry points" (paper.tex:4607‑4616) — ALL EXIST
`Mathlib/Analysis/Fourier/LpSpace.lean`:
- `MeasureTheory.Lp.fourierTransformₗᵢ` — L² Fourier as `≃ₗᵢ[ℂ]` (def, line 50) ✓
- `MeasureTheory.Lp.norm_fourier_eq` — ‖𝓕 f‖=‖f‖ (line 89) ✓
- `MeasureTheory.Lp.inner_fourier_eq` — ⟪𝓕 f,𝓕 g⟫=⟪f,g⟫ (line 93) ✓
- `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` (line 126) ✓

`Mathlib/Analysis/Distribution/Sobolev.lean`:
- `TemperedDistribution.MemSobolev (s:ℝ)(p:ℝ≥0∞)[Fact(1≤p)](f:𝓢'(E,F)):Prop` — Bessel-potential def (line 149) ✓
- `TemperedDistribution.MemSobolev.lineDerivOp` — **p=2 only** (line 316) ✓
- `TemperedDistribution.MemSobolev.laplacian` — **p=2 only** (line 344) ✓
- ⚠️ **Naming nuance:** exact identifier `memSobolev_two_iff_fourier` appears only in the module docstring (line 34),
  not as a theorem. The p=2 Fourier characterization is present under **different names**:
  `memSobolev_iff_exists_smulLeftCLM_fourier` (218), `memSobolev_zero_iff_exists_fourier` (233),
  `memSobolev_besselPotential_iff` (196). `#check` and alias the real one.

> Historical note: this tempered-distribution/Sobolev stack is the merged descendant of the Oct‑2025 arXiv paper
> "Formalizing Schwartz functions and tempered distributions" (fork `mcdoll/mathlib4:formal_schwartz`), which was
> *not merged* as of Oct 2025 but **is in mainline by v4.32.0** (2026‑07). The full suite is present:
> `Analysis/Distribution/{Distribution, TestFunction, TemperedDistribution, TemperateGrowth, Support,
> FourierMultiplier, FourierSchwartz, Sobolev, SchwartzSpace, SchwartzSpace/{Basic,Deriv,Fourier}}.lean`.

### Rest of the "allowed foundational layer" (paper.tex:4624‑4647) — ALL PRESENT
- Max-modulus / three-lines building blocks: `Analysis/Complex/AbsMax.lean`, `Analysis/Complex/PhragmenLindelof.lean`
- Weak / Banach–Alaoglu: `Analysis/Normed/Module/WeakDual.lean`, `Topology/Algebra/Module/WeakDual.lean`
- Convolution / Young: `Analysis/Convolution.lean`, `Analysis/LConvolution.lean`, `Analysis/Fourier/Convolution.lean`
- Density: `MeasureTheory/Function/SimpleFuncDenseLp.lean` (+ Schwartz density via SchwartzSpace files)
- FTC / 1D AC: `.../IntervalIntegral/FundThmCalculus.lean`, `.../Bochner/FundThmCalculus.lean`,
  `.../IntervalIntegral/AbsolutelyContinuousFun.lean`
- Interval integral: `.../IntervalIntegral/Basic.lean`
- Gaussian/oscillatory Fourier (free kernel): `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`
- du Bois-Reymond / fundamental lemma of calc-of-variations: `Analysis/Distribution/AEEqOfIntegralContDiff.lean`
  (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`)
- L2Space: `MeasureTheory/Function/L2Space.lean`

### The ONE genuinely-missing foundational leaf
- **Variable-coefficient integral Grönwall** (‖w(t)‖ ≤ ∫ a(s)‖w(s)‖ds, a∈L¹_loc), used at **paper.tex:4248‑4249**.
  Mathlib `Gronwall.lean` ships only the **constant-K derivative form**. → **NOT in Mathlib**, but this is used
  ONLY in the off-path auxiliary `cor:linear-common-potential` (4223‑4250), and is ~20–30 lines from the FTC.

### Things the paper PROVES ITSELF (so their absence from Mathlib is not a gap)
Hardy–Littlewood maximal function (weak-(1,1)+strong-(p,p), paper.tex:1139‑1204, explicitly "without invoking an
interpolation theorem"); time-line HLS (`lem:HLS-time`); three-lines (`lem:three-lines-explicit`); Riesz–Thorin
used-form (`lem:riesz-thorin-used`); Christ–Kiselev (`lem:CK`); van der Corput (in-line, 3373‑3412); the entire
H^{±1/2} calculus; mixed-norm L^q_tL^r_x spaces; all Strichartz; local smoothing; distribution-valued traces; the
half-space Carleman/unique-continuation theorem. **No PDE big theorem is imported as a black box anywhere.**
There is **no** Riesz–Thorin/interpolation file and **no** Hardy–Littlewood-maximal file in Mathlib v4.32.0 — but
neither is needed, because the paper builds them.

---

## Q1 — Self-contained? **YES** (for the main result)

Every PDE proposition on the path to `thm:main` has a complete in-document proof; the chain is acyclic and the only
leaves are the declared foundational layer. Main-line assembly is short and clean:
`F(0)=0` via half-space UC (`thm:halfspace-UC`, 4037) → `lem:Hilbert-wedge` (4146‑4177; trivial: Cauchy–Schwarz +
Fubini + inner-product homogeneity) → gauge covariance → `thm:main`.

**Surviving genuine gaps on the main path: NONE.**

**Genuine gaps, but OFF the main path (both in `cor:linear-common-potential`, 4223‑4250; nothing on the `thm:main`
path consumes it):**
1. Variable-coefficient integral Grönwall (4243‑4249) — "the elementary Grönwall argument… yields w=0"; never a
   numbered lemma; the one missing Mathlib leaf. Easily filled (~20–30 lines) or de-scope the corollary.
2. Under-specified hypothesis (4230‑4231): "possess the local half-derivative smoothing needed for the quadratic
   current" is purposive prose, not a transcribable `Prop` — the formalizer must select the exact norm/space
   (reconstructible from C6 `lem:point-smoothing`, ≈ cutoff `L²_t H^{1/2}_x`).

**Pseudo-gaps flagged by chapter auditors but REFUTED on verification** (so NOT gaps): "H^{-1/2} follows by duality"
(804, mechanical); 1D weak-FTC / difference-quotient `(τ_h f−f)/h→f'` (837/868/1685 — whitelisted foundation +
proved as `lem:Wp-difference-quotient` 825); "inverse FT of C_c^∞ is Schwartz" (708 — only uses `C_c^∞⊆S`, `F:S→S`);
`thm:fourier-gagliardo`/`lem:smooth-multiplier`/H^{±1/2} pairing "NOT-in-mathlib" (they are the paper's own Module-1
infra, proved); du Bois-Reymond at 2661 (present in Mathlib); the C12 "Riesz–Thorin/HLS/van der Corput/mixed-norm
NOT-in-mathlib" cluster (all earlier in-paper results or proved in-line).

**Residual risk (presence-of-proof vs. line-by-line correctness):** the audit confirmed a complete proof *exists* for
each proposition and that nothing external is imported — it did **not** re-derive every estimate. Two chapters carry
residual correctness risk that could not be exhaustively discharged at this depth:
- **C12 Carleman (`thm:halfspace-UC`, 3258‑4103) — highest risk.** Structure sound (acyclic; iteration arithmetic
  δ=L/32N, Nh→∞ checked; van der Corput in-line; Gaussian-regularization limits) but explicit oscillatory-kernel
  bounds, sign/branch conventions in `P_β`/`A(ξ)`, and the general-open-set `D'`-calculus verified for soundness of
  approach, not certified computationally. If one genuine error lurks in the main proof, C12 is the likeliest host.
- **C11 traces (`prop:Neumann-trace`, 3079‑3202) — moderate risk.** No blocking gap, but `eq:translated-test-multiplier`
  (3152) needs a quantitative, parameter-uniform, C^k-controlled multiplier bound; `lem:smooth-multiplier`'s
  qualitative *statement* doesn't literally supply it (its *proof* 794‑805 is already quantitative). Restate the lemma.

---

## Q2 — Lean-friendly split? **MOSTLY**

- **Granularity — HIGH.** ~90 numbered results (C2:10, C3:5, C4a:6, C4b:4, C5a:8, C5b:4, C6:4, C7:8, C8:5, C9‑10:4,
  C11:7, C12:15, C13:5) + un-audited Module 1 scaffolding. No monolith. Five dense proofs to pre-split into
  sub-lemmas: `thm:fourier-gagliardo` (669), `prop:Neumann-trace` (3079), `thm:hom-strichartz` (4,∞)-endpoint (1258),
  `thm:critical-wronskian` (2681), `lem:Tbeta-kernel` (3325).
- **Fixed representations — MOSTLY pinned, one soft cluster.** Well-pinned: `conv:joint-representatives` (266),
  `def:scalar-mixed-norm` (306, deliberately avoids nonseparable L^∞-Bochner), `T_β`/kernel (3325), zero-set-safe
  division-free regularizers (2718). **Soft cluster — all H^{±1/2} objects in Module 1 / Module 8:** `A(K)` test
  algebra (2389‑2398; density claim as stated is false at the 1D critical index H^{1/2}⊄C⁰ — must be redefined as the
  H^{1/2}+L^∞-closure of C_c^∞; the fix is definitional, since `lem:quadratic-form-extension` is actually proved by a
  direct formula); the H^{-1/2}–H^{1/2} pairing (prose-only `eq:quad-form` 2378‑2382, never numbered, load-bearing at
  804/2405/3107‑3202/2743‑2780); the current `f̄ f_x` (unnumbered + unstated locality lemma); H^{±1/2}_loc (no numbered
  cutoff definition); `A_x f` (2136‑2155); `X(I)`/`X_k(J)` inline Banach spaces (1477, 1812, completeness asserted in
  one sentence).
- **Dependency structure — acyclic, but the 15‑module order is incomplete.** Logical acyclicity holds (backward-only).
  Three frictions: (1) `lem:tensor-test-density` (4295, in an appendix) is forward-referenced from `thm:current-recovery`
  (2633) and `prop:G-equation` (3247) — self-contained, but no module slot; pull it early. (2) **C2 scalar mixed norms
  (255‑623) has NO module in `app:ledger`'s 15-module order**, yet is consumed by Strichartz (1255) and C12 (3275) —
  insert "Module 0: ScalarMixedNorms" before Module 4. (3) C2 closing prose (607‑615) forward-references later chapters
  (narrative only, DAG-clean).
- **The H^{1/2} predicate-vs-Hilbert bridge — the central burden (MEDIUM).** Mathlib gives `MemSobolev` only as a
  **Prop predicate** — no bundled H^{1/2} Hilbert space, no Gagliardo inner product, no H^{-1/2}–H^{1/2} pairing. The
  paper defines its *own* H^s (line 655, via ⟨ξ⟩^s f̂ ∈ L²). Module 1 must construct: (1) bundled H^{1/2} + Gagliardo⇔
  Fourier equivalence — **`thm:fourier-gagliardo` supplies this in full**; (2) H^{-1/2} + the complex-*bilinear*
  pairing — prose-only, must be numbered; (3) ∂:H^{1/2}→H^{-1/2} + difference quotients (`lem:translation-dq` 807,
  `lem:Wp-difference-quotient` 825); (4) smooth-multiplier boundedness (`lem:smooth-multiplier` 789) upgraded to a
  quantitative C^k form for C11's 3152; (5) H^s_loc cutoff definition. Proofs are honest/mechanical, but the **API is
  under-specified** and every downstream module (C7/C8/C9‑10/C11) breaks if it is chosen poorly. This is the module
  that most rewards up-front interface design.

---

## Q3 — Only uses Mathlib v4.32.0? **YES (leaves), NO ("little code")**

Leaf ledger and self-proved list are in the "PRIMARY-SOURCE" section above. Crucial distinction:
- **"Leaves are in Mathlib" → TRUE.** Every main-path leaf bottoms out in a confirmed-present v4.32.0 foundational
  fact or an earlier numbered in-paper result.
- **"Little new code needed" → FALSE.** ~90 numbered results across ~15 modules + the un-audited Module 1 H^{±1/2}
  scaffolding are genuinely new Lean, on top of Mathlib's analysis primitives.
- **Genuinely-missing foundational infra:** exactly one — variable-coefficient integral Grönwall (4248‑4249),
  off-path, tiny.

---

## Scope-of-work / hardest modules

Hardest, in order: **(1) Carleman (C12, 15 results)** — general-`D'` calculus, spatial Fourier of a time-parametrized
distributional ODE, explicit oscillatory-kernel bounds, countable-C¹-dense construction; highest residual correctness
risk. **(2) Traces (C11, `prop:Neumann-trace`)** — quantitative multiplier upgrade. **(3) Module 1 / critical H^{1/2}
calculus** — not the hardest math but the highest-leverage API design; every later module consumes it.

---

## Recommendations for the follow-up prompt

1. **`#check` the pinned entry points FIRST** (before any proof work) at commit 81a5d25:
   `Lp.fourierTransformₗᵢ`, `Lp.norm_fourier_eq`, `Lp.inner_fourier_eq`, `Lp.fourier_toTemperedDistribution_eq`,
   `TemperedDistribution.MemSobolev`, `.lineDerivOp`, `.laplacian`. For the p=2 Fourier characterization the paper
   calls `memSobolev_two_iff_fourier`, `#check` and alias the real name (`memSobolev_iff_exists_smulLeftCLM_fourier` /
   `memSobolev_besselPotential_iff`).
2. **Build the H^{1/2} bridge first (Module 1), design the interface before proofs.** Decide bundled H^s Hilbert space
   (⟨ξ⟩^s f̂∈L², line 655) vs. reuse `MemSobolev`; define H^{-1/2} and the **complex-bilinear** H^{-1/2}–H^{1/2}
   pairing (extending ∫Tφ, line 2382 — NOT the sesquilinear inner product) as numbered definitions; make
   `lem:smooth-multiplier` quantitative (C^k) at definition time.
3. **Add "Module 0: ScalarMixedNorms" (C2, 255‑623) before Strichartz**, and pull `lem:tensor-test-density` (4295)
   into an early utilities module — both are un-slotted in `app:ledger`.
4. **Start order:** Module 0 → Module 1 (full API) → utilities → C4a/C4b (Strichartz) → upward. Warm up with
   `lem:Hilbert-wedge` (4146‑4177): fully self-contained, Lean-clean, a good API smoke-test.
5. **De-scope `cor:linear-common-potential`** (4223‑4250) from the initial blueprint (both genuine gaps live there,
   off the main path). If kept, add a numbered variable-coefficient integral-Grönwall lemma + explicit Prop hypothesis.
6. **Promote implicit objects to numbered definitions** before translating: `A(K)` (H^{1/2}+L^∞-closure of C_c^∞);
   current `f̄ f_x` + locality lemma; `X(I)`/`X_k(J)` with completeness lemmas; H^{±1/2}_loc.
7. **Budget C12 (Carleman) and C11 (traces) for extra verification** — structure and leaf-availability are certified,
   full computational correctness of their kernel bounds and pairing manipulations is not.

---

## Caveats — what was and was NOT verified

- **DID verify:** presence of a complete in-document proof for every PDE proposition on the `thm:main` path;
  acyclicity of the DAG chapter-by-chapter; that no external non-foundational PDE/analysis theorem is imported on the
  main line; leaf availability (every leaf → confirmed-present Mathlib v4.32.0 fact or earlier numbered result), with
  specific identifiers curl-checked at commit 81a5d25 (`LpSpace.lean`, `Sobolev.lean`, `AbsolutelyContinuousFun.lean`,
  `AEEqOfIntegralContDiff.lean`, `Gronwall.lean`).
- **Did NOT verify:** full line-by-line mathematical correctness of the hardest chapters (C12 Carleman oscillatory
  kernels/branches/`D'`-calculus; C11 Neumann trace / quantitative multiplier) — checked for soundness of approach,
  not certified computationally. No Lean was compiled.
