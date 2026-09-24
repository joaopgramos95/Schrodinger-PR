# Axiom status

## Current state

- Project axioms: 75
- `sorry` occurrences in `Lean_Code`: 0
- Stage: Step 4 declaration-faithful scaffold is complete through Module 15;
  Step 5 bottom-up axiom elimination is in progress.
- Current target dependency frontier (`#print axioms
  CubicNLSPhaseRetrieval.phase_retrieval_interval`): `hom_strichartz`,
  `exponential_separation`, and
  `zero_extension_jump`, in addition to Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

The former `moving_galilean_weak_equation` and `one_step_propagation` axioms
have been replaced by compiled proofs.  The latter now exposes its genuine
lower dependency, `exponential_separation`.

### Blocking interface defect discovered during elimination

The current definitions of `carlemanXNorm` and `carlemanYNorm` take infima over
arbitrary function decompositions, without requiring the decomposition pieces
to be (a.e. strongly) measurable.  Mathlib's `eLpNorm` is only a seminorm with
the needed triangle inequality on measurable inputs.  Consequently the
absorption step needed to prove `exponential_separation` is not derivable from
the present interface; nonmeasurable decompositions can undercut the intended
sum-space gauge.  A sound continuation must add measurability/MemLp membership
to the Carleman decomposition witnesses and thread measurable representatives
through the ridge-potential application.  This changes internal interfaces but
does not change the statements of `phase_retrieval_interval`,
`phase_retrieval_cubic_NLS`, or `GlobalSolution`.

## Current temporary axioms

| Lean axiom | Blueprint label | Full proof pointer | Why temporary |
|---|---|---|---|
| `gagliardo_fourier_identity` | `lem:gagliardo-fourier-identity` | — | Tonelli/Plancherel/change-of-variables proof pending. |
| `gagliardo_mollification` | `lem:gagliardo-mollification` | — | Convolution/Jensen formalization pending. |
| `gagliardo_cutoff_error` | `lem:gagliardo-cutoff-error` | — | Uniform near/far integral estimate pending. |
| `gagliardo_density` | `lem:gagliardo-density` | — | Weighted Fourier density and closure argument pending. |
| `smooth_multiplier_quantitative` | `lem:smooth-multiplier-quantitative` | — | Quantitative multiplier construction and duality pending. |
| `Wp_difference_quotient` | `lem:Wp-difference-quotient` | `paper.tex L825-L851` | Mathlib supplies strong `L^p` translation continuity, but the proof still needs an integral-Minkowski theorem for an `L^p`-valued translation average and a Fubini theorem identifying its bundled Bochner integral with the pointwise weak-FTC representative. |
| `countable_norming_Linfty` | `lem:countable-norming-Linfty` | — | Separable L¹ unit-ball construction pending. |
| `endpoint_norming` | `prop:endpoint-norming` | `paper.tex L441-L472` | Measurable maximizing-test construction pending. |
| `sum_intersection_complete` | `lem:sum-intersection-complete` | — | Quotient/closed-diagonal Banach proof pending. |
| `free_kernel_explicit` | `lem:free-kernel-explicit` | — | Gaussian regularization and boundary-value limit pending. |
| `propagator_compatibility` | `lem:propagator-compatibility` | — | Simultaneous L¹/L² Schwartz approximation pending. |
| `riesz_thorin_used` | `lem:riesz-thorin-used` | `paper.tex L1080-L1111` | Analytic-family interpolation proof pending. |
| `maximal_weak11` | `lem:maximal-weak11` | — | Greedy interval covering proof pending. |
| `maximal_strongp` | `lem:maximal-strongp` | — | Distribution-function integration proof pending. |
| `hedberg` | `lem:hedberg` | — | Near/far optimization proof pending. |
| `tensor_test_density` | `lem:tensor-test-density` | `paper.tex L4313-L4356` | Fourier-series separated-test approximation pending. |
| `distribution_slicing` | `lem:distribution-slicing` | — | Countable dense-test slicing proof pending. |
| `distributional_products` | `lem:distributional-products` | — | `v` now has genuine `MemScalarMixed` membership; the product-space Hölder/factorization proof is pending. |
| `TTstar_finite` | `lem:TTstar-finite` | — | Dispersive interpolation plus HLS pending. |
| `TTstar_endpoint` | `lem:TTstar-endpoint` | — | Scalar endpoint norming argument pending. |
| `strichartz_endpoint_identification` | `lem:strichartz-endpoint-identification` | — | Mixed/L² subsequence identification pending. |
| `hom_strichartz` | `thm:hom-strichartz` | `paper.tex L1225-L1320` | Depends on the three TT*/endpoint lemmas. |
| `christ_kiselev` | `lem:CK` | — | Dyadic time-ordering proof pending. |
| `inhom_strichartz` | `thm:inhom-str` | `paper.tex L1372-L1404` | The rough output is now tied to the completion of classical retarded Bochner Duhamel curves; the TT*/Christ–Kiselev estimates are pending. |
| `retarded_continuous` | `lem:retarded-continuous` | — | Completion/base-time/Bochner compatibility pending. |
| `cubic_65` | `lem:cubic-65` | — | Mixed Hölder and finite-time embedding pending. |
| `cubic_lip` | `lem:cubic-lip` | — | Pointwise cubic difference plus mixed Hölder pending. |
| `local_wellposedness` | `thm:LWP` | `paper.tex L1536-L1576` | Contraction, unconditional uniqueness, and Lipschitz flow pending. |
| `cubic_derivative_map` | `lem:cubic-derivative-map` | `paper.tex L1608-L1622` | Real-linear cubic estimates pending. |
| `H1_persistence` | `lem:H1-persistence` | `paper.tex L1639-L1701` | Linearized fixed point and difference quotients pending. |
| `mass_L2` | `prop:mass-L2` | — | H¹ approximation and flow stability pending. |
| `gelfand_chain_rule` | `lem:gelfand-chain-rule` | `paper.tex L1722-L1743` | The natural real-bilinear embedding/pairing compatibility is now explicit; the time-mollification product rule is pending. |
| `cubic_Hk_leibniz` | `lem:cubic-Hk-leibniz` | — | Lower derivatives now carry the required fixed-point mixed norms; the higher-order Leibniz estimate is pending. |
| `Hk_persistence` | `prop:Hk-persistence` | `paper.tex L1891-L1994` | `HigherFixedPointData` now identifies every slot with the corresponding iterated distributional derivative; the genuine persistence induction is pending. |
| `schwartz_smooth` | `lem:schwartz-smooth` | — | Smooth-data persistence and joint representative pending. |
| `endpoint_bound` | `prop:endpoint` | `paper.tex L2024-L2063` | Endpoint approximation and forcing stability pending. |
| `C0_slices` | `cor:C0-slices` | — | Combination of endpoint and one-dimensional Sobolev embedding pending. |
| `hom_smoothing` | `cor:hom-smoothing` | `paper.tex L2158-L2182` | The witness is now tied distributionally to `χ S(t)f`; the commutator/local-smoothing proof is pending. |
| `Duhamel_smoothing` | `prop:forced-smoothing` | `paper.tex L2186-L2212` | The witness is now tied to the cutoff of the displayed Duhamel solution; the Minkowski argument is pending. |
| `NLS_smoothing` | `cor:NLS-smoothing` | `paper.tex L2214-L2234` | Cutoff identity and stability of localized representatives are now explicit; the forcing/stability proof is pending. |
| `countable_full_measure` | `lem:countable-full-measure` | — | Countable cutoff exhaustion from the repaired `NLS_smoothing` interface and `C0_slices` is pending. |
| `gagliardo_product` | `lem:gagliardo-product` | — | Critical product estimate pending. |
| `lipschitz_composition` | `lem:lipschitz-composition` | — | Gagliardo difference estimate pending. |
| `mollification_critical_uniform` | `lem:mollification-critical-uniform` | `paper.tex L2288-L2312` | Approximants are now represented by smooth compactly supported functions; simultaneous `H^{1/2}`/uniform density is pending. |
| `quadratic_form_extension` | `lem:quadratic-form-extension` | `paper.tex L2401-L2436` | `Q` is now tied to the defining `H^{-1/2}`–`H^{1/2}` product pairing; the product bound and extension proof are pending. |
| `smooth_continuity_equation` | `lem:smooth-continuity-equation` | `paper.tex L2545-L2573` | Gelfand-triple weighted mass identity pending. |
| `current_recovery` | `thm:current-recovery` | `paper.tex L2599-L2671` | Approximation, tensor-density, and slicing argument pending. |
| `wronskian_smooth_approx` | `lem:wronskian-smooth-approx` | — | Critical cutoff product rule pending. |
| `wronskian_zero_set_safe` | `lem:wronskian-zero-set-safe` | — | Zero-safe critical multiplier construction pending. |
| `wronskian_current_form` | `lem:wronskian-current-form` | — | Regularized current-to-Wronskian limit pending. |
| `diagonal_wronskian` | `cor:diagonal-W` | — | Good-slice specialization pending. |
| `F_equation` | `prop:F-equation` | `paper.tex L2846-L2898` | Smooth approximation and factored forcing limit pending. |
| `Q_bounds` | `lem:Q-bounds` | — | Ridge change-of-variables bounds pending. |
| `interior_first_derivative` | `lem:interior-first-derivative` | — | Interior integration-by-parts estimate pending. |
| `H2_weak_limit` | `lem:H2-weak-limit` | — | Mollification/weak compactness argument pending. |
| `translated_test_multiplier` | `lem:translated-test-multiplier` | — | Quantitative translated multiplier estimate pending. |
| `scalarization_normal` | `lem:scalarization-normal` | — | Normal-variable local-H² argument pending. |
| `neumann_localization` | `lem:neumann-localization` | — | The test is now compactly supported; the nested-cutoff construction is pending. |
| `neumann_strong_convergence` | `lem:neumann-strong-convergence` | — | Dominated time-integrated difference quotient limit pending. |
| `neumann_trace_zero` | `prop:Neumann-trace` | `paper.tex L3087-L3205` | Difference-quotient trace identification pending. |
| `zero_extension_jump` | `prop:zero-extension-jump` | `paper.tex L3223-L3248` | Distributional boundary-jump calculation pending. |
| `G_equation` | `prop:G-equation` | `paper.tex L3207-L3257` | Zero extension plus integrability assembly pending. |
| `vandercorput_kernel` | `lem:vandercorput-kernel` | `paper.tex L3373-L3412` | The phase is now real-valued; the stationary-phase integration-by-parts proof is pending. |
| `K_homogeneous` | `lem:K-homogeneous` | `paper.tex L3447-L3491` | Two-dimensional TT* estimate pending. |
| `Tbeta_kernel` | `lem:Tbeta-kernel` | `paper.tex L3352-L3433` | Gaussian/Fresnel kernel realization pending. |
| `XY_multiplier` | `lem:XY-multiplier` | — | Mixed Hölder plus infimal-decomposition proof pending. |
| `linear_carleman` | `prop:linear-carleman` | `paper.tex L3503-L3547` | Explicit inverse mapping estimates pending. |
| `spatial_mollification_source` | `lem:spatial-mollification-source` | — | Approximate-identity convergence in the sum space pending. |
| `compact_support_ODE` | `lem:compact-support-ODE` | — | The conclusion is now almost everywhere, matching the weak hypothesis; weak FTC and the support endpoint limit are pending. |
| `parameterwise_distribution_ODE` | `lem:parameterwise-distribution-ODE` | `paper.tex L3581-L3643` | Countable test-family slicing pending. |
| `fourier_section_identification` | `lem:fourier-section-identification` | `paper.tex L3689-L3720` | Spatial Fourier section and scalar ODE assembly pending. |
| `carleman_closure` | `lem:carleman-closure` | `paper.tex L3732-L3779` | Graph-class mollification limit pending. |
| `exponential_separation` | `lem:exponential-separation` | — | Absorption and weighted-error limit pending. |
| `halfspace_UC` | `thm:halfspace-UC` | `paper.tex L4051-L4079` | Iterated interface propagation pending. |

## Replaced/proved in this pass

- `moment_error` is fully proved.  The proof retains the necessary linear
  moment and establishes
  `|y₁| exp (β y₁) ≤ (h+1) exp (-β h)` for `β ≥ 1` on `y₁ ≤ -h`,
  then bounds the weighted source in `L¹_tL²_x` and squeezes the
  `carlemanXNorm` to zero.  Its former over-broad compact-support hypothesis
  was corrected to the two properties actually used: `‖η‖∞ ≤ 1` and
  integrability of `η'`; both are proved for the explicit cutoff.
- The explicit one-step profile now has disjoint transitions and the compiled
  scale estimate `∫ |ω''| ≤ 6 B₂ / δ`.  This yields the exact
  `L¹_tL∞_x` near-acceleration bound, the effective-potential `Y` bound,
  and a positive universal displacement constant for every positive
  one-slab threshold.
- Moving spatial translations and the unimodular Galilean phase are proved to
  preserve every spatial section norm, scalar mixed norm, spacetime `Lᵖ`
  norm, and `carlemanXprimeNorm`.  Thus the old Galilean axiom has been
  narrowed to the distributional weak-equation identity alone.
- The complete post-localization one-step argument is proved as
  `one_step_propagation_of_localized_equation`: bounded time support,
  half-space support, potential smallness, weighted cutoff-error decay,
  one-slab separation, and the measure-preserving pullback to the central
  interval are all assembled.  Its only additional premise is the explicit
  global weak equation produced by multiplying the Galilean equation by the
  time cutoff.

- `scalar_mixed_minkowski` has been removed.  `EndpointMinkowski` proves the
  exact `L⁴_tL∞_x` inequality used by the endpoint argument from Tonelli,
  four-factor Hölder, the essential-supremum bound, and the Bochner
  norm-of-integral inequality.  The formerly bundled restriction estimate was
  already the proved theorem `scalarMixedENorm_indicator_le`.
- `hom_strichartz_four_top_of_schwartz` now proves the complete extension from
  a uniform endpoint estimate on Schwartz data to all `L²` data, including
  scalar mixed-norm completion and almost-everywhere identification.  The
  remaining `hom_strichartz` declaration is isolated to the Schwartz-data
  TT*/endpoint-norming step.
- The target no longer uses the `endpoint_bound` axiom.  The new modules
  `EndpointForcing`, `RetardedEndpoint`, and `EndpointControl` prove the exact
  endpoint information needed downstream from the mild equation.  The proof
  constructs jointly measurable representatives, identifies scalar and
  Bochner Duhamel integrals, proves compact-time integrability of the cubic
  forcing, and derives the almost-everywhere finite `L^∞_x` section norm and
  its real-valued `L^4_t` realization.  Its remaining analytic input is now
  explicitly visible as `hom_strichartz`.
- `joint_representative_L2_measurable` is fully proved by measurable simple
  approximation and product-space gluing.  The associated
  `coeFn_integral_L2_of_joint` bridge is also proved, so the representative of
  an `L²`-valued Bochner integral agrees almost everywhere with the scalar
  integral of a jointly measurable representative.
- Joint continuity of `(t,f) ↦ freeProp t f` is proved from strong continuity
  and unitarity, and is used to discharge every propagator measurability step
  in the endpoint construction.

- `lem:F-vanishing` is now fully proved.  The proof assembles the weak
  zero-extension equation, proves the required local `X'` bounds directly,
  obtains an integrable real majorant for the ridge potential, and applies a
  quantitative local propagation theorem around each requested time.  Normal
  reflection, the orthogonal coordinate change, and continuity of the bundled
  exterior product upgrade the resulting almost-everywhere statement to the
  exact time slice.
- The direct dependency on the black-box `halfspace_UC` axiom has been removed
  from the target path.  The proved theorem `halfspace_small_L1Linfty`
  iterates `one_step_propagation` at the scale
  `δ=(b-a)/(32N)`, proves the surviving middle interval and the divergent
  boundary displacement, and concludes zero almost everywhere there.
- `ridgePotential_majorant_compact` and
  `ridgePotential_small_symmetric_interval` prove the absolute-continuity
  step used by the propagation: the endpoint section norm supplies an
  integrable real majorant, whose integral over shrinking symmetric intervals
  tends to zero.
- `G_equation` and `Q_bounds` are no longer on the target dependency path.
  Their needed components are proved directly in `PhaseRetrieval.lean` from
  tensor-product `L²`/`L⁴` estimates, the normal-coordinate Haar scaling, and
  the endpoint section bound.

- `lem:interp-L8L4` is implemented from a pointwise spatial
  `L²`–`L∞` interpolation estimate followed by direct integration in time and
  the essential-supremum bound.  Joint measurability supplies the measurable
  section norms needed at all three exponents.
- `lem:mixed-subsequence-uniform` is implemented under the necessary
  sigma-finiteness and joint-measurability hypotheses.  A geometric-rate
  subsequence has summable mixed norms; finite-measure exhaustion and the
  `L^p`-to-`L^1` comparison make its endpoint section differences summable
  almost everywhere.
- `cor:halfspace-XY` is now the direct specialization of `halfspace_UC`.
  The local-potential interface was repaired to express genuine local
  membership in the full Carleman `Y` gauge on compact subintervals.
- The off-path `cor:linear-common-potential` scaffold declaration was removed.
  `NewWorkflow.txt` explicitly permits skipping this auxiliary corollary; its
  independently useful integral Grönwall lemma remains fully proved.
- The final phase propagation no longer assumes a separately packaged global
  flow.  A proved `global_solution_unique` theorem restricts global solutions
  to compact local-solution intervals, applies corrected interval-wise LWP
  uniqueness and mass conservation, and uses connectedness of `ℝ`.  Direct
  gauge rotation of a `GlobalSolution` supplies phase covariance, so the
  unused full-flow scaffold axiom was removed.
- `def:Hs-neg-pairing` is implemented as `hsNegPairing_bound` using Bochner
  integral norm control followed by the `L²` Hölder inequality.
- `lem:tensor-norm` is implemented by Tonelli factorization of the product
  `L²` norm.
- `cor:all-time-density` is implemented by a continuous bilinear
  `L² × L² → L¹` product map, continuity of `f ↦ |f|²`, and equality of
  continuous time curves from their almost-everywhere equality.
- `lem:Tbeta-symbol` is implemented by the selected-branch Fourier multiplier
  calculation.
- `lem:one-slab` is implemented as the direct specialization of
  `exponential_separation`.
- `lem:integral-gronwall` is implemented by factorial iteration on each compact
  forward interval and time reflection for the backward inequality. The proof
  formalizes the primitive-power identity for an `L¹` coefficient and passes
  to zero using `A(t)^n / n! → 0`.
- `lem:realpart-logform` is implemented by the explicit real-linear weighted
  density functional; boundedness of the Schwartz derivative supplies the
  required `L¹` integrability.
- `lem:mass-H1` is implemented from the stronger mass conservation theorem
  `mass_L2`, which already applies to every local mild solution.
- `lem:current-locality` is implemented by bundling `hsNegPairing` as a
  continuous bilinear map and composing the derivative, multiplier, and
  conjugation maps.
- `lem:C0-limit-identification` is implemented by preserving continuity and
  both vanishing tails under uniform convergence, then identifying the limit
  almost everywhere through an `L²`-convergent subsequence.
- `lem:complex-gaussian-kernel` is implemented from Mathlib's pinned
  `fourierIntegral_gaussian`, with the right-half-plane principal-logarithm
  calculation converting its complex power into the blueprint's square-root
  normalization.
- `lem:dispersive-1d` is implemented from the exact constant modulus of
  `freeKernel`, the Bochner integral norm bound, and the `eLpNorm` identity at
  exponent one.
- `thm:fourier-gagliardo` is implemented from `gagliardo_density`, Plancherel,
  and the elementary comparison of `(1+ξ²)^s` with `1+|ξ|^(2s)` for
  `0 < s < 1`, with explicit constants `1/2` and `1`.
- `lem:three-lines-explicit` is implemented by adapting Mathlib's pinned
  Hadamard three-lines theorem to the project's `ENNReal` boundary suprema.
- `lem:HLS-time` is implemented from `hedberg` and `maximal_strongp`. Raising
  the pointwise Hedberg estimate in extended `L^q`, with
  `θ = p.toReal / q.toReal`, turns the maximal-function factor into its
  `L^p` norm; the remaining powers combine to one copy of `‖F‖_p`.
- `lem:homogeneous-smoothing-identity` is implemented from the exact
  change of variables `w = ξ²` on each frequency half-line.  The proof
  establishes quasi-measure-preservation of the square-root pullback,
  integrates the singular `w⁻¹ᐟ²` weight against the Jacobian, and combines
  the two branches with Plancherel to obtain the uniform constant `√8`.
  `lem:point-smoothing` then follows from the inverse Fourier linear isometry
  and the exact `toLp` extended-norm identity.
- `lem:H1-C0` is implemented from its exact weak fundamental-theorem
  hypothesis.  The proof builds the canonical continuous representative,
  applies the absolutely continuous chain rule to `x ↦ ‖f x‖²`, proves both
  limits vanish using global integrability, and obtains the sharp constant
  `2` from the `L² × L² → L¹` Hölder bound.
- `lem:translation-dq` is implemented by conjugating the bounded symbols
  `2πiξ / √(1+ξ²)` and `h⁻¹(exp(2πihξ)-1) / √(1+ξ²)` through the `L²` Fourier
  transform.  Their norms are uniformly bounded by `2π`, and dominated
  convergence proves strong convergence of the quotient multiplier to the
  derivative multiplier.  A density argument proves the exact Fourier law for
  `L²` translations, while the positive and negative half-Bessel transforms
  identify both constructed coordinates with the required tempered
  distributions.
- `lem:Teps` is implemented by rewriting the complex regularizer as the real
  radial map `z ↦ ε / (‖z‖² + ε) • z`.  An explicit Fréchet-derivative
  calculation proves its operator norm is at most one; the scalar maximum
  gives `‖Teps ε z‖ ≤ √ε / 2`, and `lipschitz_composition` supplies the stated
  `H^{1/2}` representative.
- `lem:propagator-unitary` is implemented in full.  The multiplier group law
  gives the propagator law and identity, dominated convergence gives strong
  `L²` continuity, and a second dominated-convergence argument differentiates
  the multiplier on frequency-weighted data.  Mathlib's Schwartz Fourier
  derivative identity then identifies that derivative with
  `i · freeProp t (φ'')`; norm preservation was already supplied by the
  unit-modulus multiplier proof.
- `lem:measurable-esssup-section` is now a theorem under the necessary
  `[SFinite μx]` hypothesis.  Its proof rewrites strict essential-supremum
  superlevel sets as positivity of measurable section measures and applies
  Mathlib's product-section measurability theorem.
- The formerly vacuous interfaces for `thm:inhom-str`, `cor:hom-smoothing`,
  `prop:forced-smoothing`, `cor:NLS-smoothing`,
  `lem:mollification-critical-uniform`, and
  `lem:quadratic-form-extension` have been strengthened and returned to the
  temporary-axiom ledger.  Their witnesses are now tied respectively to the
  retarded Bochner integral, the physical cutoff solution, genuinely smooth
  compactly supported approximants, and the defining quadratic pairing.
- `HigherFixedPointData` now identifies each entry with the corresponding
  iterated distributional spatial derivative.  The previous constant-slot
  inhabitant is therefore unavailable, and `prop:Hk-persistence` is again an
  honest temporary axiom pending the induction from the paper.
- `lem:Hilbert-wedge` is implemented as the axiom-free theorem `hilbert_wedge`.
  The proof slices the product-a.e. exterior-product identity, chooses a nonzero
  section, obtains the scalar pointwise, and uses equality of L² norms to prove
  unimodularity.
- `cor:density-equal-current`, `thm:critical-wronskian`, and
  `thm:local-H2-characterization` are proved from their immediately preceding core lemmas.
- `prop:Dirichlet-trace` is proved directly from antisymmetry.
- `thm:main` and `cor:interval-version` are proved from `lem:F-vanishing`, the
  axiom-free Hilbert wedge lemma, and the global flow interface.

## Statement-faithfulness repairs

The counterexamples and vacuous-witness defects identified during the audit
have been closed at the declaration level:

- `measurable_esssup_section` requires an `SFinite` spatial measure and is now
  proved.
- `vandercorput_kernel` uses a real-valued phase.
- `neumann_localization` requires the translated Schwartz test to have compact
  support.
- `cubic_Hk_leibniz` assumes the lower derivatives lie in the fixed-point mixed
  spaces used by the product estimate.
- `gelfand_chain_rule` states the compatibility between the Hilbert embedding
  and the natural real-bilinear dual pairing.
- `compact_support_ODE` concludes its representation formula almost
  everywhere.
- `joint_representative_L2` assumes the path is strongly measurable, and
  `distributional_products` assumes genuine `MemScalarMixed` membership.
- Local smoothing witnesses represent the actual cutoff solutions;
  `inhom_strichartz` is tied to the completion of displayed retarded Bochner integrals;
  mollification produces smooth compactly supported representatives; the
  quadratic extension agrees with its defining pairing; and higher fixed-point
  slots are the actual iterated distributional derivatives.

These repairs deliberately increase the temporary-axiom count where an old
proof had only exploited a weak conclusion.  No counterexample or unrelated
zero/constant witness listed by this audit remains applicable to the current
declarations.

## Verification log

- `lake env lean FoundationChecks.lean` — succeeded.
- `lake build` on the pinned empty library — succeeded.
- `lake build` on the complete Step 3 header-only module graph — succeeded
  (8,674 jobs).
- `lake env lean Lean_Code/DensityCurrent.lean` — succeeded after scaffolding
  Modules 6–9.
- `lake env lean Lean_Code/DensityCurrent.lean` — succeeded after replacing
  `cor:all-time-density`; the project contains 103 temporary axioms.
- `lake env lean Lean_Code/PhaseRetrieval.lean` — succeeded after replacing
  `lem:integral-gronwall`; the project contains 102 temporary axioms.
- `lake build` on all 16 implemented modules — succeeded (8,674 jobs).
- `lake env lean showcase.lean` — succeeded with no `sorry`; current target
  axiom audit is the standard three plus `F_vanishing` and `global_wellposedness`.
- `lake build` after the latest six replacements — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that full build — succeeded; both showcase
  theorems depend on exactly `propext`, `Classical.choice`, `Quot.sound`,
  `F_vanishing`, and `global_wellposedness`.
- `lake env lean Lean_Code/CriticalQuadraticForms.lean` after replacing
  `Teps_properties` — succeeded; 86 project axioms remain.
- `lake build` after replacing `Teps_properties` — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that build — succeeded; the showcase
  dependency set remains exactly the standard three plus `F_vanishing` and
  `global_wellposedness`.
- A token scan of all Lean sources found no `sorry` or tactic `admit`; the only
  textual match is the English verb “admit” in a documentation comment.
- `lake env lean Lean_Code/FourierSobolev.lean` after replacing `H1_C0` —
  succeeded.
- `lake build` after replacing `H1_C0` — succeeded (8,674 jobs), and
  `lake env lean showcase.lean` retained the same exact five-axiom footprint.
- `lake env lean Lean_Code/FreeSchrodinger.lean` after replacing
  `propagator_unitary` — succeeded.
- `lake build` after replacing `propagator_unitary` — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that build — succeeded; both showcase
  theorems still depend on exactly `propext`, `Classical.choice`, `Quot.sound`,
  `F_vanishing`, and `global_wellposedness`.
- `lake env lean Lean_Code/FourierSobolev.lean` after replacing
  `translation_dq` — succeeded.
- `lake build` after replacing `translation_dq` — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that build — succeeded; both showcase
  theorems still depend on exactly `propext`, `Classical.choice`, `Quot.sound`,
  `F_vanishing`, and `global_wellposedness`.
- `lake env lean Lean_Code/FractionalIntegration.lean` after replacing
  `HLS_time` — succeeded; 83 project axioms remain.
- `lake build` after replacing `HLS_time` — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that build — succeeded; both showcase
  theorems still depend on exactly `propext`, `Classical.choice`, `Quot.sound`,
  `F_vanishing`, and `global_wellposedness`.
- `lake env lean Lean_Code/LocalSmoothing1D.lean` after replacing
  `homogeneous_smoothing_identity` and `point_smoothing` — succeeded.
- `lake build` after those two replacements — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that build — succeeded; both showcase
  theorems still depend on exactly `propext`, `Classical.choice`, `Quot.sound`,
  `F_vanishing`, and `global_wellposedness`.
- `lake env lean Lean_Code/EndpointRegularity.lean` after replacing
  `Hk_persistence` — succeeded.
- `lake build` after replacing `Hk_persistence` — succeeded (8,674 jobs).
- `lake env lean showcase.lean` after that build — succeeded; both showcase
  theorems still depend on exactly `propext`, `Classical.choice`, `Quot.sound`,
  `F_vanishing`, and `global_wellposedness`.
- The later statement-faithfulness audit showed that the axiom-free
  `Hk_persistence` inhabitant used unrelated derivative slots.  After
  `HigherFixedPointData` was repaired, `Hk_persistence` returned to the
  temporary-axiom ledger.
- `lake env lean Lean_Code/ScalarMixedNorms.lean` after proving
  `measurable_esssup_section` under `[SFinite μx]` — succeeded.
- `lake env lean` succeeded independently for every module whose false
  declaration was repaired: `EndpointRegularity`, `CubicFlow`,
  `ScalarMixedNorms`, `Utilities`, `DiagonalTrace`, and `Carleman2D`.
- `lake build` after those eight counterexample-driven declaration repairs —
  succeeded (8,674 jobs).
- `lake env lean` succeeded independently for `Strichartz1D`,
  `LocalSmoothing1D`, and `CriticalQuadraticForms` after replacing all six
  vacuous zero/constant-witness interfaces with faithful temporary axioms.
- Final `lake build` after all statement-faithfulness repairs — succeeded
  (8,674 jobs).
- Final `lake env lean showcase.lean` — succeeded; both showcase theorems still
  depend on exactly `propext`, `Classical.choice`, `Quot.sound`, `F_vanishing`,
  and `global_wellposedness`.
- `lake env lean Lean_Code/EndpointRegularity.lean` after replacing
  `interp_L8L4` — succeeded.
- `lake build` and `lake env lean showcase.lean` after that replacement —
  succeeded; the showcase dependency set is unchanged.
- `lake env lean Lean_Code/ScalarMixedNorms.lean` after replacing
  `mixed_subsequence_uniform` — succeeded.
- `lake env lean Lean_Code/HalfspacePropagation.lean` and downstream
  `PhaseRetrieval.lean` after replacing `halfspace_XY` — succeeded.
- The current source-level project-axiom count is 81, matching the 81 rows in
  the temporary-axiom table.
