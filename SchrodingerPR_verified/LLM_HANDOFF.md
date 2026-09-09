# Lean verification handoff

## Objective

Prove the fixed `showcase.lean` theorem without project axioms or `sorry`.
Do not edit `showcase.lean`; its SHA-256 is
`e962e355193f718217b227c002ee389b14a8cd001d100f224bcb25fded025500`.

## Current verified state

Both commands succeed:

```sh
lake build CubicNLSPhaseRetrieval
lake env lean showcase.lean
```

There are no `sorry`/`admit` terms in the Lean sources. The showcase audit has
exactly three remaining project axioms:

1. `CubicNLSPhaseRetrieval.TTstar_endpoint`
2. `CubicNLSPhaseRetrieval.carleman_closure`
3. `CubicNLSPhaseRetrieval.zero_extension_jump`

The allowed foundational dependencies are `propext`, `Classical.choice`, and
`Quot.sound`.

## Recent work

`Lean_Code/EndpointCompleteness.lean` now contains a compiled, axiom-free
telescoping proof of scalar `L^p_t L^infinity_x` sequential completeness.
`Lean_Code/ScalarMixedNorms.lean` no longer declares
`scalar_endpoint_complete` as an axiom, and `Strichartz1D.lean` imports and uses
the proved theorem.

The separate mathematical supplement supplied during the working session is
not part of this source checkout.

## Important interface observations

- The supplement's zero-extension calculation starts from local normal
  derivatives and established Dirichlet/Neumann traces. The Lean theorem
  `zero_extension_jump` receives only global solutions and an equal-modulus
  premise, so a proof must also derive those trace hypotheses.
- The supplement's Carleman graph-closure paragraph uses weighted
  `L^infinity_t L^2_x` graph-class control. Check carefully how that control is
  obtained from the current `IsWeakSchrodinger2D` interface; the latter records
  distributional pairings but does not directly contain the graph norm.
- Replacing a frontier axiom by a theorem that calls another project axiom is
  not sufficient: verify the final result with `#print axioms`.
