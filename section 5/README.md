# Section 5 · Generalized Euler characteristic

Run `lake build` in this folder and import `Section5`. The package uses the same Lean toolchain and pinned Mathlib as Section 4.

| Manuscript | Lean coverage |
| --- | --- |
| 5.1–5.4, R022 | `UnaryPreparation` and `FiniteCenters` construct regularization and the finite sequence of centripetal transformations. The labels retain every previous leading term. Their inverse fibers are open discs or singletons. `FixedBaseCenters`, `PreparationGraph`, and `UnaryDeformation` obtain one finite list of centers in the VF sort of the original base, define the graph over both sorts of that base, and prove the pullback assertion for the whole RV-parameter family. The model-theoretic inputs are saturation for the indicated tuple and the immediate-isomorphism criterion from Section 3. |
| 5.12, R023 | `LiftBoundary` proves the pair of inverse identities after the two RV boundary exclusions. `RestoreCoordinates` proves the coordinatewise lifting equivalence after choosing the missing representatives over the retained field tuples. The dimension induction and the uniform definable choices still need to be assembled. |
| 5.27 and 5.34–5.35 | `UnaryBlowup` checks the equivalence for a chosen unary focus, with both the infinitesimal nonzero multipliers and the zero multiplier. The zero multiplier corresponds to the zero translated field coordinate. |

The higher-dimensional preparation, general blowup comparison, and integration theorems are in progress.
