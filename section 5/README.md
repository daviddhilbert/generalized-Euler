# Section 5 · Generalized Euler characteristic

Run `lake build` in this folder and import `Section5`. The package uses the same Lean toolchain and pinned Mathlib as Section 4.

| Manuscript | Lean coverage |
| --- | --- |
| 5.1–5.4 | `UnaryPreparation` and `FiniteCenters` construct regularization and the finite sequence of centripetal transformations. The labels retain every previous leading term. Their inverse fibers are open discs or singletons. `FixedBaseCenters`, `PreparationGraph`, and `UnaryDeformation` obtain one finite list of centers in the VF sort of the original base, define the graph over both sorts of that base, and prove the pullback assertion for the whole RV-parameter family. The model-theoretic inputs are saturation for the indicated tuple and the immediate-isomorphism criterion from Section 3. |
| 5.5, induction | `VerticalCenters` and `UniformVerticalPreparation` choose one finite list of center terms for all complementary field tuples and auxiliary RV values. `HeadPreparation` shows that the leading terms of the pairwise center differences determine the possible histories. `DescendedVerticalGraph` defines the graph after dropping the prepared field coordinate. `VerticalSuccessor` checks the image and injectivity of the combined head and tail maps. The complete field-arity induction still needs to be assembled. |
| 5.6 and 5.8, one field coordinate | `UnaryFunctions` prepares all RV outputs of a definable graph at once. `UnaryLifting` proves that the prepared image of a set with finite RV fibers is the union of the lifts of two fixed-base Section 4 objects. It pads the degree-zero lift by zero and uses the nonzero leading term as the degree-one structure map. |
| 5.12 | `LiftBoundary` proves the pair of inverse identities after the two RV boundary exclusions. `RestoreCoordinates` proves the coordinatewise lifting equivalence after choosing the missing representatives over the retained field tuples. The dimension induction and the uniform definable choices still need to be assembled. |
| 5.27 and 5.34–5.35 | `UnaryBlowup` checks the equivalence for a chosen unary focus, with both the infinitesimal nonzero multipliers and the zero multiplier. The zero multiplier corresponds to the zero translated field coordinate. |

The higher-dimensional preparation, general blowup comparison, and integration theorems are in progress.
