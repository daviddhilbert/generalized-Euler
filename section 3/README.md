# Section 3 · Definable sets in VF

Run `lake build` in this folder. Import `Section3` to use its declarations.
Lake uses the sibling Section 2 package and its pinned Mathlib revision.
The ordinary base is a fixed two-sorted substructure. Results involving extra
disc codes specify the extra parameter family. As in Section 2, valued-field
discs use Mathlib's multiplicative valuation, so a smaller radius denotes a
smaller disc.

## Proof coverage

The table describes the current Lean declarations and their mathematical inputs.
A proof step listed below can be used without assuming the rest of its manuscript lemma.

| Manuscript | Module | Verified statement and inputs |
| --- | --- | --- |
| 3.1 | `TopTerms` | Quantifier-free truth is determined by the RV assignment and the leading terms of one finite set of VF expressions. VF expressions ignore the RV variables. The theorem takes encodings of the primitive VF atoms. |
| 3.3, 3.6–3.7 | `DefinableFunctions`, `DefinablePoints` | A graph isolated by its top terms takes values among discontinuities and boundaries of zero sets. The resulting finite-image bound is uniform over the auxiliary inputs when the unary critical sets are finite. Section 2 immediate movers put each definable VF point into the base even with arbitrary RV parameters. |
| 3.8, 3.19–3.20 | `DefinablePoints` | Exchange eliminates a disc parameter when its centers cannot all belong to one small closure. Sorted QE and Section 2 RV closure put a definable RV point into the same base. For a closed disc, realization of the small value cut constructs an outside point matching *every* old translate. Invariance under those matches forces a base point in the disc. |
| 3.9–3.15, 3.18, 3.22 | `Atomicity`, `AtomicParameters`, `ConvexCuts`, `AtomicDiscs` | Complete type loci, definable images, atomicity from transitive parameter-fixing automorphisms, canonical codes for value fibers, and the intersecting-slices argument. A per-formula two-sided germ transfers from one point to the atom and a common saturation bound works for all formulas. An infinite family of discs of a fixed radius admits an atomic member given HNF and realization of the finitely satisfiable label tests. Recentring recovers its code. |
| 3.23 | `DiscMaps`, `ClosedDiscImages` | Both directions of the open-disc definition. For the corrected converse the input on the definable value-group graph is its last affine branch (van den Dries, Theorem B). Strict increase follows from injectivity, and the proof identifies the open image at the finite endpoint in both directions. The gap example verifies the need for the inverse hypothesis. |
| 3.25–3.28 | `Contraction`, `ConvexCuts`, `BoundaryInduction`, `ExceptionalLabels` | Empty RV-boundary characterizes pullbacks. Contraction exists uniquely exactly when output labels are constant on fibers. The unary boundary is finite under HNF. A mixed product fiber has a mixed coordinate section. Given splitting witnesses and the boundary bound, adjoining all zero-coordinate labels preserves the strict dimension estimate. Arity zero is treated directly. |
| 3.30–3.32 | `ResidueDerivatives`, `Contraction`, `BoundaryInduction` | Integrality in the normalized mean-value calculation, the reduced secant identity, the limit giving the order derivative, finite fibers of the exceptional interior, and the absence of interior for a set with finite last-coordinate fibers. Once the jet identities hold on a common good label, evaluating a differential polynomial commutes with reduction. |
| 3.34 | `AffineLine` | Equal profiles at two origins give a translation conjugate to a dilation. In fact the affine map must be a translation because a nontrivial dilation cannot have a fixed point on the ray. Common profiles give an injective exponential. Eventual monotonicity of its normalized ratio, as supplied by the derivative calculation, contradicts any proposed power bound. |
| 3.35–3.36 | `AffineSlopes` | Uniqueness of the RV slope on a set with two distinct points, passage to the value shift, the mean-value step for a field branch with constant nonzero leading derivative, and identification of the shift from surjectivity onto the target disc. |

## Remaining integrations

The section is in progress. In particular, the higher-dimensional boundary
bound in 3.26, the cell and type arguments giving the unary taxonomy and the
atomic open-disc image theorem, and the relative disc-imaginary interpretation
still require integration. The present generic mean-value and jet calculations
do not yet construct the common definable good locus from the hypotheses of
3.31. Regularity and the orientation transfer also require their full statements.
