# Section 2 · Basic results in T-convex valued fields

Lean 4 formalization of the reviewed manuscript. Run the following commands from this directory.

```sh
lake exe cache get
lake build
```

The package uses the Lean and Mathlib revisions pinned by the related ACVF
projects. Import `Section2` for the public declarations.

| Manuscript | Lean modules | Checked content |
| --- | --- | --- |
| Convention 2.1 and Definition 2.2 | `PowerBounded`, `SortedModelTheory` | Definability over a specified set of parameters, o-minimality, and power boundedness. Full parameter sets give the convention of §2.1. |
| §2.2 | `Language`, `LeadingTerm`, `LeadingTermOrder`, `Residue`, `ResidueOrder`, `SortedStructure` | The two sorts and typed symbols, the canonical RV quotient and signed order, the unsigned valuation, and the residue field with its operations extended by zero. |
| §2.2, Ax. 8–10 | `LeadingTermPower`, `PowerOrder`, `RVVectorSpace` | The clamping proof of descent and uniqueness for the whole power family. Algebraic and ordered power laws on the positive branch. The exponent-field action, linear unsigned value map, and identification of its kernel with positive residues. |
| Theorem 2.11 and Proposition 2.13 | `ConvexLanguage`, `LeadingTermMap`, `LeadingTermPresentation`, `ResidueMap`, `ResidueInterpretation`, `CanonicalEmbedding`, `CanonicalModel`, `PresentedExpansion` | The residue compatibility and unit test give the kernel of the presented RV quotient. Reduction fixes the continuous residue primitives and their definitions fix the remaining operations. The quotient identification, residue compatibility, and power axioms give an isomorphism of the full sorted signatures over the field. |
| Theorem 2.14 and the VF definability corollary | `QuotientInterpretation`, `ValuedFieldFormulas`, `ResidueInterpretation` | Uniform interpretation of the canonical signature from the defining graphs in the continuous residue language and the field graphs of the named powers. Ax. 8 gives reduction of the continuous primitives. The translation restricts residue quantifiers to the valuation ring, interprets the order and operations, and transfers completeness to isomorphic presentations and definability over parameter representatives. |
| §2.3, Theorem 2.16 and Lemmas 2.20–2.22 | `SortedModelTheory`, `TaggedTheory`, `SortedTypes`, `SortedQE`, `GeneratedSubstructure`, `PrescribedLift`, `TrivialBaseLift`, `ImmediateExtension`, `VFLiftSubstructure`, `RVAgreement`, `ConvexRingComparison`, `DirectedSubstructure` | The substructure form of the Shoenfield criterion, comparison of convex rings using the old cut, and preservation of the test for an old unsigned value. Directed unions glue compatible embeddings. A common-lift step over the fixed RV sort gives a VF-generated enlargement. Partial elementarity on such enlargements then gives the generated-embedding criterion for sorted QE. The two field extension properties give an immediate automorphism. |
| §2.3, one-generator extensions | `FieldReduct`, `FieldGeneratedEmbedding`, `FieldTypeLift`, `TrivialBaseLift`, `ConvexRingComparison`, `RVVectorSpace`, `RVAgreement` | Matching cuts give a field-language embedding from the same unary cell descriptions. Sorted embeddings restrict to the valued-field language on VF. Valued-field QE and the one-point saturation hypothesis give extensions that preserve equality with the named leading terms. The coarsening map is linear for common field powers. Relative value rank at most one gives the span by a new value and the resulting criterion for equality of the rings. When values stay unchanged, agreement on the residue generators propagates to all intermediate leading terms. Over a trivial base, the new-value calculation handles either side of one, and a new residue leaves the generated field trivially valued under the valuation property. |
| §2.4, Definition 2.25, Lemma 2.26, Remark 2.27 and Lemma 2.28 | `WeakOminimal`, `Dimension`, `DefinableCharts`, `DimensionLower`, `ValueFiberTopology` | Projection dimension, the maximal fiber-rank calculation, and preservation of dimension on a signed value fiber. A finite definable chart cover gives a fixed-base definable injection with distinct RV numeral tags. Compactness extracts a finite cover from chart formulas that cover in all pointed models. An injective definable graph isolates each input over its image, giving the lower bound from exchange rank and the no-new-VF-points property. |
| §2.4, Remark 2.27 | `SortedDefinability`, `RVReduct` | Fixed-base Boolean operations and projection. After QE, formulas on RV tuples reduce to RV formulas using only parameters already in the base RV sort. |
| §2.4, Lemmas 2.23 and 2.29 | `ValueSplitting`, `SeparatedSets`, `AffinePullback`, `ResidueFiber`, `RVMonomials` | A fixed-base linear section and product coordinates with lexicographic order on positive RV. Finite unions of rectangles are closed under Boolean operations, coordinate projections, and pullbacks along separate coordinate maps. A functional separated graph has finite image. The affine equivalence on given pieces uses definable monomial division with intercepts from the same base. |
| §2.4, Remark 2.30 and Theorem 2.31 | `ResidueFiber`, `DefinableResidueCharts`, `RVDefinableEquivalence`, `ResidueClassification` | A finite set of value fibers gives a definable bijection onto labeled residue tuples, including zero coordinates. Projection gives definability of the image, and inverse and composition of RV graphs transport bijections. With the induced residue structure and the cited classification of residue normal forms, the criterion transfers to the original RV sets. |
| §2.4, Definitions 2.32 and 2.36 and Notation 2.34 | `ValuativeDisc`, `HigherLeadingTerm`, `TorsorDerivative` | The higher leading-term quotients and their fibers. Maximality of the open children and the residue chart on their quotient, including its order, affine chart changes, and the entire central class. Uniqueness of derivatives and invariance of the normalized derivative under affine changes of charts. |
| §2.4, valuative intervals and Holly normal form | `ValuativeInterval`, `HollyNormalForm`, `DefinableHolly` | Boolean closure of finite unions of valuative intervals. The representative interpretation gives definability of unary VF sets in the valued-field language. A unary Boolean description gives the unique interval decomposition, and naming a point in each component makes it definable. |

The unsigned value uses Mathlib's multiplicative valuation convention, with
values below one on the maximal ideal. Its order is dual to the manuscript's
additive convention.

## Cited hypotheses

The Lean declarations take cited mathematical inputs as explicit hypotheses.
`ConvexTheoryFacts` records van den Dries–Lewenberg (1995), Theorem 3.10 and
Corollary 3.13. `WeakImmediacyTransfer` and `LeadingTermMonomialTransfer`
record the uses of Freni's thesis, Proposition 3.3.11 (Tyne) and Corollary
3.3.13, for the specified one-generator extension.
`vfDimension_eq_max_fiber_rank` and `signedValue_fiber_dimension` use the
projection-versus-rank comparison and maximal-dimensional charts from
Macpherson, Marker, and Steinhorn (2000), Theorems 4.12 and 4.11, respectively.
The relative finrank hypothesis in
`span_base_and_new_value_of_relative_finrank_le_one` is the value-space
part of van den Dries (1997), Corollary 5.6.
`HasInducedResidueDefinability` records van den Dries (1997), Theorem A.
`rvDefinablyEquivalent_iff_of_residue_classification` takes the
classification of the residue normal forms from van den Dries (1998),
§8.2.11 as a hypothesis.

The canonical interpretation takes the continuous functional presentation
and uniform defining graphs as inputs. The isomorphism with a presentation
uses the residue compatibility, order, and power conditions in Definition 2.9.
The field-specific extension steps for two-sorted QE and the remaining
definability and dimension arguments in §2.4 are still in progress.
The lower-bound proof in Lemma 2.26 takes the
forward use of the no-new-VF-points property from §3 as a premise. Obtaining
the uniform chart cover from the dimension theorem still needs to be connected
to that proof. For Lemma 2.29 the remaining steps are separating all auxiliary
formulas and choosing the finite definable partition over the fixed base.
For Theorem 2.31 the transport is checked with the invariants of the residue
normal forms. Their identification with the manuscript's dimension and
Euler characteristic still needs to be checked. For Holly normal form the
unary Boolean description is a premise, and fixed-base definability of the
end-discs is still pending.
