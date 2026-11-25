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
| Remark 2.3 | `ContinuousDefinitions` | Definable completeness gives a continuous distance to each nonempty definable set in finite field coordinates. Its zero set is the closure. Given a cell decomposition over the original base, each locally closed piece is a difference of two such zero sets. This gives a quantifier-free description over the empty base in the language of parameter-free continuous functions. Continuity rules out a universal QE presentation in this language when inverse is definable. Compactness would force finitely many unary terms to give inverse, and all those terms stay bounded near zero. |
| §2.2 | `Language`, `LeadingTerm`, `LeadingTermOrder`, `Residue`, `ResidueOrder`, `SortedStructure` | The two sorts and typed symbols, the canonical RV quotient and signed order, the unsigned valuation, and the residue field with its operations extended by zero. |
| §2.2, signed value group | `SignedValue`, `RVMonomials` | Signed values form the product of the sign group and the unsigned value group, with zero adjoined. The signed valuation has the quotient order induced by convex field fibers. The kernel on RV is the positive residue group. Quotienting by the unit signs recovers the unsigned value group. Quantifier-free RV formulas define equality and strict order of the represented signed values. |
| §2.2, Ax. 8–10 | `LeadingTermPower`, `PowerOrder`, `RVVectorSpace` | The clamping proof of descent and uniqueness for the whole power family. Algebraic and ordered power laws on the positive branch. The exponent-field action, linear unsigned value map, and identification of its kernel with positive residues. |
| Example 2.8 | `HahnExample` | The RV class of a Hahn series is determined by its leading exponent and coefficient. Every coordinate pair has a monomial representative. Constant coefficient identifies the residue field with the reals, and the valuation ring is the convex hull of the constant real series. The quotient order has the stated sign-dependent lexicographic formula. Rational field powers give the named RV powers on positive monomials. The signed valuation is multiplicative, with kernel the positive constant classes and range the signed rational exponentials on nonzero inputs. The analytic elementary embedding and residue compatibility give the canonical T-convex expansion. |
| Theorem 2.11 and Proposition 2.13 | `ConvexLanguage`, `LeadingTermMap`, `LeadingTermPresentation`, `ResidueMap`, `ResidueInterpretation`, `CanonicalEmbedding`, `CanonicalModel`, `PresentedExpansion` | The residue compatibility and unit test give the kernel of the presented RV quotient. Reduction fixes the continuous residue primitives and their definitions fix the remaining operations. The quotient identification, residue compatibility, and power axioms give an isomorphism of the full sorted signatures over the field. Elementary field embeddings preserve powers given by uniform field formulas. The induced ordered residue map and the reflected equality of values are checked. Compatible residue sections make the induced residue map an embedding in the full language. |
| Theorem 2.14 and the VF definability corollary | `QuotientInterpretation`, `ValuedFieldFormulas`, `ResidueInterpretation`, `RecoveredValuedField`, `InterpretedValuedTheory` | Uniform interpretation of the canonical signature from the defining graphs in the continuous residue language and the field graphs of the named powers. Ax. 8 gives reduction of the continuous primitives. The translation restricts residue quantifiers to the valuation ring, interprets the order and operations, and transfers completeness to isomorphic presentations and definability over parameter representatives. The signed ring test recovers the valued-field reduct. A first-order axiom scheme characterizes the uniform quotient interpretation, with completeness transferred from the recovered theory. Two realizations of the same interpreting formulas on the same field are canonically isomorphic. |
| §2.3, Theorem 2.16 and Lemmas 2.20–2.22 | `SortedQE`, `InterpretedValuedQE`, `CanonicalQuantifierElimination`, `TransportLift`, `PrescribedLift`, `TrivialBaseLift`, `ImmediateExtension`, `ConvexRingComparison`, `DirectedSubstructure`, `ImmediateAdjunction`, `ImmediateIdentity`, `ImmediateBackAndForth`, `SmallBackAndForth`, `SmallImmediateAdjunction`, `ImmediateTranslate`, `ImmediateFieldLift`, `ImmediateTranslateLift` | A common-lift step over the fixed RV sort gives a VF-generated enlargement for the Shoenfield criterion. On the interpreted theory, the quantifier-free ring test recovers a valued-field embedding and the common representatives give full partial elementarity. The representative step transports across sorted isomorphisms. The compactness proof gives QE from canonical model presentations and the residue and rank inputs on the generated field. The same iteration followed by restriction to the field generated by the selected representatives gives the first stage of Lemma 2.20. Valued-field QE and saturation over that field give the second stage and the fixed-RV field extension. Naming all RV by identity and reversing lifts on their images give both directions of the automorphism construction. The initial-ordinal iteration bounds each field domain by the maximum of the initial bound and the cardinality of the preceding stages, so saturation is used only below the ambient field cardinality. Matching translates determine the field cut. The new-value and weak-immediacy cases detect a new translate whenever the leading-term image changes. The fixed-RV lift at that translate sends the original point to the prescribed image. In the unchanged case, the two pullbacks have the same old value group and valuation ring. Restricting the lift to the two generated structures gives the immediate isomorphism. |
| Corollary 2.17 | `ElementaryGenerated` | The RV formula for a nonzero element of value different from one witnesses the forward implication by elementarity. From the natural residue embedding, the sorted substructure generated by field points has precisely the field-language closure and its leading terms. The reverse implication applies valued-field QE to the proper recovered pair to inherit the quotient interpretation, then uses sorted QE. |
| §2.3, one-generator extensions | `FieldReduct`, `FieldGeneratedEmbedding`, `FieldCellTransfer`, `FieldOperations`, `FieldTypeLift`, `TrivialBaseLift`, `ConvexRingComparison`, `RVVectorSpace`, `RVAgreement`, `ValueMonomials`, `RelativeValueSubspace`, `PrescribedValueComparison`, `FieldDefinableClosure`, `PrescribedRVStep`, `WilkieRVStep`, `AdjunctionPowers`, `WilkieInequality`, `TrivialAdjunctionRank`, `CommonValuedAdjunction`, `GeneratedRVAdjunction` | The old RV embedding supplies a representative with the same cut. Universality and field QE make the old field an elementary submodel. Its unary cells describe the same unary formula in both fields and give the specified field embedding. Named ordered-field terms give an ordered ring map. Their interpretation is inherited by field-language substructures through an ordered ring embedding. The target ring pulls back to the source ring in the cut-comparison cases. Valued-field QE and saturation give field lifts preserving equality with named leading terms. The old values form an exponent subspace. With relative value rank at most one, coarsening is injective if the chosen generator remains new. With unchanged residues, every nonzero leading term is a named power of the generator times an old field factor. The two pullbacks preserve the old-value decision and agree on the old ring. The normalized residue is new when the prescribed leading term is new and its value is old. In a universal field theory with QE, unique definability gives term generation. In a generated sorted substructure the VF carrier is exactly the field-language closure of the VF generators. The common field adjunction has the same pulled-back valuation ring by the value-rank comparison. The natural residue embeddings and uniform power graphs give the two canonical embeddings. Both Wilkie cases then give a fixed-RV extension that preserves the chosen field embedding. The named powers restrict to the generated field and its leading terms. A single bound on the sum of the relative ranks gives the two Wilkie alternatives. Negation reduces the representative step to positive representatives. |
| §2.4, Definition 2.25, Lemma 2.26, Remark 2.27 and Lemma 2.28 | `WeakOminimal`, `Dimension`, `DimensionWithBot`, `DefinableCharts`, `UniformCharts`, `DimensionFormulas`, `DimensionLower`, `FieldClosureUnderRV`, `ValueFiberTopology` | Projection and VF dimensions are minus infinity on the empty set and give the existing natural-number arity on nonempty sets. The maximal fiber-rank calculation, and preservation of dimension on a signed value fiber. Nonempty interior of a projection is expressed by an open-box formula, so a fiber-dimension bound is first order. The cited pointwise charts yield a finite definable chart cover by compactness and a fixed-base definable injection with distinct RV numeral tags. An injective definable graph isolates each input over its image. For the lower bound, a finitely satisfiable type yields a distinct field point with the same translated leading terms. The immediate-isomorphism and automorphism arguments then show that a uniquely definable tuple over arbitrary RV parameters has its field coordinates in the small field-language closure. Applying exchange rank gives the least-arity characterization. |
| §2.4, Remark 2.27 | `SortedDefinability`, `RVReduct`, `RVClosure` | Fixed-base Boolean operations and projection. After QE, formulas on RV tuples reduce to RV formulas using only parameters already in the base RV sort. The representative adjunction constructs the VF-generated enlargement with exactly the old RV sort. For the trivial case, Lean constructs the monomial extension of a trivial-value RV base, identifies the intersection of extensions by two independent values, and recovers a generator from a monomial with nonzero exponent. |
| Remark 2.27, exchange | `RVClosure`, `RVExchange`, `RVResidueClosure` | The two enlargements are RV substructures. Under the RV definable-closure hypothesis, every point definable from the new generator belongs to the corresponding enlargement. At a new value, division and an inverse exponent recover the positive monomial generator, and a signed unit recovers either sign. At an old value, dividing by an old representative gives the new residue, and residue exchange gives a term recovering the generator over the original RV base and the new point. |
| §2.4, Lemmas 2.23 and 2.29 | `RVSplitCoordinates`, `RVCoordinatePrimitives`, `RVFormulaSeparation`, `ValueResidueOrthogonality`, `AffineValueSelection`, `DefinableAffinePartitions`, `RVSignCharts` | Every canonical RV primitive separates over the two coordinate languages. Slicing gives value-language definitions and finite cross-sort images in both directions. A section taking old values to old leading terms keeps the normalized residues in the base. Lower-dimensional projection charts pad to the required arity. The cited affine graph decomposition refines those charts into definable pieces over the value base. Pulling the pieces back and dividing by their monomial lifts gives the positive-case trivialization. Quantifier-free sign tests define the sign pieces from the full pullback over the original base. Sign changes and tagged unions also preserve that base. |
| §2.4, Remark 2.30 and Theorem 2.31 | `ResidueFiber`, `DefinableResidueCharts`, `RVDefinableEquivalence`, `ResidueClassification`, `ResidueTopology`, `RVInvariants` | A finite set of value fibers gives a definable bijection onto labeled residue tuples, including zero coordinates. The positive and negative residue branches embed openly into RV. Every nonempty open projection meets the tuples with no zero coordinate, so the embedding preserves projection dimension. The o-minimal Euler characteristic of a residue normal form is independent of the choice of normalization, and the cited classification transfers to the original RV sets. |
| §2.4, Definitions 2.32 and 2.36 and Notation 2.34 | `ValuativeDisc`, `DiscCodes`, `HigherLeadingTerm`, `TorsorDerivative`, `ValuedFieldFormulas` | First-order valued-field formulas compare represented values and define disc membership and equality of codes. Disc codes identify descriptions with equal point sets, including the closed radius-zero points. A disc has constant valuation exactly when it avoids zero or is the singleton at zero. Coordinate products give polydiscs and polyradii. The RV hull is the least union of RV fibers containing the given set. The higher leading-term maps identify the maximal open children. Their quotient has a residue chart, with the inherited order, affine chart changes, and the entire central class. Uniqueness of derivatives and invariance of the normalized derivative under affine changes of charts. |
| §2.4, valuative intervals and Holly normal form | `ValuativeInterval`, `EndDiscs`, `DefinableEndDiscs`, `HollyNormalForm`, `DefinableHolly` | Boolean closure of finite unions of valuative intervals. A nonempty interval is definable over a parameter set precisely when its end-discs are. Upward and downward closures give the endpoint rays, and their translation periods recover the end-discs. The representative interpretation gives definability of unary VF sets in the valued-field language. A unary Boolean description gives the unique interval decomposition, and naming a point in each component makes it definable. |

The unsigned value uses Mathlib's multiplicative valuation convention, with
values below one on the maximal ideal. Its order is dual to the manuscript's
additive convention.

## Cited hypotheses

The Lean declarations take cited mathematical inputs as explicit hypotheses.
`exists_formula_continuousFunctionalLanguage` takes the cell
decomposition over the empty base from van den Dries (1998), Chapter 3,
as an input. The continuous descriptions themselves follow from
definable infima and the order topology.
[Cell decomposition](https://www.cambridge.org/core/books/tame-topology-and-ominimal-structures/cell-decomposition/04F570063CE5D7F34AE6152836529552)

`RestrictedAnalyticHahnFacts` records DMM (1994), Corollary 2.11 and
Theorem 2.14, and the polynomial growth and rational exponent inputs
of Example 2.8. The canonical expansion uses the T-convex hull and residue
matching from van den Dries–Lewenberg (1995).
[Restricted analytic fields](https://annals.math.princeton.edu/1994/140-1/p05)

`ConvexTheoryFacts` records van den Dries–Lewenberg (1995), Theorem 3.10 and
Corollary 3.13. `WeakImmediacyTransfer` and `LeadingTermMonomialTransfer`
record the uses of Freni's thesis, Proposition 3.3.11 (Tyne) and Corollary
3.3.13, for the specified one-generator extension.
`vfDimension_eq_max_fiber_rank` uses Macpherson, Marker, and Steinhorn
(2000), Theorem 4.12. `signedValue_fiber_dimension` and
`exists_definable_embedding_of_vfDimension_le` use the coordinate
projection charts of Theorem 4.11. For the latter, the input is a chart
formula in each pointed fiber and its open projection, with the
parameters already named by the base and the fiber tuple.
The relative finrank hypothesis in
`span_base_and_new_value_of_relative_finrank_le_one` is the value-space
part of van den Dries (1997), Corollary 5.6.
`RelativeValueRankLEOne` states the same bound for the old-value subspace
constructed from a field closed under the named powers.
`HasInducedResidueDefinability` records van den Dries (1997), Theorem A.
`RVCoordinateDefinability` specifies the value- and residue-language
definability inputs used with Theorems A and B, including the graphs of the
restricted exponent operations.
`HasFixedBaseAffineGraphDecomposition` states the piecewise-affine
part of Theorem B for a definable graph over a value subspace.
`rvDefinablyEquivalent_iff_projectionDimension_euler` uses the classification
of residue normal forms from van den Dries (1998), §8.2.11, and
definable-bijection invariance of RV dimension from Macpherson, Marker,
and Steinhorn (2000), Theorem 4.7. Independence of the choice of residue
normal form uses definable-bijection invariance of the o-minimal Euler
characteristic from van den Dries (1998), §4.2.

The canonical interpretation takes the uniform defining graphs for the
continuous presentation as inputs. The single-model construction of
continuous descriptions is checked separately. The isomorphism with a presentation
uses the residue compatibility, order, and power conditions in Definition 2.9.
The quantifier-elimination theorem for the interpreted theory takes
the model data and uniform interpretation of the recovered valued fields
and the rank and residue data for the actual generated adjunction as explicit
inputs. The canonical isomorphisms of the recovered models follow in Lean. It constructs the
field embedding, restricted powers, and fixed-RV extension.
`OneGeneratorWilkieInequality` states the relative rank bound of van den Dries
(1997), Corollary 5.6. The two rank alternatives follow in Lean. The
trivially valued monomial calculation also gives the relative value rank
bound. The rank consequences of the cited inequalities and leading-term
formula are checked for both kinds of base. The uniform supply of the
relative residue pregeometry and natural residue maps remains an
explicit input on pairs of canonical models. Lemma 2.20 uses the same
inputs, the cited valued-field QE, and small-field saturation.
Lemma 2.22 also uses the translate detector from the reviewed
valuation and weak-immediacy cases. The RV closure theorem constructs
the VF-generated enlargement from the representative step of Theorem 2.16.
It takes sorted QE, the proper-pair model condition, and two independent
values as hypotheses.
For Lemma 2.26, `isLeast_definableMixedEmbeddingArities_of_small_field_base`
obtains the closure step from `CanonicalQEModel.exists_immediate_automorphism_moving_field`
and `vf_range_subset_fieldClosure_of_small_immediate_movers`, using the
same saturation and source inputs as Lemmas 2.20 and 2.22.
The relative closure and rank are those of the field pregeometry,
using van den Dries–Lewenberg (1995), §3.2, and the cited weakly
o-minimal dimension results.
For Lemma 2.29 the checked selection uses the cited coordinate charts
and piecewise-affine graph theorem.
The unary Boolean description used to obtain Holly normal form is a premise.
