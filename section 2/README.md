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
| Theorem 2.11 and Proposition 2.13 | `ConvexLanguage`, `LeadingTermMap`, `LeadingTermPresentation`, `ResidueMap`, `CanonicalEmbedding`, `CanonicalModel` | The valued-field reduct and the cited QE input, elementarity of embeddings under QE, uniqueness of the ordered multiplicative RV quotient, and embeddings between canonical expansions. Given the residue model and the reduction of the clamped powers, the canonical quotient admits a unique family of power interpretations. |
| Theorem 2.14 and the VF definability corollary | `QuotientInterpretation`, `ValuedFieldFormulas` | Translation of sorted formulas to formulas on representatives, transfer of completeness through a uniform interpretation, and transfer of definability over parameter representatives. Explicit valued-field formulas for RV equality, the residue predicate, and functions on RV obtained by reducing a field term and extending it by zero. |
| §2.3, Theorem 2.16 and Lemmas 2.20–2.22 | `SortedModelTheory`, `TaggedTheory`, `SortedTypes`, `SortedQE`, `GeneratedSubstructure`, `PrescribedLift`, `TrivialBaseLift`, `ImmediateExtension`, `VFLiftSubstructure`, `RVAgreement`, `ConvexRingComparison` | Sorted compactness for theories and partial types, the Shoenfield criterion, and embeddings of generated substructures from matching quantifier-free types. The cut calculation for an RV map on the old substructure, the prescribed-lift calculation over a trivial base, comparison of convex rings, and agreement of RV embeddings on the new-value monomials. Enlargement of VF with a compatible embedding and unchanged RV, and the transfer from old leading terms to equality of RV images. |
| §2.3, one-generator extensions | `FieldGeneratedEmbedding`, `FieldTypeLift`, `TrivialBaseLift`, `ConvexRingComparison`, `RVAgreement` | Matching cuts give a field-language embedding from the same unary cell descriptions. Valued-field QE and the one-point saturation hypothesis give extensions over common field representatives. Relative value rank at most one gives the span by a new value. Over a trivial base, the new-value calculation handles either side of one, and a new residue leaves the generated field trivially valued under the valuation property. Agreement on intermediate leading terms gives the sorted lift. |
| §2.4, Definition 2.25, Lemma 2.26, Remark 2.27 and Lemma 2.28 | `WeakOminimal`, `Dimension`, `ValueFiberTopology` | Descent of finite convex decomposition along RV, projection dimension and the maximal fiber-rank calculation, the injection built from a finite cover by coordinate charts with RV tags, and preservation of dimension on a signed value fiber using a maximal-dimensional chart. |
| §2.4, Remark 2.27 | `SortedDefinability`, `RVReduct` | Fixed-base Boolean operations and projection. After QE, formulas on RV tuples reduce to RV formulas using only parameters already in the base RV sort. |
| §2.4, Lemma 2.29 | `ValueSplitting`, `SeparatedSets`, `AffinePullback` | A base-compatible linear section and the corresponding product coordinates. Closure of finite unions of rectangles under Boolean operations and coordinate projections. The affine equivalence on each given piece assembles over a disjoint partition with intercept representatives in the same base. |
| §2.4, Remark 2.30 | `ResidueFiber` | Multiplicative translation identifies a nonzero value fiber with the nonzero residue field, with a coordinatewise version and a chart retaining the value label of each tuple. A positive representative gives an order isomorphism. |
| §2.4, Definitions 2.32 and 2.36 and Notation 2.34 | `ValuativeDisc`, `HigherLeadingTerm`, `TorsorDerivative` | The higher leading-term quotients and their fibers. Maximality of the open children and the residue chart on their quotient, including its order, affine chart changes, and the entire central class. Uniqueness of derivatives and invariance of the normalized derivative under affine changes of charts. |
| §2.4, valuative intervals and Holly normal form | `ValuativeInterval`, `HollyNormalForm` | Boolean closure of finite unions of valuative intervals. Existence and uniqueness of the interval decomposition for a unary Boolean combination of order and valuation conditions. |

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

The remaining work includes completing the uniform interpretation for the
full residue language and the named powers, the field-specific extension
steps for two-sorted QE, and the remaining definability and dimension
arguments in §2.4. The affine equivalence uses given pieces and intercepts.
Choosing the finite partition and proving its definability over the fixed
base are proof obligations in Lemma 2.29.
For Holly normal form, the conversion from definability to the unary
Boolean description and the definability of the component endpoints
remain to be connected to the sorted theory.
