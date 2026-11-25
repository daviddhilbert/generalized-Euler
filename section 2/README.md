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
| §2.2, Ax. 8–10 | `LeadingTermPower`, `PowerOrder` | The clamping proof of descent and uniqueness. Algebraic and ordered laws on the positive branch, and reduction of a compatible positive power on a positive unit. |
| Theorem 2.11 and Proposition 2.13 | `ConvexLanguage`, `LeadingTermMap`, `LeadingTermPresentation`, `ResidueMap`, `CanonicalEmbedding` | The valued-field reduct and the cited QE input, elementarity of embeddings under QE, transport along valued-field embeddings, uniqueness of the ordered multiplicative RV quotient, and embeddings between canonical expansions with compatible residue operations and powers. |
| §2.3, Theorem 2.16 and Lemmas 2.20–2.22 | `SortedSyntax`, `SortedModelTheory`, `TaggedLanguage`, `TaggedSyntax`, `PrescribedLift`, `TrivialBaseLift`, `ImmediateExtension`, `VFLiftSubstructure`, `ConvexRingComparison` | Quantifier-free invariance, the semantic back-and-forth criterion, and a guarded translation into Mathlib's ordinary first-order syntax. The prescribed-lift calculation over a trivial base, comparison of convex rings, enlargement of VF with a compatible embedding and unchanged RV, and the transfer from old leading terms to equality of RV images. |
| §2.4, Definition 2.25, Remark 2.27 and Lemma 2.28 | `WeakOminimal`, `Dimension`, `ValueFiberTopology` | Descent of finite convex decomposition along RV, projection dimension and the maximal fiber-rank calculation, openness of nonzero signed value fibers, and preservation of dimension on a fiber using a maximal-dimensional chart. |
| §2.4, Lemma 2.29 | `ValueSplitting`, `SeparatedSets`, `AffinePullback` | A base-compatible linear section, closure of finite unions of rectangles under Boolean operations and coordinate projections, and the affine equivalence on each given piece. |
| §2.4, Definitions 2.32 and 2.36 and Notation 2.34 | `ValuativeDisc`, `TorsorDerivative`, `ValuativeInterval` | Maximality of the open children and the residue chart on their quotient, including the entire central class. Uniqueness of derivatives and invariance of the normalized derivative under affine changes of charts. Valuative intervals and the statement of a Holly decomposition. |

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

The remaining work includes the full expansion of Proposition 2.13,
completeness and the extension steps for two-sorted QE, and the definability
and dimension arguments in §2.4. The affine equivalence already checked
assumes the affine piece and its intercept are given. Choosing the finite
partition and proving its definability over the fixed base are separate
proof obligations in Lemma 2.29.
