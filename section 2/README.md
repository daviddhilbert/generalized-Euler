# Section 2 · Basic results in T-convex valued fields

Lean 4 formalization of the reviewed manuscript. Run from this directory:

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
| Theorem 2.11 and Proposition 2.13 | `ConvexLanguage`, `LeadingTermMap`, `LeadingTermPresentation` | The valued-field reduct and the cited QE input, elementarity of embeddings under QE, transport along valued-field embeddings, and uniqueness of the ordered multiplicative RV quotient. |
| §2.3, Theorem 2.16 and Lemmas 2.20–2.22 | `SortedSyntax`, `SortedModelTheory`, `LeadingTerm`, `PrescribedLift`, `TrivialBaseLift`, `ImmediateExtension` | Quantifier-free invariance and the semantic back-and-forth criterion. The valued-field test for RV equality, the cut comparison for a prescribed leading term, the prescribed-lift calculation over a trivial base, and the argument from old leading terms to weak immediacy and then equality of RV images. |
| §2.4, Lemma 2.29 and Notation 2.34 | `AffinePullback`, `ValuativeDisc` | The affine pullback equivalence on each given piece, with the translation lifted in the same base. The closed-disc quotient by open children and its residue chart, including the entire central class. |

The unsigned value uses Mathlib's multiplicative valuation convention, with
values below one on the maximal ideal. Its order is dual to the manuscript's
additive convention.

## Cited hypotheses

The Lean declarations take cited mathematical inputs as explicit hypotheses.
`ConvexTheoryFacts` records van den Dries–Lewenberg (1995), Theorem 3.10 and
Corollary 3.13. `WeakImmediacyTransfer` and `LeadingTermMonomialTransfer`
record the uses of Freni's thesis, Proposition 3.3.11 (Tyne) and Corollary
3.3.13, for the specified one-generator extension.

The remaining work includes the full expansion of Proposition 2.13,
completeness and the extension steps for two-sorted QE, and the definability
and dimension arguments in §2.4. The affine equivalence already checked
assumes the affine piece and its intercept are given. Choosing the finite
partition and proving its definability over the fixed base are separate
proof obligations in Lemma 2.29.
