# Section 2 · Basic results in T-convex valued fields

This Lake package starts the Lean 4 formalization of the reviewed manuscript.
Run these commands from this directory:

```sh
lake exe cache get
lake build
```

The package pins the same Lean and mathlib revisions as the related ACVF
projects. Import `Section2` to use the declarations below.

| Manuscript | Lean module | Checked content |
| --- | --- | --- |
| Convention 2.1 and Definition 2.2 | `Section2.PowerBounded` | Definability over a parameter set, o-minimality, and power boundedness. The arbitrary-parameter definition uses the entire field as parameter set. |
| §2.2, signature | `Section2.Language` | VF and RV₀ sorts, typed function and relation symbols, and exponent-indexed RV powers. |
| §2.2, Ax. 2 and Ax. 5 | `Section2.LeadingTerm` | RV as the quotient by principal units, separate zero, the surjective multiplicative RV map, the unsigned value map, and the ring and maximal-ideal tests on RV₀. |
| §2.2, Ax. 8–10 | `Section2.ConvexValuation`, `Section2.LeadingTermPower` | The reviewed clamping argument, existence and uniqueness of each RV power under residue compatibility, and the algebraic laws on the positive branch. |
| §2.3 and §2.4, supporting lemmas | `Section2.LeadingTerm` | Equality of leading terms in the valued-field language and the open-disc description of a nonzero RV fiber. |

The unsigned value uses mathlib's multiplicative valuation convention, with
values below one on the maximal ideal. Its order is dual to the manuscript's
additive convention. Order convexity of the valuation ring and residue
compatibility for the clamped field power are explicit hypotheses.

The next step in §2.2 is to give the signature its first-order semantics and
complete the signed order and residue-field interpretation. The remaining
power axioms include strict monotonicity and agreement on positive residue
elements. Quantifier elimination in §2.3 and the structural results in §2.4
remain open. In the later parameter arguments, Lemma 2.29 uses the same base
for the partition and lift, including when its value group is trivial.
Notation 2.34 uses the quotient by maximal open subdiscs, including the
central child.
