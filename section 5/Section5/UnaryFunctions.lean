module

public import Section5.UnaryDeformation

/-! Applying unary preparation to all output values of an RV-valued
graph at once, as in the unary case of Corollary 5.6. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I J : Type}

local notation "M" => canonicalStructure (L := L) O hO power

set_option linter.style.haveILetI false in
/-- For one field variable, prepare a definable RV-valued graph in one
step. Empty output fibers give the complement of the domain. Single-valued
output fibers give contraction of the represented partial function. -/
theorem unary_graph_preparation
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes M (CenterTestVariables S.carrier (I ⊕ J))
      (CenterTestAssignments S.carrier (I ⊕ J)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism M M, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (G : Set ((K × (I → RV0 O)) × (J → RV0 O)))
    (hG : SortedDefinableOver M S.carrier
      {a : ∀ s, MixedVariables 1 (I ⊕ J) s → CanonicalSort O s |
        ((a .vf 0, a .rv ∘ Sum.inl), a .rv ∘ Sum.inr) ∈ G}) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      (∀ x y ξ, P.label x = P.label y →
        {t | ((x, ξ), t) ∈ G} = {t | ((y, ξ), t) ∈ G}) ∧
      SortedDefinableOver M S.carrier
        {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
          P.map (v .vf 0) = (v .vf 1, decodeHistory O cs.length (v .rv))} := by
  let A : Set (K × (I ⊕ J → RV0 O)) := {p | ((p.1, p.2 ∘ Sum.inl), p.2 ∘ Sum.inr) ∈ G}
  obtain ⟨cs, hgraph, _, hconst, _⟩ :=
    unary_deformation O hO power S minusOne hm F hF sat immediate A hG
  refine ⟨cs, ?_, hgraph⟩
  intro x y ξ he
  ext t
  exact hconst x y (Sum.elim ξ t) he

end GeneralizedEuler.Section5
