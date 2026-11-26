module

public import Section5.FieldArityPreparation

/-! Restriction of a preparation to a mixed definable graph, and
contraction of its RV-valued output. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*} {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type}
  {G : PointTests O n I J}

@[expose] def testDomain (G : PointTests O n I J) :
    Set (PreparationPoint O (Fin n) I) :=
  {p | ∃ s, (p,s) ∈ G}

namespace PreparedMap

/-- The full domain image is a pullback. Empty output sets account for
points outside the original domain. -/
theorem domain_image_whole (P : PreparedMap M S G)
    (a b : PreparationPoint O (Fin n) P.tags) (he : preparationLabel a = preparationLabel b) :
    (a ∈ P.map '' testDomain G ↔ b ∈ P.map '' testDomain G) := by
  have step (u v : PreparationPoint O (Fin n) P.tags)
      (h : preparationLabel u = preparationLabel v) (hu : u ∈ P.map '' testDomain G) :
      v ∈ P.map '' testDomain G := by
    obtain ⟨p,⟨s,hs⟩,hp⟩ := hu
    have same : u ∈ P.map '' {p | (p,s) ∈ G} := ⟨p,hs,hp⟩
    obtain ⟨q,hq,he⟩ := (P.test_image_whole s h).1 same
    exact ⟨q,⟨s,hq⟩,he⟩
  exact ⟨step a b he, step b a he.symm⟩

/-- For a function graph the contraction is single-valued. The map is
the same for every RV output tuple. -/
theorem graph_contracts (P : PreparedMap M S G)
    (unique : ∀ p s t, (p,s) ∈ G → (p,t) ∈ G → s = t)
    {p q : PreparationPoint O (Fin n) I} {s t : J → RV0 O}
    (hp : (p,s) ∈ G) (hq : (q,t) ∈ G)
    (he : preparationLabel (P.map p) = preparationLabel (P.map q)) : s = t :=
  unique q s t ((P.tests p q he s).1 hp) hq

/-- The sequence of translations restricts to the domain of the graph. -/
theorem on_testDomain_special (P : PreparedMap M S G)
    (h : SpecialChain O (Fin n) Set.univ P.map) :
    SpecialChain O (Fin n) (testDomain G) P.map :=
  h.restrict (Set.subset_univ _)

end PreparedMap

end GeneralizedEuler.Section5
