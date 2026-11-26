module

public import Section5.RelativeElementarySchemes
public import Section5.RelativeSchemeDescent

/-! Descent of an elementary scheme preserves validity of the
original label graph and its deleted-label graph. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P Q : TCsort → Type} {m k : ℕ}

local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin (k+1))
local notation "W" => RVVariables (Fin k)

theorem relativeDeleteLabelGraph_descend (j : Fin (k+1))
    (H : SortedAssignment X P → SortedAssignment X Q → Prop)
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))) :
    descendRelationScheme H (relativeDeleteLabelGraph j G) =
      relativeDeleteLabelGraph j (descendRelationScheme H G) := by
  ext a
  let q : SortedAssignment X Q := fun s => a s ∘ Sum.inl ∘ Sum.inl
  let u : SortedAssignment X U := fun s => a s ∘ Sum.inl ∘ Sum.inr
  let w : SortedAssignment X W := fun s => a s ∘ Sum.inr
  have eq : (fun s => a s ∘ Sum.inl) = appendAssignments q u := by
    funext s i
    cases i <;> rfl
  change (∃ p, H p q ∧ ∃ v : SortedAssignment X V,
    appendAssignments (appendAssignments p u) v ∈ G ∧ deleteRVAssignment j v = w) ↔
    (∃ v : SortedAssignment X V, appendAssignments (fun s => a s ∘ Sum.inl) v ∈ descendRelationScheme H G ∧
      deleteRVAssignment j v = w)
  rw [eq]
  constructor
  · rintro ⟨p,hp,v,hv,he⟩
    exact ⟨v,⟨p,hp,hv⟩,he⟩
  · rintro ⟨v,⟨p,hp,hv⟩,he⟩
    exact ⟨p,hp,v,hv,he⟩

@[expose] def RelativeElementaryScheme.descend [Finite (P .vf)] [Finite (P .rv)]
    (I : RelativeElementaryScheme M S P k)
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) : RelativeElementaryScheme M S Q k where
  arity := I.arity
  slot := I.slot
  sourceBound := I.sourceBound
  deletionBound := I.deletionBound
  tags := descendFiberScheme H I.tags
  graph := descendRelationScheme H I.graph
  tagsDefinable := descendFiberScheme_definable defH I.tagsDefinable
  graphDefinable := descendRelationScheme_definable defH I.graphDefinable

theorem RelativeElementaryScheme.descend_valid [Finite (P .vf)] [Finite (P .rv)]
    (I : RelativeElementaryScheme M S P k)
    {H : SortedAssignment X P → SortedAssignment X Q → Prop} (defH : DefinableRelation M S.carrier H)
    {p : SortedAssignment X P} {q : SortedAssignment X Q} (hp : H p q) (zero : S.carrier .rv)
    (constD : ∀ p', H p' q → ∀ u, appendAssignments p u ∈ I.tags ↔ appendAssignments p' u ∈ I.tags)
    (constG : ∀ p', H p' q → ∀ u v, appendAssignments (appendAssignments p u) v ∈ I.graph ↔
      appendAssignments (appendAssignments p' u) v ∈ I.graph)
    (valid : I.valid zero p) :
    (I.descend defH).valid zero q := by
  unfold RelativeElementaryScheme.valid
  constructor
  · exact relativeRVWitness_descends hp constD constG valid.1
  · change RelativeRVWitness (descendFiberScheme H I.tags)
      (relativeDeleteLabelGraph I.slot (descendRelationScheme H I.graph)) zero.val I.deletionBound q
    rw [← relativeDeleteLabelGraph_descend]
    apply relativeRVWitness_descends hp constD _ valid.2
    intro p' h' u w
    simp only [relativeDeleteLabelGraph_iff,constG p' h' u]

end GeneralizedEuler.Section5
