module

public import Section5.FieldTermWitnesses

/-! Uniform fixed-base field choice by the first valid term tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {V : TCsort → Type} {k : ℕ}

/-- Once field term witnesses exist over each input, the first valid
tuple in a single finite list gives a fixed-base definable choice. -/
theorem definable_field_choice_from_terms
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier V) (BaseAssignments S.carrier V))
    (A : Set (SortedAssignment X V)) (hA : SortedDefinableOver M S.carrier A)
    {R : SortedAssignment X V → SortedAssignment X (MixedVariables k Empty) → Prop}
    (hR : DefinableRelation M S.carrier R)
    (witness : ∀ x ∈ A, ∃ T : FieldTermTuple M S V k, R x (realizeFieldTuple T x)) :
    ∃ f : A → SortedAssignment X (MixedVariables k Empty),
      (∀ x : A, R x.val (f x)) ∧
      DefinableRelation M S.carrier (fun x y => ∃ h : x ∈ A, f ⟨x,h⟩ = y) := by
  classical
  obtain ⟨C,hC⟩ := finite_field_term_witnesses sat A hA hR witness
  let m := Fintype.card C
  let order : Fin m ≃ C := (Fintype.equivFin C).symm
  let term (i : Fin m) := (order i).val
  let valid (x : SortedAssignment X V) (i : Fin m) := R x (realizeFieldTuple (term i) x)
  let good (x : A) := (Finset.univ : Finset (Fin m)).filter (valid x.val)
  have hn (x : A) : (good x).Nonempty := by
    obtain ⟨T,hT,hvalid⟩ := hC x.val x.property
    let i := order.symm ⟨T,hT⟩
    have hi : term i = T := congrArg Subtype.val (order.apply_symm_apply ⟨T,hT⟩)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [valid,hi] using hvalid⟩⟩
  let first (x : A) := (good x).min' (hn x)
  have valid_first (x : A) : valid x.val (first x) := by
    exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
  have least (x : A) (i : Fin m) (hi : valid x.val i) : first x ≤ i :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  let cell (i : Fin m) : Set (SortedAssignment X V) :=
    {x | x ∈ A ∧ valid x i ∧ ∀ j < i, ¬ valid x j}
  have in_cell (x : A) : x.val ∈ cell (first x) :=
    ⟨x.property, valid_first x, fun j hlt hj => (not_le_of_gt hlt) (least x j hj)⟩
  have first_of_cell (x : A) (i : Fin m) (h : x.val ∈ cell i) : first x = i := by
    apply le_antisymm (least x i h.2.1)
    exact le_of_not_gt (fun hc => h.2.2 _ hc (valid_first x))
  have validDef (i : Fin m) : SortedDefinableOver M S.carrier {x | valid x i} :=
    termWitness_valid_definable hR (term i)
  have cellDef (i : Fin m) : SortedDefinableOver M S.carrier (cell i) := by
    have earlier := SortedDefinableOver.iInter (fun j : {j : Fin m // j < i} => (validDef j.val).compl)
    convert hA.inter ((validDef i).inter earlier) using 1
    ext x
    simp only [cell, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      Subtype.forall]
  let f (x : A) := realizeFieldTuple (term (first x)) x.val
  refine ⟨f, valid_first, ?_⟩
  let W := MixedVariables k Empty
  let piece (i : Fin m) : Set (SortedAssignment X (SumVariables V W)) :=
    {v | (fun s => v s ∘ Sum.inl) ∈ cell i ∧
      realizeFieldTuple (term i) (fun s => v s ∘ Sum.inl) = (fun s => v s ∘ Sum.inr)}
  have pieceDef (i : Fin m) : SortedDefinableOver M S.carrier (piece i) :=
    ((cellDef i).pullback_relabel (fun s => Sum.inl)).inter (fieldTuple_graph (term i))
  unfold DefinableRelation
  convert SortedDefinableOver.iUnion pieceDef using 1
  ext v
  let x (s : TCsort) := v s ∘ Sum.inl
  let y (s : TCsort) := v s ∘ Sum.inr
  change (∃ h : x ∈ A, f ⟨x,h⟩ = y) ↔ v ∈ ⋃ i, piece i
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨h,he⟩
    exact ⟨first ⟨x,h⟩,in_cell ⟨x,h⟩,he⟩
  · rintro ⟨i,hcell,hy⟩
    refine ⟨hcell.1, ?_⟩
    change realizeFieldTuple (term (first ⟨x,hcell.1⟩)) x = y
    rw [first_of_cell ⟨x,hcell.1⟩ i hcell]
    exact hy

end GeneralizedEuler.Section5
