module

public import Section5.DefinableRelations
public import Section5.VerticalCenters

/-! Compactness chooses one finite list of tuples of field terms when
each parameter fiber contains a witness in the generated field sort. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {V : TCsort → Type}
  {k : ℕ}

abbrev FieldTermTuple (M : SortedStructure L E X) (S : SortedSubstructure M)
    (V : TCsort → Type) (k : ℕ) :=
  Fin k → SortedTerm L E (WithBase S.carrier V) .vf

@[expose] def realizeFieldTuple (T : FieldTermTuple M S V k)
    (x : SortedAssignment X V) : SortedAssignment X (MixedVariables k Empty)
  | .vf => fun i => (T i).realize M (fun s => Sum.elim Subtype.val (x s))
  | .rv => Empty.elim

theorem fieldTuple_graph (T : FieldTermTuple M S V k) :
    DefinableRelation M S.carrier (fun x y => realizeFieldTuple T x = y) := by
  let W := MixedVariables k Empty
  let rename : ∀ s, WithBase S.carrier V s → WithBase S.carrier (SumVariables V W) s :=
    fun s => Sum.map id Sum.inl
  have defEq (j : Fin k) := SortedDefinableOver.coordinate_eq_term
    (M := M) (A := S.carrier) (Var := SumVariables V W) .vf (.inr j) ((T j).relabel rename)
  unfold DefinableRelation
  convert SortedDefinableOver.iInter defEq using 1
  ext v
  let x (s : TCsort) := v s ∘ Sum.inl
  let y (s : TCsort) := v s ∘ Sum.inr
  have he : (fun s => Sum.elim Subtype.val (v s) ∘ rename s) =
      (fun s => Sum.elim Subtype.val (x s)) := by
    funext s i
    cases i <;> rfl
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, SortedTerm.realize_relabel]
  change (realizeFieldTuple T x = y) ↔
    ∀ j, v .vf (.inr j) = (T j).realize M (fun s => Sum.elim Subtype.val (v s) ∘ rename s)
  rw [he]
  constructor
  · intro h j
    exact (congrFun (congrFun h .vf) j).symm
  · intro h
    funext s i
    cases s with
    | vf => exact (h i).symm
    | rv => exact i.elim

theorem termWitness_valid_definable
    {R : SortedAssignment X V → SortedAssignment X (MixedVariables k Empty) → Prop}
    (hR : DefinableRelation M S.carrier R) (T : FieldTermTuple M S V k) :
    SortedDefinableOver M S.carrier {x | R x (realizeFieldTuple T x)} := by
  have hT := fieldTuple_graph T
  unfold DefinableRelation at hR hT
  have h := definable_project_mixed (hT.inter hR)
  convert h using 1
  ext x
  change R x (realizeFieldTuple T x) ↔ ∃ y, realizeFieldTuple T x = y ∧ R x y
  exact ⟨fun h => ⟨_,rfl,h⟩, fun ⟨_,rfl,h⟩ => h⟩

/-- The existence of a term witness for each input in a definable domain
gives a finite family of such terms, uniformly over the fixed base. -/
theorem finite_field_term_witnesses
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier V)
      (BaseAssignments S.carrier V))
    (A : Set (SortedAssignment X V)) (hA : SortedDefinableOver M S.carrier A)
    {R : SortedAssignment X V → SortedAssignment X (MixedVariables k Empty) → Prop}
    (hR : DefinableRelation M S.carrier R)
    (witness : ∀ x ∈ A, ∃ T : FieldTermTuple M S V k, R x (realizeFieldTuple T x)) :
    ∃ C : Finset (FieldTermTuple M S V k),
      ∀ x ∈ A, ∃ T ∈ C, R x (realizeFieldTuple T x) := by
  classical
  obtain ⟨φ,hφ⟩ := hA
  have hdef (T) := termWitness_valid_definable hR T
  choose ψ hψ using hdef
  let V' := WithBase S.carrier V
  let W := BaseAssignments S.carrier V
  obtain ⟨C,hC⟩ := finite_tests M V' W sat φ (fun T => (ψ T).neg) (by
    intro v hv htests hφv
    let x (s : TCsort) (i : V s) := v s (.inr i)
    have hv' : v = fun s => Sum.elim Subtype.val (x s) := by
      funext s i
      cases i with
      | inl c => exact hv s c
      | inr i => rfl
    rw [hv'] at htests hφv
    obtain ⟨w, hw⟩ := witness x ((hφ x).2 hφv)
    exact ((ψ w).realize_neg M _).1 (htests w) ((hψ w x).1 hw))
  refine ⟨C, fun x hx => ?_⟩
  by_contra! h
  let v (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → X s) (x s)
  exact hC v (fun _ _ => rfl)
    (fun T ht => ((ψ T).realize_neg M v).2 (fun hp => h T ht ((hψ T x).2 hp)))
    ((hφ x).1 hx)

end GeneralizedEuler.Section5
