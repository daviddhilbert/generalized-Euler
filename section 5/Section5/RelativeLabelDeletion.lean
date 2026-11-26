module

public import Section5.RelativeRVWitnesses

/-! Delete one active label coordinate in a family while keeping the
parameters and all RV tags. This is the lower-degree blowup graph. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P : TCsort → Type} {m k : ℕ}

local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin (k+1))
local notation "W" => RVVariables (Fin k)

@[expose] def deleteRVAssignment (j : Fin (k+1)) (v : SortedAssignment X V) : SortedAssignment X W
  | .vf => PEmpty.elim
  | .rv => v .rv ∘ j.succAbove

@[expose] def relativeDeleteLabelGraph (j : Fin (k+1))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))) :
    Set (SortedAssignment X (SumVariables (SumVariables P U) W)) :=
  {a | ∃ v : SortedAssignment X V, appendAssignments (fun s => a s ∘ Sum.inl) v ∈ G ∧
    deleteRVAssignment j v = (fun s => a s ∘ Sum.inr)}

theorem relativeDeleteLabelGraph_definable (j : Fin (k+1))
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defG : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier (relativeDeleteLabelGraph j G) := by
  let R := SumVariables P U
  let T := SumVariables (SumVariables R W) V
  let take (s : TCsort) : SumVariables R V s → T s := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have coords := SortedDefinableOver.iInter (fun i : Fin k =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T) .rv (.inr (j.succAbove i)) (.inl (.inr i)))
  have projected := definable_project_mixed ((defG.pullback_relabel take).inter coords)
  convert projected using 1
  ext a
  let t : SortedAssignment X W := fun s => a s ∘ Sum.inr
  let p : SortedAssignment X R := fun s => a s ∘ Sum.inl
  have takeEq (v : SortedAssignment X V) :
      (fun s => appendAssignments a v s ∘ take s) = appendAssignments p v := by
    funext s i
    cases i <;> rfl
  simp only [Set.mem_iInter,Set.mem_inter_iff]
  change (∃ v : SortedAssignment X V, appendAssignments p v ∈ G ∧ deleteRVAssignment j v = t) ↔
    ∃ v : SortedAssignment X V, (fun s => appendAssignments a v s ∘ take s) ∈ G ∧
      ∀ i, v .rv (j.succAbove i) = t .rv i
  simp only [takeEq]
  constructor
  · rintro ⟨v,h,e⟩
    exact ⟨v,h,fun i => congrFun (congrFun e .rv) i⟩
  · rintro ⟨v,h,e⟩
    refine ⟨v,h,?_⟩
    funext s i
    cases s
    · exact i.elim
    · exact e i

theorem relativeDeleteLabelGraph_iff (j : Fin (k+1))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (p : SortedAssignment X P) (a : SortedAssignment X U) (w : SortedAssignment X W) :
    appendAssignments (appendAssignments p a) w ∈ relativeDeleteLabelGraph j G ↔
      ∃ v, appendAssignments (appendAssignments p a) v ∈ G ∧ deleteRVAssignment j v = w := Iff.rfl

theorem relativeDeleteLabelGraph_valid (j : Fin (k+1))
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {zero : X .rv} {oldBound newBound : ℕ} {p : SortedAssignment X P}
    (old : RelativeRVWitness D G zero oldBound p)
    (finiteDelete : ∀ (v : SortedAssignment X W) (a : Fin (newBound+1) → SortedAssignment X U),
      (∀ i, appendAssignments (appendAssignments p (a i)) v ∈ relativeDeleteLabelGraph j G) →
      ¬ Function.Injective a) :
    RelativeRVWitness D (relativeDeleteLabelGraph j G) zero newBound p := by
  unfold RelativeRVWitness
  refine ⟨?_,?_,?_,finiteDelete⟩
  · intro a
    rw [old.1]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨deleteRVAssignment j v,(relativeDeleteLabelGraph_iff j G p a _).2 ⟨v,hv,rfl⟩⟩
    · rintro ⟨w,hw⟩
      obtain ⟨v,hv,_⟩ := (relativeDeleteLabelGraph_iff j G p a w).1 hw
      exact ⟨v,hv⟩
  · intro a w w' hw hw'
    obtain ⟨v,hv,eq⟩ := (relativeDeleteLabelGraph_iff j G p a w).1 hw
    obtain ⟨v',hv',eq'⟩ := (relativeDeleteLabelGraph_iff j G p a w').1 hw'
    rw [← eq,← eq',old.2.1 a _ _ hv hv']
  · intro a w hw i
    obtain ⟨v,hv,eq⟩ := (relativeDeleteLabelGraph_iff j G p a w).1 hw
    rw [← eq]
    exact old.2.2.1 a v hv (j.succAbove i)

end GeneralizedEuler.Section5
