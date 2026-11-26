module

public import Section5.LiftBoundaryDimension

/-! Definability of RV coordinate projections and their images. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ}

/-- A tuple of selected coordinates, in the order of the selection. -/
@[expose] def projectLabels (p : Fin k → Fin n) (a : labelAssignment n X) :
    labelAssignment k X :=
  rvTupleAssignment (a .rv ∘ p)

theorem projectLabels_definable (p : Fin k → Fin n) :
    DefinableRelation M S.carrier (fun a b => projectLabels p a = b) := by
  let V := SumVariables (RVVariables (Fin n)) (RVVariables (Fin k))
  have h := SortedDefinableOver.iInter (fun i : Fin k =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V) .rv
      (.inl (p i)) (.inr i))
  unfold DefinableRelation
  convert h using 1
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro eq i
    exact congrFun (congrFun eq .rv) i
  · intro eq
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => exact eq i

theorem projectLabels_image_definable (p : Fin k → Fin n)
    {A : Set (labelAssignment n X)} (hA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier (projectLabels p '' A) :=
  (projectLabels_definable p).image hA

end GeneralizedEuler.Section5
