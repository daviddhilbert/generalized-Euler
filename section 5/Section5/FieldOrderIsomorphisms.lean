module

public import Section5.RelativelyUnaryContractions
public import Section5.MixedRelabeling

/-! Reindexing the field coordinates induces the expected definable
bijection and leaves the retained RV tuple fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ}

local notation "Z" => CanonicalSort O

theorem RetainedFieldFamily.permuteVF_iso (A : RetainedFieldFamily M S n k)
    (order : Equiv.Perm (Fin n)) :
    ∃ e : MixedGraphIso M S
      {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple b ∈ (A.permuteVF order).carrier},
      (∀ a, (e.equiv a).val .vf = a.val .vf ∘ order) ∧ (∀ a, (e.equiv a).val .rv = a.val .rv) := by
  let U := MixedVariables n A.tags
  let To (s : TCsort) : U s → U s := match s with
    | .vf => order
    | .rv => id
  let From (s : TCsort) : U s → U s := match s with
    | .vf => order.symm
    | .rv => id
  let forward (a : SortedAssignment Z U) : SortedAssignment Z U := fun s => a s ∘ To s
  let backward (a : SortedAssignment Z U) : SortedAssignment Z U := fun s => a s ∘ From s
  have left (a : SortedAssignment Z U) : backward (forward a) = a := by
    funext s i
    cases s
    · exact congrArg (a .vf) (order.apply_symm_apply i)
    · rfl
  have right (a : SortedAssignment Z U) : forward (backward a) = a := by
    funext s i
    cases s
    · exact congrArg (a .vf) (order.symm_apply_apply i)
    · rfl
  let D := {a : SortedAssignment Z U | mixedTuple a ∈ A.carrier}
  let E' := {a : SortedAssignment Z U | mixedTuple a ∈ (A.permuteVF order).carrier}
  have domain (a : SortedAssignment Z U) : a ∈ E' ↔ backward a ∈ D := Iff.rfl
  let e : D ≃ E' :=
    { toFun := fun a => ⟨forward a.val,(domain _).2 (by rw [left]; exact a.property)⟩
      invFun := fun a => ⟨backward a.val,(domain _).1 a.property⟩
      left_inv := fun a => Subtype.ext (left a.val)
      right_inv := fun a => Subtype.ext (right a.val) }
  let : Finite A.tags := A.finiteTags
  have g := mixed_projection_graph (M := M) (S := S) To
  refine ⟨⟨e,?_⟩,fun _ => rfl,fun _ => rfl⟩
  apply (g.inter_left A.definable).congr
  intro a b
  exact ⟨fun ⟨eq,h⟩ => ⟨h,eq⟩,fun ⟨h,eq⟩ => ⟨eq,h⟩⟩

theorem RetainedFieldFamily.permuted_iso {A B : RetainedFieldFamily M S n k}
    (f : MixedGraphIso M S
      {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables n B.tags) | mixedTuple b ∈ B.carrier})
    (order : Equiv.Perm (Fin n)) :
    ∃ e : MixedGraphIso M S
      {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ (A.permuteVF order).carrier}
      {b : SortedAssignment Z (MixedVariables n B.tags) | mixedTuple b ∈ (B.permuteVF order).carrier},
      ∀ a, (e.equiv a).val .vf = (f.equiv ((A.permuteVF_iso order).choose.equiv.symm a)).val .vf ∘ order ∧
        (e.equiv a).val .rv = (f.equiv ((A.permuteVF_iso order).choose.equiv.symm a)).val .rv := by
  let a := (A.permuteVF_iso order).choose
  let b := (B.permuteVF_iso order).choose
  let : Finite A.tags := A.finiteTags
  let : Finite B.tags := B.finiteTags
  refine ⟨(a.symm.trans f).trans b,?_⟩
  intro x
  exact ⟨(B.permuteVF_iso order).choose_spec.1 _,(B.permuteVF_iso order).choose_spec.2 _⟩

end GeneralizedEuler.Section5
