module

public import Section4.WholeFiberRelation
import all Section4.FiniteScissors
import all Section4.WholeFiberRelation

/-! Specializing any finite block of RV coordinates to an old tuple
preserves definability over the same two-sorted base. -/
public section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {J : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure J F Z} {S : SortedSubstructure M}
  {I H : Type} [Finite H]

theorem oldTuple_definable (a : H → Z .rv) (old : ∀ j, a j ∈ S.carrier .rv) :
    isRVSet M S {x : H → Z .rv | x = a} := by
  unfold isRVSet
  convert SortedDefinableOver.iInter (fun j : H =>
    SortedDefinableOver.coordinate_eq_parameter (M := M) (A := S.carrier) (Var := RVVariables H) .rv j ⟨a j,old j⟩) using 1
  ext x
  simp [funext_iff]

theorem rv_slice_at_base {D : Set (I ⊕ H → Z .rv)} (hd : isRVSet M S D)
    (a : H → Z .rv) (old : ∀ j, a j ∈ S.carrier .rv) :
    isRVSet M S {u : I → Z .rv | Sum.elim u a ∈ D} := by
  have h := isRVSet_project (isRVSet_inter hd (isRVSet_precomp Sum.inr (oldTuple_definable a old)))
  convert h using 1
  ext x
  exact ⟨fun hx => ⟨a,hx,rfl⟩,fun ⟨y,hy,eq⟩ => (show y = a from eq) ▸ hy⟩

end GeneralizedEuler.Section4
