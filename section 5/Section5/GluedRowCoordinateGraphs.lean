module

public import Section5.RVCoordinateGraphs
public import Section5.RelativeRVRows
import all Section4.Objects

/-! A glued row recovers an ordinary RV object when the retained
index is already a coordinate projection of its original tags. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h t d : ℕ} {I : RelativeRVIndex M S h t}

theorem RelativeRVRow.gluedClass_eq_of_projection (A : RelativeRVRow I d) (W : RVObject M S (t+d))
    (arity : W.arity = A.arity) (sel : Fin h → Fin A.arity)
    (matchTags : ∀ (p : Fin h → X .rv) (b : Fin A.arity → X .rv),
      (p ∈ I.labels ∧ appendAssignments (rvTupleAssignment p) (rvTupleAssignment b) ∈ A.tags) ↔
        b ∘ Fin.cast arity ∈ W.carrier ∧ p = b ∘ sel) :
    A.gluedClass = objectClass M S ⟨t+d,W⟩ := by
  let C := {x : Fin A.arity → X .rv | x ∘ Fin.cast arity ∈ W.carrier}
  have dC : isRVSet M S C := isRVSet_precomp (Fin.cast arity) W.definable
  have cIso := rv_cast_carrier_equiv W arity C (fun _ => Iff.rfl)
  let G := {b : Fin h ⊕ Fin A.arity → X .rv | b ∘ Sum.inr ∈ C ∧ b ∘ Sum.inl = b ∘ Sum.inr ∘ sel}
  have cG : RVDefinablyEquivalent M S.carrier C G := rv_equiv_record_coordinates C dC sel
  have dG := isRVSet_of_rvEquiv (M := M) (S := S) cG
  let idx : Fin (h+A.arity) ≃ Fin h ⊕ Fin A.arity := finSumFinEquiv.symm
  have pack := rv_reindex_equivalent M S idx G dG
  have eq : {b | b ∘ idx.symm ∈ G} = gluedRVTags I.labels A.tags := by
    ext b
    exact (matchTags (b ∘ rvHead) (b ∘ rvTail)).symm
  rw [eq] at pack
  exact scissors_sound M S (.iso _ _ (A.object_carrier_equiv.trans ((cIso.trans (cG.trans pack)).symm)))

end GeneralizedEuler.Section5
