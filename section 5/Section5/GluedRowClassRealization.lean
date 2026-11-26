module

public import Section5.GluedRowCoordinateGraphs
import all Section4.Objects

/-! Identify a glued row with an ordinary graded object by an exact
description of its carrier after reindexing the RV coordinates. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h t d e : ℕ} {I : RelativeRVIndex M S h t}

theorem RelativeRVRow.gluedClass_realized (A : RelativeRVRow I d) (W : RVObject M S e)
    (degree : e = t+d) (arity : W.arity = h+A.arity)
    (tags : ∀ x : Fin (h+A.arity) → X .rv,
      x ∘ Fin.cast arity ∈ W.carrier ↔ x ∈ gluedRVTags I.labels A.tags) :
    A.gluedClass = objectClass M S ⟨e,W⟩ := by
  subst e
  have iso := rv_cast_carrier_equiv W arity _ tags
  exact scissors_sound M S (.iso _ _ (A.object_carrier_equiv.trans iso.symm))

end GeneralizedEuler.Section5
