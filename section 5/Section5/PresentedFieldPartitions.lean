module

public import Section5.FieldClassPartitions
public import Section5.UnaryFactorizationComparison

/-! A finite definable partition of a mixed set can be transported
to any fixed-base VF presentation of that set. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} [TopologicalSpace (X .vf)]
  {U : TCsort → Type} [Finite (U .vf)] [Finite (U .rv)] {I : Type} [Fintype I]

theorem fieldClass_eq_sum_of_presented_partition
    {A : Set (SortedAssignment X U)} (P : VFObject M S) (iso : MixedDefinablyEquivalent M S A P.2.carrier)
    (D : I → Set (SortedAssignment X U)) (d : ∀ i, SortedDefinableOver M S.carrier (D i))
    (sub : ∀ i, D i ⊆ A) (disj : Pairwise (fun i j => Disjoint (D i) (D j))) (cover : (⋃ i, D i) = A) :
    ∃ Q : I → VFObject M S, (∀ i, MixedDefinablyEquivalent M S (D i) (Q i).2.carrier) ∧
      fieldClass M S P = ∑ i, fieldClass M S (Q i) := by
  obtain ⟨e,g⟩ := iso
  let f : MixedGraphIso M S A P.2.carrier := ⟨e,g⟩
  obtain ⟨disjoint,covers⟩ := f.rangeOver_partition D sub disj cover
  let R (i : I) := f.rangeOver (sub i)
  let dR (i : I) := (f.restrict (sub i) (d i)).target_definable (d i)
  have subR (i : I) : R i ⊆ P.2.carrier := by
    rintro _ ⟨x,rfl⟩
    exact (f.equiv ⟨x.val,sub i x.property⟩).property
  let Q (i : I) := restrictedFieldObject P (R i) (subR i) (dR i)
  exact ⟨Q,fun i => (f.restrict (sub i) (d i)).equivalent,
    fieldClass_partition P R dR subR disjoint covers⟩

end GeneralizedEuler.Section5
