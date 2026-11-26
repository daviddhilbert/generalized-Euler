module

public import Section5.FieldScissors
public import Section4.FiniteScissors
import all Section2.Dimension

/-! A finite definable partition gives a finite sum in the filtered
VF scissor semiring, with each part inheriting the dimension bound. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} [TopologicalSpace (X .vf)]

theorem vfDimension_mono {n : ℕ} {Y : Type*} {D B : Set ((Fin n → X .vf) × Y)} (h : D ⊆ B) :
    vfDimension D ≤ vfDimension B := by
  classical
  unfold vfDimension
  apply Finset.sup_mono
  intro i hi
  obtain ⟨hn,y,p,hy⟩ := Finset.mem_filter.1 hi
  exact Finset.mem_filter.2 ⟨hn,y,p,hy.mono (interior_mono (Set.image_mono (fun _ hx => h hx)))⟩

@[expose] def restrictedFieldObject (A : VFObject M S)
    (D : Set (SortedAssignment X (VFVars M S A))) (sub : D ⊆ A.2.carrier)
    (defD : SortedDefinableOver M S.carrier D) : VFObject M S :=
  ⟨A.1,
    { vfArity := A.2.vfArity
      rvArity := A.2.rvArity
      carrier := D
      definable := defD
      dimension := (vfDimension_mono (Set.image_mono sub)).trans A.2.dimension
      finiteFibers := fun b => (A.2.finiteFibers b).subset (fun _ hr => Set.image_mono sub hr) }⟩

theorem fieldClass_partition {I : Type} [Fintype I] (A : VFObject M S)
    (D : I → Set (SortedAssignment X (VFVars M S A)))
    (hD : ∀ i, SortedDefinableOver M S.carrier (D i))
    (sub : ∀ i, D i ⊆ A.2.carrier)
    (disjoint : Pairwise (fun i j => Disjoint (D i) (D j))) (cover : ⋃ i, D i = A.2.carrier) :
    fieldClass M S A = ∑ i, fieldClass M S (restrictedFieldObject A (D i) (sub i) (hD i)) := by
  let P (D : Set (SortedAssignment X (VFVars M S A))) :=
    D ⊆ A.2.carrier ∧ SortedDefinableOver M S.carrier D
  let cls (D) (h : P D) := fieldClass M S (restrictedFieldObject A D h.1 h.2)
  have empty : P ∅ := ⟨Set.empty_subset _,⟨.falsum,fun _ => Iff.rfl⟩⟩
  have zero : cls ∅ empty = 0 := field_scissors_sound M S (.zero _ rfl)
  have union {D E} (hd : P D) (he : P E) : P (D ∪ E) :=
    ⟨Set.union_subset hd.1 he.1,hd.2.union he.2⟩
  have cut (C E) (hc : P C) (he : P E) (disj : Disjoint C E) :
      cls (C ∪ E) (union hc he) = cls C hc + cls E he := by
    unfold cls fieldClass
    rw [← map_add]
    exact field_scissors_sound M S (.cut _ _ _ C E hc.2 he.2 disj rfl
      (MixedDefinablyEquivalent.refl hc.2) (MixedDefinablyEquivalent.refl he.2))
  obtain ⟨h,hs⟩ := finite_scissor_sum cls empty zero @union cut D (fun i => ⟨sub i,hD i⟩) disjoint
  refine Eq.trans ?_ hs
  apply fieldClass_of_iso M S
  change MixedDefinablyEquivalent M S A.2.carrier (⋃ i, D i)
  rw [cover]
  exact MixedDefinablyEquivalent.refl A.2.definable

end GeneralizedEuler.Section5
