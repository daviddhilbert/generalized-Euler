module

public import Section5.RelativeRVFunctions
public import Section5.RelativeRVBaseCuts
public import Section5.RelativeFubiniClasses

/-! Collect the local graded lifts of the fibers into a single
relative representative by extending each over its base part.
The total lift recovers the original VF class. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {b n m : ℕ}

local notation "P" => MixedVariables b Empty
local notation "U" => MixedVariables n (Fin m)

variable {D : Set (fieldAssignment b X)} {A : Set (SortedAssignment X (SumVariables (MixedVariables b Empty) (MixedVariables n (Fin m))))}
  {zero : S.carrier .rv} (C : GradedLiftCover M S D A zero)

namespace GradedLiftCover

abbrev summands := Σ i : {i // i ∈ C.schemes}, Fin i.val.count

@[expose] def summandIndex : Fin (Fintype.card C.summands) ≃ C.summands := (Fintype.equivFin _).symm

@[expose] def summandObject (i : C.summands) : RelativeRVObjectScheme M S P :=
  let W := i.1.val.object i.2
  ⟨⟨W.degree,W.arity,W.tags,W.tagsDefinable⟩,W.labelGraph,W.labelDefinable,W.bound⟩

@[expose] def representative : RelativeRVFunctionRepresentative M S b D zero where
  count := Fintype.card C.summands
  object j :=
    let i := C.summandIndex j
    (C.summandObject i).restrictBase (C.pieces i.1) (C.definable i.1)
  valid p _ j := by
    let i := C.summandIndex j
    apply (C.summandObject i).restrictBase_valid (C.pieces i.1) (C.definable i.1) zero p
    exact fun hp => ((C.valid i.1 p hp).2.2 i.2).1

theorem piece_subset (i : {i // i ∈ C.schemes}) : C.pieces i ⊆ D := by
  intro p hp
  exact C.covers ▸ Set.mem_iUnion.2 ⟨i,hp⟩

variable [TopologicalSpace (X .vf)]

theorem representative_total_class
    (d : SortedDefinableOver M S.carrier D) (a : SortedDefinableOver M S.carrier A)
    (finite : ∀ p ∈ D, ∀ x : Fin n → X .vf,
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment X U | appendAssignments p u ∈ A}}.Finite) :
    C.representative.totalLiftClass d = fieldClass M S
      (mixedFieldObject S (totalMixedSet (onlyOver D A)) (totalMixedSet_definable (onlyOver_definable d a))
        (totalMixedSet_finite finite)) := by
  obtain ⟨B,iB,eq⟩ := uniform_graded_total_class D d A a finite zero C.schemes C.pieces C.definable
    C.valid C.disjoint C.covers
  refine Eq.trans ?_ eq.symm
  unfold RelativeRVFunctionRepresentative.totalLiftClass
  refine Fintype.sum_equiv C.summandIndex _ _ (fun j => ?_)
  let i := C.summandIndex j
  let R := onlyOver (C.pieces i.1) (relativeRVLift (M := M) (C.summandObject i).graph)
  have covers : onlyOver D (C.representative.liftPiece j).carrier = R := by
    change onlyOver D (relativeRVLift (M := M)
      ((C.summandObject i).restrictBase (C.pieces i.1) (C.definable i.1)).graph) = R
    rw [RelativeRVObjectScheme.restrictBase_relativeLift]
    ext u
    exact ⟨And.left,fun h => ⟨h,C.piece_subset i.1 h.2⟩⟩
  have c := C.representative.totalLiftObject_iso d j
  rw [covers] at c
  exact fieldClass_of_iso M S (c.symm.trans (iB i))

end GradedLiftCover

end GeneralizedEuler.Section5
