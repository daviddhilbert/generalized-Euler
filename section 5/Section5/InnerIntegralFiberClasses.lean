module

public import Section5.InnerIntegralRepresentatives
public import Section5.RelativePositiveIntegration

/-! The fibers of the inner-integral representative have the
positive integral of the corresponding VF fiber. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {b n m : ℕ}
  [TopologicalSpace (X .vf)]

local notation "P" => MixedVariables b Empty
local notation "U" => MixedVariables n (Fin m)

theorem GradedLiftCover.representative_fiber_lift_class
    {D : Set (fieldAssignment b X)}
    {A : Set (SortedAssignment X (SumVariables (MixedVariables b Empty) (MixedVariables n (Fin m))))}
    {zero : S.carrier .rv} (C : GradedLiftCover M S D A zero)
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (a : SortedDefinableOver M S.carrier A) (p : D)
    (finite : ∀ x : Fin n → X .vf,
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment X U | appendAssignments p.val u ∈ A}}.Finite) :
    (∑ j, liftObjectClass (C.representative.fiberObject hzero p j)) =
      fieldClass M (M.termGenerated (namedTuple S p.val))
        (mixedFieldObject _ _ (definable_scheme_at_fiber p.val A a) finite) := by
  classical
  let T := M.termGenerated (namedTuple S p.val)
  let F := mixedFieldObject T _ (definable_scheme_at_fiber p.val A a) finite
  let R (j : Fin C.representative.count) :=
    let i := C.summandIndex j
    onlyOver (C.pieces i.1) (i.1.val.source i.2)
  let B (j : Fin C.representative.count) : Set (SortedAssignment X U) :=
    {u | appendAssignments p.val u ∈ R j}
  have defB (j : Fin C.representative.count) : SortedDefinableOver M T.carrier (B j) := by
    let i := C.summandIndex j
    exact definable_scheme_at_fiber p.val _ (onlyOver_definable (C.definable i.1) (i.1.val.sourceDefinable i.2))
  obtain ⟨disjoint,cover,_⟩ := uniform_graded_lift_total_bijections D A zero C.schemes C.pieces C.definable
    C.valid C.disjoint C.covers
  have sub (j : Fin C.representative.count) : B j ⊆ F.2.carrier := by
    intro u hu
    have h : appendAssignments p.val u ∈ onlyOver D A :=
      cover ▸ Set.mem_iUnion.2 ⟨C.summandIndex j,hu⟩
    exact h.1
  have disj : Pairwise (fun j k => Disjoint (B j) (B k)) := by
    intro j k ne
    exact Set.disjoint_left.2 (fun _ hj hk =>
      Set.disjoint_left.1 (disjoint (fun eq => ne (C.summandIndex.injective eq))) hj hk)
  have all : (⋃ j, B j) = F.2.carrier := by
    ext u
    constructor
    · intro h
      obtain ⟨j,hj⟩ := Set.mem_iUnion.1 h
      exact sub j hj
    · intro hu
      have h : appendAssignments p.val u ∈ onlyOver D A := ⟨hu,p.property⟩
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 (cover.symm ▸ h)
      refine Set.mem_iUnion.2 ⟨C.summandIndex.symm i,?_⟩
      change appendAssignments p.val u ∈
        onlyOver (C.pieces (C.summandIndex (C.summandIndex.symm i)).1)
          ((C.summandIndex (C.summandIndex.symm i)).1.val.source (C.summandIndex (C.summandIndex.symm i)).2)
      rwa [Equiv.apply_symm_apply]
  have part := fieldClass_partition F B defB sub disj all
  refine (Finset.sum_congr rfl (fun j _ => ?_)).trans part.symm
  let i := C.summandIndex j
  let W := i.1.val.object i.2
  let K := C.representative.fiberObject hzero p j
  apply fieldClass_of_iso M T (A := ⟨K.1,liftFieldObject K.2⟩)
    (B := restrictedFieldObject F (B j) (sub j) (defB j))
  apply MixedDefinablyEquivalent.symm
  have liftEq := C.representative.liftPiece_fiber_eq hzero p j
  change MixedDefinablyEquivalent M T (B j) (ObjectLift.carrier K.2)
  rw [← liftEq]
  by_cases hp : p.val ∈ C.pieces i.1
  · have h := ((C.valid i.1 p.val hp).2.2 i.2).2
    let Y := {u : SortedAssignment X U | appendAssignments p.val u ∈ i.1.val.source i.2}
    let V := {v : SortedAssignment X (MixedVariables W.degree (Fin W.arity)) |
      appendAssignments p.val v ∈ relativeRVLift (M := M) W.labelGraph}
    have source (u : SortedAssignment X U) : u ∈ B j ↔ u ∈ Y := onlyOver_fiber_iff hp u
    let restricted : Set (SortedAssignment X (SumVariables P (MixedVariables W.degree (Fin W.arity)))) :=
      (C.representative.liftPiece j).carrier
    have resEq : restricted = onlyOver (C.pieces i.1) (relativeRVLift (M := M) W.labelGraph) :=
      (C.summandObject i).restrictBase_relativeLift (C.pieces i.1) (C.definable i.1)
    have target (v : SortedAssignment X (MixedVariables W.degree (Fin W.arity))) :
        appendAssignments p.val v ∈ restricted ↔ v ∈ V := by
      rw [resEq]
      exact onlyOver_fiber_iff hp v
    let e := (Equiv.subtypeEquivRight source).trans (h.equiv.trans (Equiv.subtypeEquivRight target).symm)
    refine ⟨e,(definable_relation_scheme_at_fiber p.val _ W.liftGraphDefinable).congr ?_⟩
    intro u v
    constructor
    · intro hh
      have hu := (h.1 u).2 ⟨v,hh⟩
      exact ⟨(source u).2 hu,(h.equiv_graph ⟨u,hu⟩ v).1 hh⟩
    · rintro ⟨hu,hh⟩
      exact (h.equiv_graph ⟨u,(source u).1 hu⟩ v).2 hh
  · let Z₀ := {v | appendAssignments p.val v ∈ (C.representative.liftPiece j).carrier}
    let : IsEmpty (B j) := ⟨fun u => hp u.property.2⟩
    let : IsEmpty Z₀ := ⟨fun v => hp v.property.2⟩
    refine ⟨Equiv.equivOfIsEmpty (B j) Z₀,?_⟩
    exact ⟨.falsum,fun _ => ⟨fun ⟨hu,_⟩ => (hp hu.2).elim,False.elim⟩⟩

end GeneralizedEuler.Section5
