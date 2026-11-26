module

public import Section5.RelativeRVObjectSchemes
public import Section5.RelativeTotalClasses
public import Section5.RelativeMixedTotalClasses
public import Section5.FieldScissorRealization

/-! A finite tagged RV family over a fixed field base has a fiber
class and a total VF lift class. Pointwise equality of the lifted
classes implies equality of the total lift classes. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {b : ℕ}

local notation "P" => MixedVariables b Empty

structure RelativeRVFunctionRepresentative (M : SortedStructure L E X) (S : SortedSubstructure M)
    (b : ℕ) (D : Set (fieldAssignment b X)) (zero : S.carrier .rv) where
  count : ℕ
  object : Fin count → RelativeRVObjectScheme M S (MixedVariables b Empty)
  valid : ∀ p ∈ D, ∀ i, (object i).valid zero p

namespace RelativeRVObjectScheme

@[expose] def mixedLiftPiece (W : RelativeRVObjectScheme M S (MixedVariables b Empty)) : RelativeMixedCarrier M S P where
  vars := MixedVariables W.data.degree (Fin W.data.arity)
  finiteVars s := by cases s <;> exact inferInstanceAs (Finite (Fin _))
  carrier := relativeRVLift (M := M) W.graph
  definable := relativeRVLift_definable W.definable

theorem mixedLiftPiece_finite (W : RelativeRVObjectScheme M S (MixedVariables b Empty))
    (p : fieldAssignment b X) {zero : S.carrier .rv} (valid : W.valid zero p)
    (x : Fin W.data.degree → X .vf) :
    {r | (x,r) ∈ mixedTuple '' {u | appendAssignments p u ∈ W.mixedLiftPiece.carrier}}.Finite := by
  have fin := relativeRVLift_finite_fibers (M := M) valid x
  apply fin.subset
  rintro r ⟨u,hu,e⟩
  have hx : u .vf = x := congrArg Prod.fst e
  have hr : u .rv = r := congrArg Prod.snd e
  have eq : u = (fun | .vf => x | .rv => r) := by
    funext s j
    cases s with
    | vf => exact congrFun hx j
    | rv => exact congrFun hr j
  change appendAssignments p (fun | .vf => x | .rv => r) ∈ W.mixedLiftPiece.carrier
  exact (congrArg (fun a : SortedAssignment X (MixedVariables W.data.degree (Fin W.data.arity)) =>
    appendAssignments p a ∈ W.mixedLiftPiece.carrier) eq).mp hu

@[expose] def totalLiftObject [TopologicalSpace (X .vf)]
    (W : RelativeRVObjectScheme M S (MixedVariables b Empty))
    {D : Set (fieldAssignment b X)} {zero : S.carrier .rv}
    (d : SortedDefinableOver M S.carrier D) (valid : ∀ p ∈ D, W.valid zero p) : VFObject M S :=
  mixedFieldObject S (totalMixedSet (onlyOver D W.mixedLiftPiece.carrier))
    (totalMixedSet_definable (onlyOver_definable d W.mixedLiftPiece.definable))
    (totalMixedSet_finite (fun p hp => W.mixedLiftPiece_finite p (valid p hp)))

end RelativeRVObjectScheme

namespace RelativeRVFunctionRepresentative

variable {D : Set (fieldAssignment b X)} {zero : S.carrier .rv}
  (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
  (F G : RelativeRVFunctionRepresentative M S b D zero)

@[expose] def fiberObject (p : D) (i : Fin F.count) : GradedObject M (M.termGenerated (namedTuple S p.val)) :=
  ⟨(F.object i).data.degree,(F.object i).realize zero hzero p.val (F.valid p.val p.property i)⟩

@[expose] def fiberClass (p : D) : RVSemiring M (M.termGenerated (namedTuple S p.val)) :=
  ∑ i, objectClass M _ (F.fiberObject hzero p i)

@[expose] def liftPiece (i : Fin F.count) : RelativeMixedCarrier M S P :=
  (F.object i).mixedLiftPiece

theorem liftPiece_fiber_eq (p : D) (i : Fin F.count) :
    {u | appendAssignments p.val u ∈ (F.liftPiece i).carrier} =
      ObjectLift.carrier (F.fiberObject hzero p i).2 := by
  let W := F.object i
  have valid : RelativeRVWitness W.data.tags W.graph (M.funMap .rvZero (fun j => j.elim0)) W.bound p.val := by
    simpa only [RelativeRVObjectScheme.valid,hzero] using F.valid p.val p.property i
  exact realizedRelativeRVObject_lift_eq p.val W.data.definable W.definable valid

theorem liftPiece_finite (i : Fin F.count) (p : D) (x : Fin (F.object i).data.degree → X .vf) :
    {r | (x,r) ∈ mixedTuple '' {u | appendAssignments p.val u ∈ (F.liftPiece i).carrier}}.Finite :=
  (F.object i).mixedLiftPiece_finite p.val (F.valid p.val p.property i) x

variable [TopologicalSpace (X .vf)]

@[expose] def totalLiftObject (d : SortedDefinableOver M S.carrier D) (i : Fin F.count) : VFObject M S :=
  (F.object i).totalLiftObject d (fun p hp => F.valid p hp i)

theorem totalLiftObject_iso (d : SortedDefinableOver M S.carrier D) (i : Fin F.count) :
    MixedDefinablyEquivalent M S (onlyOver D (F.liftPiece i).carrier) (F.totalLiftObject d i).2.carrier :=
  mixed_reindex_equivalent totalCoordinates _ (onlyOver_definable d (F.liftPiece i).definable)

@[expose] def totalLiftClass (d : SortedDefinableOver M S.carrier D) : VFSemiring M S :=
  ∑ i, fieldClass M S (F.totalLiftObject d i)

theorem totalLiftClass_eq_of_fiber_lift_eq
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver M S.carrier D)
    (eq : ∀ p : D, (∑ i, liftObjectClass (F.fiberObject hzero p i)) =
      ∑ j, liftObjectClass (G.fiberObject hzero p j)) :
    F.totalLiftClass d = G.totalLiftClass d := by
  apply equal_relative_total_classes_of_fiber_iso sat D d F.liftPiece G.liftPiece
    ?_ (F.totalLiftObject d) (G.totalLiftObject d) (F.totalLiftObject_iso d) (G.totalLiftObject_iso d)
  intro p hp
  let U := RelativeMixedCarrier.fibers F.liftPiece p
  let V := RelativeMixedCarrier.fibers G.liftPiece p
  let A (i : Fin F.count) : VFObject M (M.termGenerated (namedTuple S p)) := ⟨(F.fiberObject hzero ⟨p,hp⟩ i).1,
    liftFieldObject (F.fiberObject hzero ⟨p,hp⟩ i).2⟩
  let B (j : Fin G.count) : VFObject M (M.termGenerated (namedTuple S p)) := ⟨(G.fiberObject hzero ⟨p,hp⟩ j).1,
    liftFieldObject (G.fiberObject hzero ⟨p,hp⟩ j).2⟩
  have same := MixedTaggedFamily.equal_field_scissors_iso A B (eq ⟨p,hp⟩)
  have left : U.Iso (MixedTaggedFamily.fieldObjectPieces A) := by
    apply U.iso_retag (MixedTaggedFamily.fieldObjectPieces A) (Equiv.refl (Fin F.count))
    intro i
    change MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p))
      {u | appendAssignments p u ∈ (F.liftPiece i).carrier} (ObjectLift.carrier (F.fiberObject hzero ⟨p,hp⟩ i).2)
    rw [F.liftPiece_fiber_eq hzero ⟨p,hp⟩ i]
    exact .refl (ObjectLift.definable _)
  have right : V.Iso (MixedTaggedFamily.fieldObjectPieces B) := by
    apply V.iso_retag (MixedTaggedFamily.fieldObjectPieces B) (Equiv.refl (Fin G.count))
    intro j
    change MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p))
      {u | appendAssignments p u ∈ (G.liftPiece j).carrier} (ObjectLift.carrier (G.fiberObject hzero ⟨p,hp⟩ j).2)
    rw [G.liftPiece_fiber_eq hzero ⟨p,hp⟩ j]
    exact .refl (ObjectLift.definable _)
  exact U.iso_trans _ _ left (MixedTaggedFamily.iso_trans _ _ _ same (V.iso_symm _ right))

end RelativeRVFunctionRepresentative

end GeneralizedEuler.Section5
