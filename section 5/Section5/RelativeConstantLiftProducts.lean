module

public import Section5.RelativeScalarRepresentatives
public import Section5.MixedProductIsomorphisms

/-! The total lift of a relative Cartesian product with a constant
object is the ordinary Cartesian product with its fixed-base lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {b k : ℕ}
  {D : Set (fieldAssignment b X)} {zero : S.carrier .rv}
  (W : RelativeRVObjectScheme M S (MixedVariables b Empty))
  (U : RVObject M S k) (bound : ℕ)

local notation "BaseVars" => MixedVariables b Empty
local notation "C" => (constantRelativeRVObject (P := BaseVars) U bound)

theorem relative_product_with_constant_lift_iso (defD : SortedDefinableOver M S.carrier D) :
    MixedDefinablyEquivalent M S
      (mixedProduct (onlyOver D W.mixedLiftPiece.carrier) (ObjectLift.carrier U))
      (onlyOver D (W.cartesianProduct C).mixedLiftPiece.carrier) := by
  let A := MixedVariables W.data.degree (Fin W.data.arity)
  let B := ObjectLift.Vars U
  let R := MixedVariables (W.data.degree+k) (Fin (W.data.arity+U.arity))
  let reorder (s : TCsort) : SumVariables BaseVars R s ≃ SumVariables (SumVariables BaseVars A) B s :=
    match s with
    | .vf => (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans (Equiv.sumAssoc _ _ _).symm
    | .rv => (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans (Equiv.sumAssoc _ _ _).symm
  let start := mixedProduct (onlyOver D W.mixedLiftPiece.carrier) (ObjectLift.carrier U)
  have defStart := MixedTaggedFamily.mixedProduct_definable (onlyOver_definable defD W.mixedLiftPiece.definable)
    (ObjectLift.definable U)
  have e := mixed_reindex_equivalent reorder start defStart
  have same : onlyOver D (W.cartesianProduct C).mixedLiftPiece.carrier =
      {a : SortedAssignment X (SumVariables BaseVars R) | (fun s => a s ∘ (reorder s).symm) ∈ start} := by
    ext a
    let p : SortedAssignment X BaseVars := fun s => a s ∘ Sum.inl
    let x : SortedAssignment X R := fun s => a s ∘ Sum.inr
    have old : appendAssignments p x = a := by
      funext s i
      cases i <;> rfl
    rw [← old]
    have left : (fun s => appendAssignments p x s ∘ (reorder s).symm ∘ Sum.inl) =
        appendAssignments p (fun s => x s ∘ W.productCoordsLeft C s) := by
      funext s i
      cases s <;> cases i <;> rfl
    have right : (fun s => appendAssignments p x s ∘ (reorder s).symm ∘ Sum.inr) =
        (fun s => x s ∘ W.productCoordsRight C s) := by
      funext s i
      cases s <;> rfl
    change (appendAssignments p x ∈ relativeRVLift (M := M) (W.cartesianProduct C).graph ∧ p ∈ D) ↔
      ((fun s => appendAssignments p x s ∘ (reorder s).symm ∘ Sum.inl) ∈ onlyOver D W.mixedLiftPiece.carrier ∧
      (fun s => appendAssignments p x s ∘ (reorder s).symm ∘ Sum.inr) ∈ ObjectLift.carrier U)
    rw [left,right]
    change (_ ∧ p ∈ D) ↔ (_ ∧ p ∈ D) ∧ _
    have prod := W.cartesianProduct_lift_mem C p x
    have eq := constantRelativeRVObject_fiber_lift_eq U bound p
    have h : appendAssignments p (fun s => x s ∘ W.productCoordsRight C s) ∈
        relativeRVLift (M := M) (C).graph ↔
        (fun s => x s ∘ W.productCoordsRight C s) ∈ ObjectLift.carrier U :=
      Set.ext_iff.1 eq _
    constructor
    · rintro ⟨hm,hp⟩
      obtain ⟨hl,hr⟩ := prod.1 hm
      exact ⟨⟨hl,hp⟩,h.1 hr⟩
    · rintro ⟨⟨hl,hp⟩,hr⟩
      exact ⟨prod.2 ⟨hl,h.2 hr⟩,hp⟩
  exact same.symm ▸ e

variable [TopologicalSpace (X .vf)]

theorem totalLiftObject_product_with_constant
    (defD : SortedDefinableOver M S.carrier D) (v : ∀ p ∈ D, W.valid zero p)
    (valid : ∀ p ∈ D, (C).valid zero p) :
    fieldClass M S ((W.cartesianProduct C).totalLiftObject defD
      (fun p hp => W.cartesianProduct_valid C (v p hp) (valid p hp))) =
      fieldClass M S (W.totalLiftObject defD v) * liftObjectClass ⟨k,U⟩ := by
  let F := W.totalLiftObject defD v
  let G := (W.cartesianProduct C).totalLiftObject defD
    (fun p hp => W.cartesianProduct_valid C (v p hp) (valid p hp))
  have source : MixedDefinablyEquivalent M S (onlyOver D W.mixedLiftPiece.carrier) F.2.carrier :=
    mixed_reindex_equivalent totalCoordinates _ (onlyOver_definable defD W.mixedLiftPiece.definable)
  have target : MixedDefinablyEquivalent M S
      (onlyOver D (W.cartesianProduct C).mixedLiftPiece.carrier) G.2.carrier :=
    mixed_reindex_equivalent totalCoordinates _ (onlyOver_definable defD (W.cartesianProduct C).mixedLiftPiece.definable)
  have f := source.symm.product (MixedDefinablyEquivalent.refl (ObjectLift.definable U))
  have g := relative_product_with_constant_lift_iso W U bound defD
  have comp := f.trans (g.trans target)
  unfold liftObjectClass fieldClass
  rw [← map_mul]
  exact field_scissors_sound M S (.product F ⟨k,liftFieldObject U⟩ G comp)

end GeneralizedEuler.Section5
