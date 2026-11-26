module

public import Section5.FieldScissors

/-! Enlarging the named base preserves field objects, definable
bijections, and the relations of the positive VF scissor semiring. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S T : SortedSubstructure M}

theorem MixedDefinablyEquivalent.extendBase {U V : TCsort → Type}
    {A : Set (SortedAssignment X U)} {B : Set (SortedAssignment X V)}
    (iso : MixedDefinablyEquivalent M S A B) (sub : ∀ s, S.carrier s ⊆ T.carrier s) :
    MixedDefinablyEquivalent M T A B := by
  obtain ⟨e,de⟩ := iso
  exact ⟨e,de.mono sub⟩

variable [TopologicalSpace (X .vf)] (sub : ∀ s, S.carrier s ⊆ T.carrier s)

@[expose] def extendFieldObject (A : VFObject M S) : VFObject M T where
  fst := A.1
  snd :=
    { vfArity := A.2.vfArity
      rvArity := A.2.rvArity
      carrier := A.2.carrier
      definable := A.2.definable.mono sub
      dimension := A.2.dimension
      finiteFibers := A.2.finiteFibers }

private theorem fieldBaseWeights_respect (a b : VFExpression M S) (h : VFRelation M S a b) :
    MvPolynomial.eval₂ (Nat.castRingHom (VFSemiring M T)) (fun A => fieldClass M T (extendFieldObject sub A)) a =
    MvPolynomial.eval₂ (Nat.castRingHom (VFSemiring M T)) (fun A => fieldClass M T (extendFieldObject sub A)) b := by
  cases h with
  | iso A B e =>
    simpa only [MvPolynomial.eval₂_X] using
      fieldClass_of_iso M T (A := extendFieldObject sub A) (B := extendFieldObject sub B) (e.extendBase sub)
  | zero A empty =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_zero,fieldClass,← map_zero (ringConGen (VFRelation M T)).mk']
    exact field_scissors_sound M T (.zero (extendFieldObject sub A) empty)
  | one A point =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_one,fieldClass,← map_one (ringConGen (VFRelation M T)).mk']
    exact field_scissors_sound M T (.one (extendFieldObject sub A) point)
  | cut A B C D F d e disj cov iD iF =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_add,fieldClass,← map_add]
    exact field_scissors_sound M T (.cut (extendFieldObject sub A) (extendFieldObject sub B)
      (extendFieldObject sub C) D F (d.mono sub) (e.mono sub) disj cov (iD.extendBase sub) (iF.extendBase sub))
  | product A B C e =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul,fieldClass,← map_mul]
    exact field_scissors_sound M T (.product (extendFieldObject sub A) (extendFieldObject sub B)
      (extendFieldObject sub C) (e.extendBase sub))

def fieldClassBaseExtension : VFSemiring M S →+* VFSemiring M T :=
  (ringConGen (VFRelation M S)).lift
    (MvPolynomial.eval₂Hom (Nat.castRingHom (VFSemiring M T)) (fun A => fieldClass M T (extendFieldObject sub A)))
    (RingCon.ringConGen_le.mpr (fieldBaseWeights_respect sub))

theorem fieldClassBaseExtension_class (A : VFObject M S) :
    fieldClassBaseExtension sub (fieldClass M S A) = fieldClass M T (extendFieldObject sub A) := by
  change MvPolynomial.eval₂ (Nat.castRingHom (VFSemiring M T)) (fun A => fieldClass M T (extendFieldObject sub A))
    (MvPolynomial.X A) = _
  exact MvPolynomial.eval₂_X _ _ _

end GeneralizedEuler.Section5
