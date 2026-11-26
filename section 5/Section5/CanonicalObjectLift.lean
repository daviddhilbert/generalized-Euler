module

public import Section5.LiftClassHom
public import Section5.RVObjectLiftTheorem
public import Section4.LexicographicTags

/-! Supply the object-isomorphism hypothesis of the lift homomorphism
from the fixed-base lift of RV label bijections. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem liftsRVIsomorphisms_of_label_lifts
    (sat : ∀ k (D : ℕ → Set (Fin k → RV0 O)), (∀ i, isRVSet 𝓜 S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (liftSets : ∀ k (A B : Set (labelAssignment k (CanonicalSort O))) (g : A ≃ B),
      SortedDefinableOver 𝓜 S.carrier A → SortedDefinableOver 𝓜 S.carrier B →
      DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ A, (g ⟨a,ha⟩).val = b) →
      (∀ a ∈ A, ∀ j, a .rv j ≠ 0) → (∀ b ∈ B, ∀ j, b .rv j ≠ 0) →
      HasDefinableFieldLift S g) :
    LiftsRVIsomorphisms 𝓜 S := by
  intro k U V h
  obtain ⟨e,he⟩ := h
  let := rvLinearOrder O hO
  obtain ⟨f,_,hf⟩ := ObjectLift.definable_lift_of_rv_object_iso U V e he
    (fun x y => toLex x < toLex y) (fun x y => toLex x < toLex y)
    (fun a b => lt_trans a b) (fun a b => lt_trans a b)
    (fun _ => lt_irrefl _) (fun _ => lt_irrefl _)
    (fun _ _ ne => lt_or_gt_of_ne (fun eq => ne (toLex.injective eq)))
    (fun _ _ ne => lt_or_gt_of_ne (fun eq => ne (toLex.injective eq)))
    (canonical_lex_definable O hO power S) (canonical_lex_definable O hO power S)
    (sat k) (liftSets k)
  exact ⟨f,hf⟩

end GeneralizedEuler.Section5
