module

public import Section4.FiniteScissors
import all Section4.FiniteScissors

/-! Compute the graded class on intersecting blowup loci. The underlying
intersection is compared in the lowered degree and after adjoining the
same nonzero multipliers. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}

private theorem class_cut (U : RVObject M S k)
    (A B : Set (Fin U.arity → X .rv))
    (a : A ⊆ U.carrier) (b : B ⊆ U.carrier)
    (da : isRVSet M S A) (db : isRVSet M S B)
    (sep : Disjoint A B) (cover : A ∪ B = U.carrier) :
    objectClass M S ⟨k,U⟩ =
      objectClass M S ⟨k,U.restrict a da⟩ + objectClass M S ⟨k,U.restrict b db⟩ := by
  apply scissors_sound M S
  exact RVRelation.cut U (U.restrict a da) (U.restrict b db) A B da db sep cover
    ⟨Equiv.refl _,definable_identity_label M S da⟩
    ⟨Equiv.refl _,definable_identity_label M S db⟩

/-- Each lower-degree object comes from blowing up the entire first
or second locus. The paired overlap isomorphism also identifies the
positive strata after multiplying by the infinitesimal multiplier class. -/
theorem overlap_blowup_strata_classes (ZA ZB : RVObject M S k)
    (A : Set (Fin ZA.arity → X .rv)) (B : Set (Fin ZB.arity → X .rv))
    (subA : A ⊆ ZA.carrier) (subB : B ⊆ ZB.carrier)
    (defA : isRVSet M S A) (defB : isRVSet M S B)
    (shared : RVDefinablyEquivalent M S.carrier A B) (q : RVSemiring M S) :
    let ZAonly := ZA.restrict (A := ZA.carrier \ A) (fun _ h => h.1) (ZA.definable.inter defA.compl)
    let ZBonly := ZB.restrict (A := ZB.carrier \ B) (fun _ h => h.1) (ZB.definable.inter defB.compl)
    let cls := fun Z : RVObject M S k => objectClass M S ⟨k,Z⟩
    (cls ZA + cls ZBonly = cls ZB + cls ZAonly) ∧
    (cls ZA * q + cls ZBonly * q = cls ZB * q + cls ZAonly * q) := by
  intro ZAonly ZBonly cls
  let ZAover := ZA.restrict subA defA
  let ZBover := ZB.restrict subB defB
  have hA : cls ZA = cls ZAover + cls ZAonly := by
    apply class_cut ZA A (ZA.carrier \ A) subA (fun _ h => h.1) defA (ZA.definable.inter defA.compl)
    · exact Set.disjoint_left.2 fun _ x y => y.2 x
    · ext x
      change x ∈ A ∨ (x ∈ ZA.carrier ∧ x ∉ A) ↔ x ∈ ZA.carrier
      by_cases h : x ∈ A
      · simp [h, subA h]
      · simp [h]
  have hB : cls ZB = cls ZBover + cls ZBonly := by
    apply class_cut ZB B (ZB.carrier \ B) subB (fun _ h => h.1) defB (ZB.definable.inter defB.compl)
    · exact Set.disjoint_left.2 fun _ x y => y.2 x
    · ext x
      change x ∈ B ∨ (x ∈ ZB.carrier ∧ x ∉ B) ↔ x ∈ ZB.carrier
      by_cases h : x ∈ B
      · simp [h, subB h]
      · simp [h]
  have same : cls ZAover = cls ZBover := scissors_sound M S (RVRelation.iso _ _ shared)
  have zero : cls ZA + cls ZBonly = cls ZB + cls ZAonly := by
    rw [hA,hB,same,add_assoc,add_assoc,add_comm (cls ZAonly)]
  exact ⟨zero,by rw [← add_mul,← add_mul,zero]⟩

end GeneralizedEuler.Section5
