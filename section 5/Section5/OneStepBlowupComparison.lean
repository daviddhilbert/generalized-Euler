module

public import Section5.BlowupLocusTransport
public import Section5.BlowupClassProducts
import all Section4.FiniteScissors

/-! The first commuting square for two elementary blowups in one degree,
with their loci transported by a fixed-base starting isomorphism. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder
open ObjectLift (tagImage tagPreimage restrictTags)

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k : ℕ}
  {U V : RVObject (canonicalStructure (L := L) O hO power) S (k+1)}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Restricting an elementary presentation to an exclusive locus
preserves the deletion bound. -/
theorem finite_deletion_on_restricted_locus (U : RVObject 𝓜 S (k+1)) (i : Fin (k+1))
    (D : Set (Fin U.arity → RV0 O)) (subD : D ⊆ U.carrier) (defD : isRVSet 𝓜 S D)
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ i.succAbove = t}.Finite) :
    ∀ t : Fin k → RV0 O, {u ∈ Set.range (restrictTags U subD defD).label | u ∘ i.succAbove = t}.Finite := by
  intro t
  apply (finiteDelete t).subset
  rintro u ⟨⟨a,rfl⟩,h⟩
  exact ⟨⟨⟨a.val,subD a.property⟩,rfl⟩,h⟩

/-- Retain each first blowup on its own locus. Transport the other
blowup on the exclusive part of its locus and compare both resulting
degrees by scissors. -/
theorem one_step_blowup_comparison
    (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver 𝓜 S.carrier (rvGraph (fun a => (e a).val)))
    (A : Set (Fin U.arity → RV0 O)) (B : Set (Fin V.arity → RV0 O))
    (subA : A ⊆ U.carrier) (subB : B ⊆ V.carrier)
    (defA : isRVSet 𝓜 S A) (defB : isRVSet 𝓜 S B)
    (i j : Fin (k+1))
    (finiteA : ∀ t : Fin k → RV0 O,
      {u ∈ Set.range (restrictTags U subA defA).label | u ∘ i.succAbove = t}.Finite)
    (finiteB : ∀ t : Fin k → RV0 O,
      {u ∈ Set.range (restrictTags V subB defB).label | u ∘ j.succAbove = t}.Finite)
    (hneg : rv O (-1) ∈ S.carrier .rv) :
    let pre := ObjectLift.tagPreimage_definable e eDef defB
    let im := ObjectLift.tagImage_definable e eDef defA
    let ZA := zeroBlowupObject (restrictTags U subA defA) i finiteA
    let ZB := zeroBlowupObject (restrictTags V subB defB) j finiteB
    let ZAonly := restrictTags ZA (A := A \ tagPreimage (U := U) (V := V) e B)
      (fun _ h => h.1) (defA.inter pre.compl)
    let ZBonly := restrictTags ZB (A := B \ tagImage (U := U) (V := V) e A)
      (fun _ h => h.1) (defB.inter im.compl)
    let OU := restrictTags U (A := U.carrier \ (A ∪ tagPreimage (U := U) (V := V) e B)) (fun _ h => h.1)
      (U.definable.inter (defA.union pre).compl)
    let OV := restrictTags V (A := V.carrier \ (tagImage (U := U) (V := V) e A ∪ B)) (fun _ h => h.1)
      (V.definable.inter (im.union defB).compl)
    let cls := objectClass 𝓜 S
    let q := cls ⟨1,multiplierObject O hO power S hneg⟩
    let left := cls ⟨k,ZA⟩ + cls ⟨k,ZBonly⟩
    let right := cls ⟨k,ZB⟩ + cls ⟨k,ZAonly⟩
    left = right ∧ cls ⟨k+1,OU⟩ + left * q = cls ⟨k+1,OV⟩ + right * q := by
  intro pre im ZA ZB ZAonly ZBonly OU OV cls q left right
  obtain ⟨shared,_,_,exterior⟩ := blowup_loci_transport e A B eDef subA subB defA defB
  have cutA := show ZA.carrier \ (A ∩ tagPreimage (U := U) (V := V) e B) = A \ tagPreimage (U := U) (V := V) e B by
    change A \ (A ∩ tagPreimage (U := U) (V := V) e B) = A \ tagPreimage (U := U) (V := V) e B
    ext x
    change (x ∈ A ∧ ¬ (x ∈ A ∧ x ∈ tagPreimage (U := U) (V := V) e B)) ↔ (x ∈ A ∧ x ∉ tagPreimage (U := U) (V := V) e B)
    exact and_congr_right fun h => by simp [h]
  have cutB := show ZB.carrier \ (tagImage (U := U) (V := V) e A ∩ B) = B \ tagImage (U := U) (V := V) e A by
    change B \ (tagImage (U := U) (V := V) e A ∩ B) = B \ tagImage (U := U) (V := V) e A
    ext x
    change (x ∈ B ∧ ¬ (x ∈ tagImage (U := U) (V := V) e A ∧ x ∈ B)) ↔ (x ∈ B ∧ x ∉ tagImage (U := U) (V := V) e A)
    exact and_congr_right fun h => by simp [h]
  have overlap := (overlap_blowup_strata_classes ZA ZB (A ∩ tagPreimage (U := U) (V := V) e B) (tagImage (U := U) (V := V) e A ∩ B)
    (fun _ h => h.1) (fun _ h => h.2) (defA.inter pre) (im.inter defB) shared q).1
  let XA := ZA.restrict (A := ZA.carrier \ (A ∩ tagPreimage (U := U) (V := V) e B)) (fun _ h => h.1)
    (ZA.definable.inter (defA.inter pre).compl)
  let XB := ZB.restrict (A := ZB.carrier \ (tagImage (U := U) (V := V) e A ∩ B)) (fun _ h => h.1)
    (ZB.definable.inter (im.inter defB).compl)
  have reA : cls ⟨k,XA⟩ = cls ⟨k,ZAonly⟩ := by
    apply scissors_sound 𝓜 S
    apply RVRelation.iso _ _
    change RVDefinablyEquivalent 𝓜 S.carrier (ZA.carrier \ (A ∩ tagPreimage (U := U) (V := V) e B)) (A \ tagPreimage (U := U) (V := V) e B)
    rw [cutA]
    exact ⟨Equiv.refl _,definable_identity_label 𝓜 S (defA.inter pre.compl)⟩
  have reB : cls ⟨k,XB⟩ = cls ⟨k,ZBonly⟩ := by
    apply scissors_sound 𝓜 S
    apply RVRelation.iso _ _
    change RVDefinablyEquivalent 𝓜 S.carrier (ZB.carrier \ (tagImage (U := U) (V := V) e A ∩ B)) (B \ tagImage (U := U) (V := V) e A)
    rw [cutB]
    exact ⟨Equiv.refl _,definable_identity_label 𝓜 S (defB.inter im.compl)⟩
  have o : cls ⟨k+1,OU⟩ = cls ⟨k+1,OV⟩ :=
    scissors_sound 𝓜 S (RVRelation.iso _ _ exterior)
  change cls ⟨k,ZA⟩ + cls ⟨k,XB⟩ = cls ⟨k,ZB⟩ + cls ⟨k,XA⟩ at overlap
  rw [reA,reB] at overlap
  have eq : left = right := overlap
  exact ⟨eq,by rw [o,eq]⟩

end GeneralizedEuler.Section5
