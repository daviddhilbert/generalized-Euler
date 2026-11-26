module

public import Section5.ObjectLiftRestrictions
public import Section5.BlowupOverlapClasses

/-! The overlap, each exclusive locus, and the exterior are transported
by the original RV isomorphism. The structure maps may differ. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder
open ObjectLift (tagImage tagPreimage)

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}
  {U V : RVObject M S k}
  (e : U.carrier ≃ V.carrier)
  (A : Set (Fin U.arity → X .rv)) (B : Set (Fin V.arity → X .rv))

private theorem image_mem_iff (a : U.carrier) : (e a).val ∈ tagImage e A ↔ a.val ∈ A := by
  constructor
  · rintro ⟨a',ha,eq⟩
    have same : a' = a := e.injective (Subtype.ext eq)
    exact same ▸ ha
  · intro ha
    exact ⟨a,ha,rfl⟩

private theorem preimage_mem_iff (a : U.carrier) : a.val ∈ tagPreimage e B ↔ (e a).val ∈ B := by
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨a.property,h⟩⟩

private theorem restrict_transport (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
    {C : Set (Fin U.arity → X .rv)} {D : Set (Fin V.arity → X .rv)}
    (subC : C ⊆ U.carrier) (subD : D ⊆ V.carrier) (defC : isRVSet M S C)
    (matchMem : ∀ a : U.carrier, a.val ∈ C ↔ (e a).val ∈ D) :
    RVDefinablyEquivalent M S.carrier C D := by
  have h := ObjectLift.restrictIso_definable e eDef subC defC
  have eq : D = tagImage e C := by
    ext b
    constructor
    · intro hb
      let v : V.carrier := ⟨b,subD hb⟩
      have he := congrArg Subtype.val (e.apply_symm_apply v)
      exact ⟨e.symm v,(matchMem _).2 (he.symm ▸ hb),he⟩
    · rintro ⟨a,ha,rfl⟩
      exact (matchMem a).1 ha
  rw [eq]
  exact ⟨ObjectLift.restrictIso e eDef subC defC,h⟩

/-- Isomorphisms on the four loci used in the one-step comparison. -/
theorem blowup_loci_transport
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
    (subA : A ⊆ U.carrier) (subB : B ⊆ V.carrier)
    (defA : isRVSet M S A) (defB : isRVSet M S B) :
    RVDefinablyEquivalent M S.carrier (A ∩ tagPreimage e B) (tagImage e A ∩ B) ∧
    RVDefinablyEquivalent M S.carrier (A \ tagPreimage e B) (tagImage e A \ B) ∧
    RVDefinablyEquivalent M S.carrier (tagPreimage e B \ A) (B \ tagImage e A) ∧
    RVDefinablyEquivalent M S.carrier (U.carrier \ (A ∪ tagPreimage e B))
      (V.carrier \ (tagImage e A ∪ B)) := by
  have defPre := ObjectLift.tagPreimage_definable e eDef defB
  have subPre : tagPreimage e B ⊆ U.carrier := fun _ h => h.1
  have subImage := ObjectLift.tagImage_subset e A
  have hA (a : U.carrier) := image_mem_iff e A a
  have hB (a : U.carrier) := preimage_mem_iff e B a
  refine ⟨restrict_transport e eDef (fun _ h => subA h.1) (fun _ h => subB h.2) (defA.inter defPre) ?_,
    restrict_transport e eDef (fun _ h => subA h.1) (fun _ h => subImage h.1) (defA.inter defPre.compl) ?_,
    restrict_transport e eDef (fun _ h => subPre h.1) (fun _ h => subB h.1) (defPre.inter defA.compl) ?_,
    restrict_transport e eDef (fun _ h => h.1) (fun _ h => h.1)
      (U.definable.inter (defA.union defPre).compl) ?_⟩
  · intro a
    exact and_congr (hA a).symm (hB a)
  · intro a
    exact and_congr (hA a).symm (not_congr (hB a))
  · intro a
    exact and_congr (hB a) (not_congr (hA a).symm)
  · intro a
    exact and_congr (iff_of_true a.property (e a).property) (not_congr (or_congr (hA a).symm (hB a)))

end GeneralizedEuler.Section5
