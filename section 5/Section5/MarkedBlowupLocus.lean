module

public import Section5.ElementaryClassSteps
public import Section5.GradedClassCuts
import all Section4.Objects

/-! Mark the blowup center among the source tags, and cut its
lower-degree presentation using the graph on the raised degree. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cls" => objectClass 𝓜 S
local notation "p" => residuePointClass O hO power S

@[expose] def markBlowupLocus {I : Type} (W : GradedObject 𝓜 S)
    (A : I → GradedObject 𝓜 S) : Option I → GradedObject 𝓜 S :=
  fun i => i.elim ⟨W.1+1,appendUnitLabel W.2 (canonical_rvUnit_nonzero O hO power)⟩ A

theorem markBlowupLocus_class {I : Type} [Fintype I] (W : GradedObject 𝓜 S)
    (A : I → GradedObject 𝓜 S) :
    (∑ i, cls (markBlowupLocus O hO power S W A i)) = cls W * p + ∑ i, cls (A i) := by
  rw [Fintype.sum_option]
  exact congrArg (· + ∑ i, cls (A i)) (appendUnitLabel_class O hO power S W.2)

section Cuts

variable {I J : Type} [Fintype I] [Fintype J]
  (W : GradedObject (canonicalStructure (L := L) O hO power) S)
  (A : I → GradedObject (canonicalStructure (L := L) O hO power) S)
  (B : J → GradedObject (canonicalStructure (L := L) O hO power) S)

local notation "F" => taggedGradedFamily 𝓜 S (markBlowupLocus O hO power S W A)
local notation "G" => taggedGradedFamily 𝓜 S B

variable (e : (taggedGradedFamily (canonicalStructure (L := L) O hO power) S
      (markBlowupLocus O hO power S W A)).Points ≃
    (taggedGradedFamily (canonicalStructure (L := L) O hO power) S B).Points)

@[expose] def markedCenterCut (j : J) : Set (Fin W.2.arity → RV0 O) :=
  sourceGraphCut F G e none j

theorem markedCenterCut_subset (j : J) : markedCenterCut O hO power S W A B e j ⊆ W.2.carrier :=
  sourceGraphCut_subset F G e none j

@[expose] def markedCenterPiece
    (graph : ∀ i j, isRVSet 𝓜 S (RVFamily.graphPiece F G e i j))
    (j : J) : RVObject 𝓜 S W.1 :=
  ObjectLift.restrictTags W.2 (markedCenterCut_subset O hO power S W A B e j)
    (sourceGraphCut_definable F G e none j (graph none j))

/-- Restricting the raised center to a graph cut gives the same class
as raising the restricted lower-degree center. -/
theorem markedCenterPiece_raised_class
    (graph : ∀ i j, isRVSet 𝓜 S (RVFamily.graphPiece F G e i j)) (j : J) :
    cls ⟨W.1+1,sourceCutObject (markBlowupLocus O hO power S W A) B e graph none j⟩ =
      cls ⟨W.1,markedCenterPiece O hO power S W A B e graph j⟩ * p := by
  let D := markedCenterPiece O hO power S W A B e graph j
  have he := appendUnitLabel_class O hO power S D
  change cls ⟨W.1+1,appendUnitLabel D (canonical_rvUnit_nonzero O hO power)⟩ = cls ⟨W.1,D⟩ * p at he
  rw [← he]
  apply scissors_sound 𝓜 S
  apply RVRelation.iso
  change RVDefinablyEquivalent 𝓜 S.carrier D.carrier D.carrier
  exact ⟨Equiv.refl _,definable_identity_label 𝓜 S D.definable⟩

theorem markedCenterPiece_sum
    (graph : ∀ i j, isRVSet 𝓜 S (RVFamily.graphPiece F G e i j)) :
    cls W = ∑ j, cls ⟨W.1,markedCenterPiece O hO power S W A B e graph j⟩ := by
  obtain ⟨disj,cover⟩ := sourceGraphCut_partition F G e none
  exact restrictTags_partition W.2 _ _ _ disj cover

end Cuts

section Exclusive

variable {I J : Type} [Fintype I] [Fintype J]
  (W : GradedObject (canonicalStructure (L := L) O hO power) S)
  (A : I → GradedObject (canonicalStructure (L := L) O hO power) S)
  (B : J → GradedObject (canonicalStructure (L := L) O hO power) S)

local notation "F" => taggedGradedFamily 𝓜 S (markBlowupLocus O hO power S W A)
local notation "G" => taggedGradedFamily 𝓜 S B

theorem markedCenter_union_class
    (e : RVFamily.Points F ≃ RVFamily.Points G)
    (graph : ∀ i j, isRVSet 𝓜 S (RVFamily.graphPiece F G e i j))
    {H : Type} [Fintype H] (f : H ↪ J) :
    ∃ D : RVObject 𝓜 S W.1,
      cls ⟨W.1,D⟩ = ∑ i, cls ⟨W.1,markedCenterPiece O hO power S W A B e graph (f i)⟩ := by
  let cuts (i : H) := markedCenterCut O hO power S W A B e (f i)
  have hc (i : H) : isRVSet 𝓜 S (cuts i) := sourceGraphCut_definable F G e none (f i) (graph none (f i))
  have sub (i : H) : cuts i ⊆ W.2.carrier := markedCenterCut_subset O hO power S W A B e (f i)
  have disj : Pairwise (fun i j => Disjoint (cuts i) (cuts j)) := by
    intro i j ne
    exact (sourceGraphCut_partition F G e none).1 (fun eq => ne (f.injective eq))
  exact ⟨ObjectLift.restrictTags W.2 (Set.iUnion_subset sub) (isRVSet_iUnion hc),
    restrictTags_union_class W.2 cuts hc sub disj⟩

end Exclusive

end GeneralizedEuler.Section5
