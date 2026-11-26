module

public import Section5.FilteredPositiveIntegration
public import Section5.UnaryRecoveryExchange
import all Section2.Dimension

/-! The fixed-base closure test gives equality of the relative
field ranks under a mixed bijection. The projection-rank theorem then
gives the dimension invariance used by filtered integration. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

set_option linter.style.haveILetI false in
theorem mixedVFDimensionInvariant_of_rank
    (recovery : UnaryRecoveryHypotheses S) (rank : Set K → ℕ)
    (sameRank : letI := valuedStructureOfSorted 𝓜 ∅
      ∀ C D : Set K, Substructure.closure (convexLanguage L) (S.carrier .vf ∪ C) =
        Substructure.closure (convexLanguage L) (S.carrier .vf ∪ D) → rank C = rank D)
    (projectionRank : ∀ {n m : ℕ} (A : Set (SortedAssignment Z (MixedVariables n (Fin m)))),
      SortedDefinableOver 𝓜 S.carrier A →
      (∀ a ∈ A, rank (Set.range (a .vf)) ≤ vfDimension (mixedTuple '' A)) ∧
      (A.Nonempty → ∃ a ∈ A, rank (Set.range (a .vf)) = vfDimension (mixedTuple '' A))) :
    MixedVFDimensionInvariant S := by
  unfold MixedVFDimensionInvariant
  intro n m d e A B da db iso
  obtain ⟨f,defF⟩ := iso
  let g : MixedGraphIso 𝓜 S A B := ⟨f,defF⟩
  letI := valuedStructureOfSorted 𝓜 ∅
  have ab := output_field_closure_of_immediate_movers A B f defF (fun a => recovery.move n (a.val .vf))
  have ba := output_field_closure_of_immediate_movers B A g.symm.equiv g.symm.definable
    (fun b => recovery.move d (b.val .vf))
  have rankEq (a : A) : rank (Set.range (a.val .vf)) = rank (Set.range ((f a).val .vf)) := by
    apply sameRank
    apply le_antisymm
    · apply Substructure.closure_le.2
      apply Set.union_subset
      · exact Set.subset_union_left.trans (Substructure.subset_closure (L := convexLanguage L))
      · rintro _ ⟨i,rfl⟩
        have h := ba (f a) i
        change (f.symm (f a)).val .vf i ∈ Substructure.closure (convexLanguage L)
          (S.carrier .vf ∪ Set.range ((f a).val .vf)) at h
        rwa [f.symm_apply_apply] at h
    · apply Substructure.closure_le.2
      apply Set.union_subset
      · exact Set.subset_union_left.trans (Substructure.subset_closure (L := convexLanguage L))
      · rintro _ ⟨i,rfl⟩
        exact ab a i
  have ar := projectionRank A da
  have br := projectionRank B db
  have emptyDim {u v : ℕ} :
      vfDimension (mixedTuple '' (∅ : Set (SortedAssignment Z (MixedVariables u (Fin v))))) = 0 := by
    rw [Set.image_empty]
    unfold vfDimension
    simp [sortedFiber,HasInteriorProjection]
  by_cases ne : A.Nonempty
  · obtain ⟨a,ha,da⟩ := ar.2 ne
    obtain ⟨b,hb,db⟩ := br.2 ⟨(f ⟨a,ha⟩).val,(f ⟨a,ha⟩).property⟩
    refine le_antisymm ?_ ?_
    · exact da.symm.le.trans ((rankEq ⟨a,ha⟩).le.trans (br.1 _ (f ⟨a,ha⟩).property))
    · let ap := f.symm ⟨b,hb⟩
      have eq : rank (Set.range (b .vf)) = rank (Set.range (ap.val .vf)) := by
        have h := (rankEq ap).symm
        simpa only [ap,Equiv.apply_symm_apply] using h
      exact db.symm.le.trans (eq.le.trans (ar.1 _ ap.property))
  · have empA := Set.not_nonempty_iff_eq_empty.1 ne
    have empB : B = ∅ := Set.not_nonempty_iff_eq_empty.1 (fun ⟨b,hb⟩ =>
      ne ⟨(f.symm ⟨b,hb⟩).val,(f.symm ⟨b,hb⟩).property⟩)
    rw [empA,empB,emptyDim,emptyDim]

end GeneralizedEuler.Section5
