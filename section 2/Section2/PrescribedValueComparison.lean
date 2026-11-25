module

public import Section2.PrescribedRVStep
public import Section2.FieldReduct
public import Section2.FieldOperations
public import Section2.RelativeValueSubspace
public import Section2.RVMonomials
public import Section2.ValueMonomials

/-! Pullback of the valued-field data in the prescribed-RV adjunction. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w}
  {J K F : Type*} [Field J]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  (O : ValuationSubring K) (Q : ValuationSubring F)
  [L.Structure (Residue O)] [L.Structure (Residue Q)]
  (hO : IsOrderConvex O) (hQ : IsOrderConvex Q)
  (PO : E → RV0 O → RV0 O) (PQ : E → RV0 Q → RV0 Q)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO PO))
  (σ : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))
  (p : J →+* K) (q : J →+* F)
  (I R : ValuationSubring J)
  (hp : RespectsValuationRing I O p) (hq : RespectsValuationRing R Q q)
  (A : Subfield J) (rep : S.carrier .vf → J) (hRep : Set.range rep = (A : Set J))
  (hLeft : ∀ c : S.carrier .vf, p (rep c) = c.val)
  (hRight : ∀ c : S.carrier .vf, q (rep c) = σ.toEmbedding .vf c)

private theorem has_old_value_of_common_representatives {J K : Type*} [Field J] [Field K]
    (I : ValuationSubring J) (O : ValuationSubring K) (p : J →+* K)
    (hp : RespectsValuationRing I O p) {D : Type*} (d : D → J) (a : J) :
    I.valuation a ∈ I.valuation '' Set.range d ↔
      ∃ b : D, O.valuation (p a) = O.valuation (p (d b)) := by
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨b, (valuation_eq_map_iff I O p hp a (d b)).mpr hb.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨d b, Set.mem_range_self b, (valuation_eq_map_iff I O p hp _ _).mp hb.symm⟩

include hp hq hRep hLeft hRight in
/-- Pulling the two rings back to the common field adjunction
preserves the old-value decision for the prescribed generator. -/
theorem pulledValuations_agree_on_old_value (a : J) (t : S.carrier .rv)
    (ha : rv O (p a) = t.val) (hb : rv Q (q a) = σ.toEmbedding .rv t) :
    I.valuation a ∈ I.valuation '' (A : Set J) ↔ R.valuation a ∈ R.valuation '' (A : Set J) := by
  rw [← hRep, has_old_value_of_common_representatives I O p hp,
    has_old_value_of_common_representatives R Q q hq]
  have hv : O.valuation (p a) = unsignedValue O t.val :=
    (unsignedValue_rv O (p a)).symm.trans (congrArg (unsignedValue O) ha)
  have hw : Q.valuation (q a) = unsignedValue Q (σ.toEmbedding .rv t) :=
    (unsignedValue_rv Q (q a)).symm.trans (congrArg (unsignedValue Q) hb)
  simp only [hv, hw, hLeft, hRight]
  exact has_old_value_iff_of_sortedEmbedding O hO PO Q hQ PQ S σ t

include hp hq hRep hLeft hRight in
/-- The pulled-back rings agree on the old field because the original
sorted embedding preserves the signed valuation-ring test. -/
theorem pulledValuations_agree_on_old_ring
    (minusOne : S.carrier .vf) (hminus : minusOne.val = -1)
    (hminus' : σ.toEmbedding .vf minusOne = -1) :
    ∀ x ∈ A, x ∈ I ↔ x ∈ R := by
  intro x hx
  have hxRep : x ∈ Set.range rep := hRep.symm ▸ (show x ∈ (A : Set J) from hx)
  obtain ⟨c, rfl⟩ := hxRep
  rw [← hp, ← hq, hLeft, hRight]
  exact (mem_valuationRing_iff_of_sortedEmbedding O hO PO Q hQ PQ S σ
    minusOne c hminus hminus').symm

/-- A step for positive representatives suffices. A negative
representative is recovered by adjoining its opposite. -/
theorem exists_fixedRVExtension_of_positive_representative_step
    (terms : OrderedFieldTerms L) (hK : InterpretsOrderedFieldTerms (A := K) terms)
    {W : Set (RV0 O)} (C : FixedRVLift (canonicalStructure (L := L) O hO PO)
      (canonicalStructure (L := L) Q hQ PQ) W)
    (hPos : ∀ x : K, 0 < x → rv O x ∈ W → rv O x ∉ rv O '' C.source.carrier .vf →
      ∃ D : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) W,
        C ≤ D ∧ x ∈ D.source.carrier .vf)
    (t : RV0 O) (ht : t ∈ W) (hNew : t ∉ rv O '' C.source.carrier .vf) :
    ∃ D : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) W,
      C ≤ D ∧ t ∈ rv O '' D.source.carrier .vf := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  let A := subfieldOfFieldSubstructure terms hK (vfReductOfSortedSubstructure O hO PO C.source)
  have ha (z : K) : z ∈ A ↔ z ∈ C.source.carrier .vf :=
    mem_subfieldOfFieldSubstructure terms hK (vfReductOfSortedSubstructure O hO PO C.source) z
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hNew ⟨0, (ha 0).mp A.zero_mem, rfl⟩
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · let m : C.source.carrier .vf := ⟨-1, (ha _).mp (A.neg_mem A.one_mem)⟩
    have hm : rv O (-1) ∈ C.source.carrier .rv := by
      rw [← canonicalSubstructure_rvMap O hO PO C.source m]
      exact (C.source.structureOn.rvMap m).property
    have hx' : rv O x ∈ C.source.carrier .rv := C.rv_eq.symm ▸ ht
    have hn : rv O (-x) ∈ W := by
      rw [← C.rv_eq, ← neg_one_mul x, map_mul]
      let args : SortedArgs (CanonicalSort O) [.rv, .rv] :=
        Fin.cases (rv O (-1)) (Fin.cases (rv O x) (fun j => j.elim0))
      have hClosed := C.source.closed .rvMul args
      change (∀ j, args j ∈ C.source.carrier ([.rv, .rv].get j)) →
        rv O (-1) * rv O x ∈ C.source.carrier .rv at hClosed
      apply hClosed
      intro j
      fin_cases j
      · exact hm
      · exact hx'
    have hFresh : rv O (-x) ∉ rv O '' C.source.carrier .vf := by
      rintro ⟨y, hy, he⟩
      have hNeg := congrArg (rv O (-1) * ·) he
      rw [← map_mul, ← map_mul, neg_one_mul, neg_one_mul, neg_neg] at hNeg
      exact hNew ⟨-y, (ha _).mp (A.neg_mem ((ha _).mpr hy)), hNeg⟩
    obtain ⟨D, hCD, hDx⟩ := hPos (-x) (neg_pos.mpr hx) hn hFresh
    let B := subfieldOfFieldSubstructure terms hK (vfReductOfSortedSubstructure O hO PO D.source)
    have hB (z : K) : z ∈ B ↔ z ∈ D.source.carrier .vf :=
      mem_subfieldOfFieldSubstructure terms hK (vfReductOfSortedSubstructure O hO PO D.source) z
    have hxB : x ∈ B := neg_neg x ▸ B.neg_mem ((hB _).mpr hDx)
    exact ⟨D, hCD, x, (hB x).mp hxB, rfl⟩
  · obtain ⟨D, hCD, hDx⟩ := hPos x hx ht hNew
    exact ⟨D, hCD, x, hDx, rfl⟩

end GeneralizedEuler.Section2
