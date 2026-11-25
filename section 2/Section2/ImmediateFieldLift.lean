module

public import Section2.PrescribedValueComparison

/-! Extending an immediate map over an adjunction with unchanged
leading terms, using the comparison of the two pulled-back rings. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w}
  {J K F : Type*} [Field J] [LinearOrder J] [IsStrictOrderedRing J]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  (O : ValuationSubring K) (Q : ValuationSubring F)
  [L.Structure (Residue O)] [L.Structure (Residue Q)]
  (hO : IsOrderConvex O) (hQ : IsOrderConvex Q)
  (PO : E → RV0 O → RV0 O) (PQ : E → RV0 Q → RV0 Q)

/-- If both fields of the proposed adjunction have unchanged RV, their
common field map is compatible with the old RV map. The two pulled-back
rings are determined by the old valuation ring and the unchanged values. -/
theorem exists_fixedRVExtension_of_unchanged_RV_images
    {R : Set (RV0 O)} (A : FixedRVLift (canonicalStructure (L := L) O hO PO)
      (canonicalStructure Q hQ PQ) R)
    (B : L.Substructure K) (field : B ↪[L] F)
    (hbase : A.source.carrier .vf ⊆ B)
    (hfield : ∀ x : A.source.carrier .vf, field ⟨x.val, hbase x.property⟩ = A.embedding.toEmbedding .vf x)
    (p : J →+* K) (q : J →+* F) (hp : Monotone p) (hq : Monotone q)
    (rep : B → J) (surj : Function.Surjective rep)
    (hLeft : ∀ x : B, p (rep x) = x.val) (hRight : ∀ x : B, q (rep x) = field x)
    (D : Subfield J)
    (hRep : Set.range (fun c : A.source.carrier .vf => rep ⟨c.val, hbase c.property⟩) = (D : Set J))
    (m : A.source.carrier .vf) (hm : m.val = -1) (hm' : A.embedding.toEmbedding .vf m = -1)
    (hOld : ∀ x : B, rv O x.val ∈ rv O '' A.source.carrier .vf)
    (hOld' : ∀ x : B, rv Q (field x) ∈ Set.range
      (fun c : A.source.carrier .vf => rv Q (A.embedding.toEmbedding .vf c))) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) ∧
        ∀ (x : B) (hx : x.val ∈ C.source.carrier .vf),
          C.embedding.toEmbedding .vf ⟨x.val, hx⟩ = field x := by
  let I := O.comap p
  let I' := Q.comap q
  have hVal (x : J) : p x ∈ O ↔ x ∈ I := ValuationSubring.mem_comap.symm
  have hVal' (x : J) : q x ∈ Q ↔ x ∈ I' := ValuationSubring.mem_comap.symm
  let r (c : A.source.carrier .vf) := rep ⟨c.val, hbase c.property⟩
  have hl (c : A.source.carrier .vf) : p (r c) = c.val := hLeft _
  have hr (c : A.source.carrier .vf) : q (r c) = A.embedding.toEmbedding .vf c :=
    (hRight _).trans (hfield c)
  have hOldValues : ∀ v, v ∈ I.valuation '' (D : Set J) := by
    intro v
    obtain ⟨x, rfl⟩ := I.valuation_surjective v
    obtain ⟨y, rfl⟩ := surj x
    obtain ⟨c, hc, he⟩ := hOld y
    let c' : A.source.carrier .vf := ⟨c, hc⟩
    refine ⟨r c', hRep ▸ Set.mem_range_self c', ?_⟩
    apply (valuation_eq_map_iff I O p hVal _ _).mp
    rw [hl, hLeft]
    simpa only [unsignedValue_rv] using congrArg (unsignedValue O) he
  have hOldValues' : ∀ v, v ∈ I'.valuation '' (D : Set J) := by
    intro v
    obtain ⟨x, rfl⟩ := I'.valuation_surjective v
    obtain ⟨y, rfl⟩ := surj x
    obtain ⟨c, he⟩ := hOld' y
    refine ⟨r c, hRep ▸ Set.mem_range_self c, ?_⟩
    apply (valuation_eq_map_iff I' Q q hVal' _ _).mp
    rw [hr, hRight]
    simpa only [unsignedValue_rv] using congrArg (unsignedValue Q) he
  have hBase := pulledValuations_agree_on_old_ring O Q hO hQ PO PQ A.source A.embedding
    p q I I' hVal hVal' D r hRep hl hr m hm hm'
  have hEq := eq_convexValuationRing_of_all_values_old I I'
    (convex_comap_valuationRing O p hO hp) (convex_comap_valuationRing Q q hQ hq)
    D hBase hOldValues hOldValues'
  have hqI : RespectsValuationRing I Q q := hEq.symm ▸ hVal'
  have hB (x : K) (hx : x ∈ B) : rv O x ∈ A.source.carrier .rv := by
    obtain ⟨c, hc, he⟩ := hOld ⟨x, hx⟩
    have h := canonicalSubstructure_rvMap O hO PO A.source ⟨c, hc⟩
    exact (h.trans he) ▸ (A.source.structureOn.rvMap ⟨c, hc⟩).property
  have hComm (x : B) :
      A.embedding.toEmbedding .rv ⟨rv O x.val, hB x.val x.property⟩ = rv Q (field x) := by
    obtain ⟨c, hc, he⟩ := hOld x
    let c' : A.source.carrier .vf := ⟨c, hc⟩
    have hc' : rv O (p (r c')) = rv O (p (rep x)) := by
      rw [hl, hLeft]
      exact he
    have hTerm := (rv_map_eq_iff I O hVal _ _).mp hc'
    have hTerm' := (rv_map_eq_iff I Q hqI _ _).mpr hTerm
    rw [hr, hRight] at hTerm'
    have hEqRV : A.source.structureOn.rvMap c' = ⟨rv O x.val, hB x.val x.property⟩ :=
      Subtype.ext ((canonicalSubstructure_rvMap O hO PO A.source c').trans he)
    have hMap := A.embedding.map_rv c'
    rw [hEqRV, canonicalStructure_rvMap] at hMap
    exact hMap.trans hTerm'
  exact exists_fixedRVExtension_of_compatible_field O hO PO Q hQ PQ A B field hbase hB hfield hComm

end GeneralizedEuler.Section2
