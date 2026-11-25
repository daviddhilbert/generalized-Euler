module

public import Section2.PrescribedRVStep
public import Section2.RelativeValueSubspace
public import Section2.ValueMonomials
public import Section2.FieldDefinableClosure

/-! Fixed-RV extensions from the two rank-one alternatives. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w}
  {J K F : Type*} [Field J] [LinearOrder J] [IsStrictOrderedRing J] [L.Structure J]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  {I : ValuationSubring J} {O : ValuationSubring K} {Q : ValuationSubring F}
  [L.Structure (Residue I)] [L.Structure (Residue O)] [L.Structure (Residue Q)]
  {hI : IsOrderConvex I} {hO : IsOrderConvex O} {hQ : IsOrderConvex Q}
  {PI : E → RV0 I → RV0 I} {PO : E → RV0 O → RV0 O} {PQ : E → RV0 Q → RV0 Q}
  {R : Set (RV0 O)}
  (A : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R)
  (left : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure O hO PO))
  (right : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure Q hQ PQ))
  (B : L.Substructure K) (field : B ↪[L] F)
  (hbase : A.source.carrier .vf ⊆ B)
  (hfield : ∀ x : A.source.carrier .vf, field ⟨x.val, hbase x.property⟩ = A.embedding.toEmbedding .vf x)
  (rep : B → J)
  (hleft : ∀ x : B, left.toEmbedding .vf (rep x) = x.val)
  (hright : ∀ x : B, right.toEmbedding .vf (rep x) = field x)
  (D : Subfield J)
  (hD : Set.range (fun c : A.source.carrier .vf => rep ⟨c.val, hbase c.property⟩) = (D : Set J))

include hfield hleft hright hD

section Value

variable [Field E] (g : E → PositiveField J →* PositiveField J)
  (hPI : ∀ e, AgreesWithFieldPower I (g e) (PI e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField J), I.valuation (x : J) = 1 → I.valuation (g e x : J) = 1)
  (hStable : ∀ e (x : PositiveField J), (x : J) ∈ D → (g e x : J) ∈ D)

set_option linter.style.haveILetI false in
/-- The value alternative of the Wilkie bound gives the monomial
descriptions needed to extend the embedding. -/
theorem exists_fixedRVExtension_of_wilkie_new_value
    (a : PositiveField J) (t : A.source.carrier .rv)
    (ha : rv O (left.toEmbedding .vf a.val) = t.val)
    (hb : rv Q (right.toEmbedding .vf a.val) = A.embedding.toEmbedding .rv t)
    (hNew : I.valuation a.val ∉ I.valuation '' (D : Set J))
    (hRank : RelativeValueRankLEOne I g hzero hone hadd hmul D hStable PI hPI hunit)
    (hResidue : ∀ x : J, I.valuation x = 1 → rv I x ∈ rv I '' (D : Set J)) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) := by
  letI := unsignedValueModule I g PI hPI hzero hone hadd hmul hunit
  let U := oldValueSubspace I g hzero hone hadd hmul D hStable PI hPI hunit
  obtain ⟨hFin, hRank⟩ := hRank
  let : FiniteDimensional E (_ ⧸ U) := hFin
  have haU : positiveFieldValue I a ∉ U := by
    intro h
    have hv := (mem_oldValueSubspace_iff I g hzero hone hadd hmul D hStable PI hPI hunit _).mp h
    rw [positiveFieldValue_coe] at hv
    exact hNew hv
  have hmon := exists_rv_monomial_of_relative_rank I g PI hPI hzero hone hadd hmul hunit D a
    U hRank haU (exists_positive_representative_of_mem_oldValueSubspace
      I g hzero hone hadd hmul D hStable PI hPI hunit) hResidue
  apply exists_fixedRVExtension_of_canonical_monomials A left right B field hbase hfield rep hleft hright
    a.val t ha hb
  intro s hs
  obtain ⟨x, rfl⟩ := rv_surjective I s
  have hx : x ≠ 0 := fun he => hs (he ▸ map_zero (rv I))
  obtain ⟨d, hd, e, h⟩ := hmon x hx
  have hd' : d ∈ (D : Set J) := hd
  obtain ⟨c, rfl⟩ := hD.symm ▸ hd'
  exact ⟨c, e, h⟩

end Value

/-- The residue alternative gives term generation by the normalized
residue over the old residue field. -/
theorem exists_fixedRVExtension_of_wilkie_new_residue {T : L.Theory}
    [T.IsUniversal] [Residue I ⊨ T] (hQE : EliminatesQuantifiers T)
    (a : J) (t : A.source.carrier .rv)
    (ha : rv O (left.toEmbedding .vf a) = t.val)
    (hb : rv Q (right.toEmbedding .vf a) = A.embedding.toEmbedding .rv t)
    (hNew : rv I a ∉ rv I '' (D : Set J))
    (hValues : ∀ x : J, I.valuation x ∈ I.valuation '' (D : Set J))
    (old : Set (Residue I)) (hold : ∀ r, r ∈ old ↔ residueRV I r ∈ rv I '' (D : Set J))
    (M : Matroid (Residue I)) (hFull : M.E = Set.univ) (hRank : M.eRk M.E ≤ 1)
    (hNonloop : ∀ r, r ∉ old → M.IsNonloop r)
    (hClosure : ∀ r x, x ∈ M.closure {r} → ∃ φ : L.Formula ((old ⊕ Unit) ⊕ Unit),
      ∀ y : Residue I, φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => r)) (fun _ => y)) ↔ y = x) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) := by
  obtain ⟨c, hc, _, r, hr, hrNew⟩ := exists_new_residue_of_old_value I (hValues a) hNew
  have hc' : c ∈ (D : Set J) := hc
  obtain ⟨d, rfl⟩ := hD.symm ▸ hc'
  apply exists_fixedRVExtension_of_normalized_residue A left right B field hbase hfield rep hleft hright
    a t d ha hb r (hr.trans (map_div₀ (rv I) _ _)) old
  · intro s hs
    obtain ⟨z, hz, h⟩ := (hold s).mp hs
    obtain ⟨c, rfl⟩ := hD.symm ▸ hz
    exact ⟨c, h.symm⟩
  · have hr' : r ∉ old := fun h => hrNew ((hold r).mp h)
    exact exists_residue_term_of_relative_rank_le_one hQE old r M hFull hRank
      (hNonloop r hr') (hClosure r)
  · intro x
    obtain ⟨z, hz, h⟩ := hValues x
    obtain ⟨c, rfl⟩ := hD.symm ▸ hz
    exact ⟨c, h⟩

end GeneralizedEuler.Section2
