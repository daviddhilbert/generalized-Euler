module

public import Section2.RVAgreement

/-! The two leading-term cases of a fixed-RV field adjunction. -/

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

/-- A sorted embedding of canonical structures restricts to a monoid
homomorphism with zero on their leading terms. -/
@[expose]
def SortedEmbedding.rvHom
    (e : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure O hO PO)) :
    RV0 I →*₀ RV0 O where
  toFun := e.toEmbedding .rv
  map_one' := e.map_fun .rvOne (fun i => i.elim0)
  map_zero' := e.map_fun .rvZero (fun i => i.elim0)
  map_mul' x y := by
    let args : SortedArgs (CanonicalSort I) [.rv, .rv] :=
      Fin.cases x (Fin.cases y (fun i => i.elim0))
    exact e.map_fun .rvMul args

@[simp]
theorem SortedEmbedding.rvHom_apply
    (e : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure O hO PO))
    (t : RV0 I) : e.rvHom t = e.toEmbedding .rv t := rfl

theorem SortedEmbedding.rvHom_rv
    (e : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure O hO PO))
    (x : J) : e.rvHom (rv I x) = rv O (e.toEmbedding .vf x) := by
  simpa only [SortedEmbedding.rvHom_apply, canonicalStructure_rvMap] using e.map_rv x

theorem SortedEmbedding.rvHom_power
    (e : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure O hO PO))
    (d : E) (t : RV0 I) : e.rvHom (PI d t) = PO d (e.rvHom t) := by
  let args : SortedArgs (CanonicalSort I) [.rv] := Fin.cases t (fun i => i.elim0)
  exact e.map_fun (.power d) args

variable {R : Set (RV0 O)}
  (A : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R)
  (left : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure O hO PO))
  (right : SortedEmbedding (canonicalStructure (L := L) I hI PI) (canonicalStructure Q hQ PQ))

/-- Agreement over the old VF sort gives agreement on all its
representatives in the intermediate extension. -/
theorem rvMapsAgree_of_common_field_value (x : J) (a : A.source.carrier .vf)
    (hl : left.toEmbedding .vf x = a.val) (hr : right.toEmbedding .vf x = A.embedding.toEmbedding .vf a) :
    RVMapsAgree A.embedding left.rvHom right.rvHom (rv I x) := by
  let t := A.source.structureOn.rvMap a
  have ht : t.val = left.rvHom (rv I x) := by
    rw [left.rvHom_rv, hl]
    exact canonicalSubstructure_rvMap O hO PO A.source a
  refine ⟨ht ▸ t.property, ?_⟩
  have he : (⟨left.rvHom (rv I x), ht ▸ t.property⟩ : A.source.carrier .rv) = t :=
    Subtype.ext ht.symm
  rw [he, right.rvHom_rv, hr]
  simpa only [canonicalStructure_rvMap] using A.embedding.map_rv a

variable (B : L.Substructure K) (field : B ↪[L] F)
  (hbase : A.source.carrier .vf ⊆ B)
  (hfield : ∀ x : A.source.carrier .vf, field ⟨x.val, hbase x.property⟩ = A.embedding.toEmbedding .vf x)
  (rep : B → J)
  (hleft : ∀ x : B, left.toEmbedding .vf (rep x) = x.val)
  (hright : ∀ x : B, right.toEmbedding .vf (rep x) = field x)

include hfield hleft hright

/-- Once the RV maps agree on the representatives in the field
adjunction, it gives an extension in the fixed-RV iteration. -/
theorem exists_fixedRVExtension_of_canonical_agreement
    (hagree : ∀ x : B, RVMapsAgree A.embedding left.rvHom right.rvHom (rv I (rep x))) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) := by
  have hB (x : K) (hx : x ∈ B) : rv O x ∈ A.source.carrier .rv := by
    obtain ⟨hh, _⟩ := hagree ⟨x, hx⟩
    rwa [left.rvHom_rv, hleft ⟨x, hx⟩] at hh
  have hcomm (x : B) :
      A.embedding.toEmbedding .rv ⟨rv O x.val, hB x x.property⟩ = rv Q (field x) := by
    obtain ⟨hm, he⟩ := hagree x
    have heq : (⟨rv O x.val, hB x x.property⟩ : A.source.carrier .rv) =
        ⟨left.rvHom (rv I (rep x)), hm⟩ := by
      exact Subtype.ext ((left.rvHom_rv _).trans (congrArg (rv O) (hleft x))).symm
    rw [heq, he, right.rvHom_rv, hright]
  exact exists_fixedRVExtension_of_compatible_field O hO PO Q hQ PQ A B field hbase hB hfield hcomm

/-- The immediate field-extension case only needs old leading-term
representatives. Compatibility follows from the common field map. -/
theorem exists_fixedRVExtension_of_unchanged_leadingTerms
    (hOld : ∀ x : B, rv O x.val ∈ rv O '' A.source.carrier .vf) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) := by
  apply exists_fixedRVExtension_of_canonical_agreement A left right B field hbase hfield rep hleft hright
  intro x
  obtain ⟨c, hc, he⟩ := hOld x
  let p : A.source.carrier .vf := ⟨c, hc⟩
  let q : B := ⟨c, hbase hc⟩
  have hp := rvMapsAgree_of_common_field_value A left right (rep q) p (hleft q)
    ((hright q).trans (hfield p))
  have hv : rv I (rep q) = rv I (rep x) := by
    apply (left.toEmbedding .rv).injective
    rw [← left.rvHom_apply, ← left.rvHom_apply, left.rvHom_rv, left.rvHom_rv, hleft, hleft]
    exact he
  exact hv ▸ hp

/-- In the new-value case, the monomial descriptions of the intermediate
leading terms extend the embedding with the original RV sort. -/
theorem exists_fixedRVExtension_of_canonical_monomials
    (a : J) (t : A.source.carrier .rv)
    (ha : rv O (left.toEmbedding .vf a) = t.val)
    (hb : rv Q (right.toEmbedding .vf a) = A.embedding.toEmbedding .rv t)
    (hnormal : ∀ s : RV0 I, s ≠ 0 → ∃ c : A.source.carrier .vf, ∃ d : E,
      s = rv I (rep ⟨c.val, hbase c.property⟩) * PI d (rv I a)) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) := by
  have hgen : RVMapsAgree A.embedding left.rvHom right.rvHom (rv I a) := by
    have ht : t.val = left.rvHom (rv I a) := (left.rvHom_rv a).trans ha |>.symm
    refine ⟨ht ▸ t.property, ?_⟩
    have he : (⟨left.rvHom (rv I a), ht ▸ t.property⟩ : A.source.carrier .rv) = t :=
      Subtype.ext ht.symm
    rw [he, right.rvHom_rv, hb]
  let w (c : A.source.carrier .vf) := rv I (rep ⟨c.val, hbase c.property⟩)
  have hW (s : RV0 I) (hs : s ∈ Set.range w) : RVMapsAgree A.embedding left.rvHom right.rvHom s := by
    obtain ⟨c, rfl⟩ := hs
    exact rvMapsAgree_of_common_field_value A left right _ c (hleft _)
      ((hright _).trans (hfield c))
  have h := RVMapsAgree.of_monomials (old := A.embedding) (source := left.rvHom) (target := right.rvHom)
    PI (Set.range w) (rv I a)
    (fun d => left.rvHom_power d (rv I a)) (fun d => right.rvHom_power d (rv I a)) hW hgen (by
      intro s hs
      obtain ⟨c, d, he⟩ := hnormal s hs
      exact ⟨w c, Set.mem_range_self c, d, he⟩)
  exact exists_fixedRVExtension_of_canonical_agreement A left right B field hbase hfield rep hleft hright
    (fun x => h (rv I (rep x)))

/-- When the values are unchanged, the old value representatives and
the residue generators extend the embedding with the original RV sort. -/
theorem exists_fixedRVExtension_of_canonical_residue_generation
    {Var : Type*} (v : Var → Residue I)
    (hgen : ∀ r : Residue I, ∃ t : L.Term Var, t.realize v = r)
    (hv : ∀ i, RVMapsAgree A.embedding left.rvHom right.rvHom (residueRV I (v i)))
    (hvalues : ∀ x : J, ∃ c : A.source.carrier .vf,
      I.valuation (rep ⟨c.val, hbase c.property⟩) = I.valuation x) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) := by
  let w (c : A.source.carrier .vf) := rep ⟨c.val, hbase c.property⟩
  have hW (s : J) (hs : s ∈ Set.range w) : RVMapsAgree A.embedding left.rvHom right.rvHom (rv I s) := by
    obtain ⟨c, rfl⟩ := hs
    exact rvMapsAgree_of_common_field_value A left right _ c (hleft _) ((hright _).trans (hfield c))
  have h := RVMapsAgree.of_unchanged_values_and_residue_generation (old := A.embedding) I hI PI left right
    left.rvHom right.rvHom (fun t => (left.rvHom_apply t).symm)
    (fun t => (right.rvHom_apply t).symm) v hgen hv (Set.range w) hW (by
      intro x
      obtain ⟨c, hc⟩ := hvalues x
      exact ⟨w c, Set.mem_range_self c, hc⟩)
  exact exists_fixedRVExtension_of_canonical_agreement A left right B field hbase hfield rep hleft hright
    (fun x => h (rv I (rep x)))

end GeneralizedEuler.Section2
