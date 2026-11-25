module

public import Section2.FieldReduct
public import Section2.FieldTypeLift

/-! The field-adjunction step of Lemma 2.20 after naming representatives. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z

variable {L : Language.{u, v}} {E : Type w} {K F : Type*}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  {O : ValuationSubring K} {Q : ValuationSubring F} [L.Structure (Residue O)] [L.Structure (Residue Q)]
  {hO : IsOrderConvex O} {hQ : IsOrderConvex Q} {P : E → RV0 O → RV0 O} {PQ : E → RV0 Q → RV0 Q}

open Cardinal in
/-- The field used for saturation has size bounded by that of the old
field, the required representative family, and the field language. -/
theorem lift_card_representativeField_le
    {K : Type z} [L.Structure K] (A : Set K) {D : Type z} (q : D → K) :
    lift.{u, z} #(Substructure.closure L (A ∪ Set.range q)) ≤
      max ℵ₀ (lift.{u, z} #A + lift.{u, z} #D + lift.{z, u} #(Σ i, L.Functions i)) := by
  have h : #(A ∪ Set.range q : Set K) ≤ #A + #D :=
    (mk_union_le A (Set.range q)).trans (add_le_add_right mk_range_le _)
  apply Substructure.lift_card_closure_le.trans
  apply max_le_max le_rfl
  rw [← lift_add]
  exact add_le_add_left (lift_le.mpr h) _

set_option linter.style.haveILetI false in
private def fieldReductOfValuedEmbedding (O : ValuationSubring K) (Q : ValuationSubring F) :
    letI := convexStructure O L
    letI := convexStructure Q L
    letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K := convexStructure_expansion O
    ∀ (D : (convexLanguage L).Substructure K) (_ : D ↪[convexLanguage L] F),
      (LHom.sumInl : L →ᴸ convexLanguage L).substructureReduct D ↪[L] F := by
  letI := convexStructure O L
  letI := convexStructure Q L
  let e : L →ᴸ convexLanguage L := LHom.sumInl
  letI : e.IsExpansionOn K := convexStructure_expansion O
  letI : e.IsExpansionOn F := convexStructure_expansion Q
  intro D f
  let B := e.substructureReduct D
  refine { toFun := f, inj' := f.injective, map_fun' := ?_, map_rel' := ?_ }
  · intro n g x
    have h : Structure.funMap (L := L) (M := B) g x =
        Structure.funMap (L := convexLanguage L) (M := D) (e.onFunction g) x := by
      apply Subtype.ext
      exact (B.subtype.map_fun g x).trans
        ((e.map_onFunction g (B.subtype ∘ x)).symm.trans (D.subtype.map_fun (e.onFunction g) x).symm)
    change f (Structure.funMap (L := L) (M := B) g x) = _
    exact (congrArg f h).trans ((f.map_fun (e.onFunction g) x).trans (e.map_onFunction g _))
  · intro n g x
    have h : Structure.RelMap (L := convexLanguage L) (M := D) (e.onRelation g) x ↔
        Structure.RelMap (L := L) (M := B) g x :=
      (D.subtype.map_rel (e.onRelation g) x).symm.trans
        ((e.map_onRelation g (B.subtype ∘ x)).to_iff.trans (B.subtype.map_rel g x))
    exact (e.map_onRelation g (f ∘ x)).to_iff.symm.trans ((f.map_rel (e.onRelation g) x).trans h)

set_option linter.style.haveILetI false in
/-- Once the larger partial map names representatives of every leading
term of the desired simple adjunction, valued-field QE and saturation
give the required fixed-RV lift over the original source. -/
theorem exists_fixedRVExtension_of_represented_adjunction
    {R : Set (RV0 O)}
    {A C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R}
    (hAC : A ≤ C) (a : K)
    (minusOne : C.source.carrier .vf) (hminus : minusOne.val = -1)
    (hminus' : C.embedding.toEmbedding .vf minusOne = -1)
    (terms : FieldTerms (convexLanguage L))
    (hK : letI := convexStructure O L; InterpretsFieldTerms (K := K) terms)
    (hF : letI := convexStructure Q L; InterpretsFieldTerms (K := F) terms)
    {T : (convexLanguage L).Theory} (hQE : EliminatesQuantifiers T) :
    let B := Substructure.closure L (insert a (A.source.carrier .vf))
    letI := convexStructure O L
    letI := convexStructure Q L
    ∀ (_ : K ⊨ T) (_ : F ⊨ T),
      RealizesFinitelySatisfiableFieldTypes (convexLanguage L) F
        (convexReductOfSortedSubstructure O hO P C.source) →
      rv O '' (B : Set K) ⊆ rv O '' C.source.carrier .vf →
      ∃ B' : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R,
        A ≤ B' ∧ B'.source.carrier .vf = (B : Set K) := by
  let B := Substructure.closure L (insert a (A.source.carrier .vf))
  letI := convexStructure O L
  letI := convexStructure Q L
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K := convexStructure_expansion O
  dsimp only
  intro hTK hTF hsat hcover
  obtain ⟨hinclude, hmaps⟩ := (FixedRVLift.le_iff_extends A C).mp hAC
  let U := convexReductOfSortedSubstructure O hO P C.source
  let side := valuedFieldEmbeddingOfSorted O Q hO hQ P PQ C.source C.embedding minusOne hminus hminus'
  have hbase : A.source.carrier .vf ⊆ B :=
    fun _ hx => Substructure.subset_closure (Set.mem_insert_of_mem a hx)
  have hrep (x : B) : ∃ c : U, rv O c.val = rv O x.val := by
    obtain ⟨c, hc, hr⟩ := hcover ⟨x.val, x.property, rfl⟩
    exact ⟨⟨c, hc⟩, hr⟩
  choose representative hrepresentative using hrep
  obtain ⟨b, f, _, hC, hRV⟩ := exists_simpleFieldLift_preserving_namedRV O Q terms hK hF
    hQE U.subtype side hTK hTF hsat a representative
  let D := Substructure.closure (convexLanguage L)
    (Set.range (Sum.elim (U.subtype : U → K) (fun _ : Unit => a)))
  let name := (LHom.sumInl : L →ᴸ convexLanguage L)
  have hBD : B ≤ name.substructureReduct D := by
    apply Substructure.closure_le.mpr
    intro x hx
    apply (name.mem_substructureReduct).mpr
    apply Substructure.subset_closure
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨.inr (), rfl⟩
    · exact ⟨.inl ⟨x, hinclude .vf hx⟩, rfl⟩
  let field := (fieldReductOfValuedEmbedding O Q D f).comp (Substructure.inclusion hBD)
  have field_apply (x : B) : field x = f ⟨x.val, hBD x.property⟩ := rfl
  have hfield (x : A.source.carrier .vf) :
      field ⟨x.val, hbase x.property⟩ = A.embedding.toEmbedding .vf x :=
    (field_apply _).trans ((hC ⟨x.val, hinclude .vf x.property⟩).trans (hmaps .vf x).symm)
  let c (x : B) : C.source.carrier .vf := representative x
  let t (x : B) := C.source.structureOn.rvMap (c x)
  have ht (x : B) : (t x).val = rv O x.val :=
    (canonicalSubstructure_rvMap O hO P C.source (c x)).trans (hrepresentative x)
  have hB (x : K) (hx : x ∈ B) : rv O x ∈ A.source.carrier .rv := by
    have heq : C.source.carrier .rv = A.source.carrier .rv := C.rv_eq.trans A.rv_eq.symm
    have hmem : (t ⟨x, hx⟩).val ∈ A.source.carrier .rv := heq ▸ (t ⟨x, hx⟩).property
    exact ht ⟨x, hx⟩ ▸ hmem
  have himage (x : B) : rv Q (field x) = C.embedding.toEmbedding .rv (t x) := by
    have hv : rv Q (field x) = rv Q (side (representative x)) :=
      ((congrArg (rv Q) (field_apply x)).trans
        ((hRV ⟨x.val, hBD x.property⟩ x).mp (hrepresentative x).symm))
    have he := C.embedding.map_rv (c x)
    rw [canonicalStructure_rvMap] at he
    exact hv.trans he.symm
  have hcomm (x : B) :
      A.embedding.toEmbedding .rv ⟨rv O x.val, hB x x.property⟩ = rv Q (field x) := by
    let u : A.source.carrier .rv := ⟨rv O x.val, hB x x.property⟩
    have he : (⟨u.val, hinclude .rv u.property⟩ : C.source.carrier .rv) = t x := Subtype.ext (ht x).symm
    exact (hmaps .rv u).trans ((congrArg (C.embedding.toEmbedding .rv) he).trans (himage x).symm)
  obtain ⟨C, hAC, hC, _⟩ :=
    exists_fixedRVExtension_of_compatible_field O hO P Q hQ PQ A B field hbase hB hfield hcomm
  exact ⟨C, hAC, hC⟩

/-- A larger lift can be restricted to any intermediate field
substructure while keeping its fixed RV sort. -/
theorem exists_restricted_fixedRVLift {R : Set (RV0 O)}
    {A B : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R}
    (hAB : A ≤ B) (V : L.Substructure K)
    (hAV : A.source.carrier .vf ⊆ V) (hVB : (V : Set K) ⊆ B.source.carrier .vf) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R,
      A ≤ C ∧ C ≤ B ∧ C.source.carrier .vf = (V : Set K) := by
  obtain ⟨hABmem, hABeq⟩ := (FixedRVLift.le_iff_extends A B).mp hAB
  let W := vfReductOfSortedSubstructure O hO P B.source
  let field : V ↪[L] F :=
    (fieldEmbeddingOfSorted O Q hO hQ P PQ B.source B.embedding).comp
      (Substructure.inclusion (T := W) hVB)
  have hRV (x : K) (hx : x ∈ V) : rv O x ∈ B.source.carrier .rv := by
    rw [← canonicalStructure_rvMap O hO P (L := L)]
    exact B.source.rvMap_mem (hVB hx)
  have hcomm (x : V) :
      B.embedding.toEmbedding .rv ⟨rv O x.val, hRV x x.property⟩ = rv Q (field x) := by
    let w : B.source.carrier .vf := ⟨x.val, hVB x.property⟩
    have he : (⟨rv O x.val, hRV x x.property⟩ : B.source.carrier .rv) = B.source.structureOn.rvMap w :=
      Subtype.ext (canonicalSubstructure_rvMap O hO P B.source w).symm
    rw [he, B.embedding.map_rv, canonicalStructure_rvMap]
    rfl
  let F := enlargeVF O hO P B.source V hRV
  let e := liftVFEmbedding O hO P Q hQ PQ B.source V hRV B.embedding field hcomm
  let C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R :=
    ⟨F, B.rv_eq, e⟩
  have hCBmem (s : TCsort) : C.source.carrier s ⊆ B.source.carrier s := by
    cases s with
    | vf => exact hVB
    | rv => exact Set.Subset.rfl
  have hCBeq (s : TCsort) (x : C.source.carrier s) :
      C.embedding.toEmbedding s x = B.embedding.toEmbedding s ⟨x.val, hCBmem s x.property⟩ := by
    cases s with
    | vf => exact liftVFEmbedding_vf_apply O hO P Q hQ PQ B.source V hRV B.embedding field hcomm x
    | rv => exact liftVFEmbedding_rv_apply O hO P Q hQ PQ B.source V hRV B.embedding field hcomm x
  have hACmem (s : TCsort) : A.source.carrier s ⊆ C.source.carrier s := by
    cases s with
    | vf => exact hAV
    | rv => exact hABmem .rv
  refine ⟨C, FixedRVLift.le_of_compatible hACmem ?_, FixedRVLift.le_of_compatible hCBmem hCBeq, rfl⟩
  intro s x
  exact (hABeq s x).trans (hCBeq s ⟨x.val, hACmem s x.property⟩).symm

set_option linter.style.haveILetI false in
/-- The two stages of Lemma 2.20 give a single field-point extension.
After the common-lift iteration, restrict its field to the closure of
the old field and one representative per required leading term.
Saturation is only used over that generated field. -/
theorem exists_fixedRVExtension_via_representatives
    {R : Set (RV0 O)}
    (A : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R)
    (a : K) (minusOne : A.source.carrier .vf) (hminus : minusOne.val = -1)
    (hminus' : A.embedding.toEmbedding .vf minusOne = -1)
    (terms : FieldTerms (convexLanguage L))
    (hK : letI := convexStructure O L; InterpretsFieldTerms (K := K) terms)
    (hF : letI := convexStructure Q L; InterpretsFieldTerms (K := F) terms)
    {T : (convexLanguage L).Theory} (hQE : EliminatesQuantifiers T) :
    let B := Substructure.closure L (insert a (A.source.carrier .vf))
    let D := rv O '' (B : Set K)
    letI := convexStructure O L
    letI := convexStructure Q L
    ∀ (_ : K ⊨ T) (_ : F ⊨ T),
      (∀ (C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R)
        (q : D → K), C.source.carrier .vf =
          (Substructure.closure L (A.source.carrier .vf ∪ Set.range q) : Set K) →
        RealizesFinitelySatisfiableFieldTypes (convexLanguage L) F
          (convexReductOfSortedSubstructure O hO P C.source)) →
      (∀ C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R,
        A ≤ C → ∀ t ∈ D, t ∉ rv O '' C.source.carrier .vf →
        ∃ U : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R,
          C ≤ U ∧ t ∈ rv O '' U.source.carrier .vf) →
      ∃ C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure Q hQ PQ) R,
        A ≤ C ∧ C.source.carrier .vf = (B : Set K) ∧ a ∈ C.source.carrier .vf := by
  let B := Substructure.closure L (insert a (A.source.carrier .vf))
  let D := rv O '' (B : Set K)
  letI := convexStructure O L
  letI := convexStructure Q L
  dsimp only
  intro hTK hTF hsat hstep
  obtain ⟨U, hAU, hcover⟩ := A.exists_cover_by_representatives (rv O) D hstep
  have hrep (t : D) : ∃ x ∈ U.source.carrier .vf, rv O x = t.val := hcover t.property
  choose q hqmem hqRV using hrep
  let V := Substructure.closure L (A.source.carrier .vf ∪ Set.range q)
  have hAV : A.source.carrier .vf ⊆ V :=
    fun _ hx => Substructure.subset_closure (Or.inl hx)
  have hUV : (V : Set K) ⊆ U.source.carrier .vf := by
    change V ≤ vfReductOfSortedSubstructure O hO P U.source
    apply Substructure.closure_le.mpr
    intro x hx
    rcases hx with hx | ⟨t, rfl⟩
    · exact ((FixedRVLift.le_iff_extends A U).mp hAU).choose .vf hx
    · exact hqmem t
  obtain ⟨C, hAC, _, hCV⟩ := exists_restricted_fixedRVLift hAU V hAV hUV
  have hCcover : D ⊆ rv O '' C.source.carrier .vf := by
    intro t ht
    refine ⟨q ⟨t, ht⟩, ?_, hqRV ⟨t, ht⟩⟩
    rw [hCV]
    exact Substructure.subset_closure (Or.inr (Set.mem_range_self (⟨t, ht⟩ : D)))
  obtain ⟨hACmem, hACeq⟩ := (FixedRVLift.le_iff_extends A C).mp hAC
  let m : C.source.carrier .vf := ⟨minusOne.val, hACmem .vf minusOne.property⟩
  have hm : C.embedding.toEmbedding .vf m = -1 := (hACeq .vf minusOne).symm.trans hminus'
  obtain ⟨J, hAJ, hJB⟩ := exists_fixedRVExtension_of_represented_adjunction hAC a m hminus hm
    terms hK hF hQE hTK hTF (hsat C q hCV) hCcover
  exact ⟨J, hAJ, hJB, hJB.symm ▸ Substructure.subset_closure (Set.mem_insert a _)⟩

end GeneralizedEuler.Section2
