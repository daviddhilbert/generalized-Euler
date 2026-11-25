module

public import Section2.InterpretedValuedQE
public import Section2.GeneratedRVAdjunction
public import Section2.RVClosure

/-! Quantifier elimination from the model presentation and the
T-convex inputs on a simple field adjunction. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w a z

variable {L : Language.{u, v}} {E : Type w} [Field E]
  (T : L.Theory) (Tconvex : (convexLanguage L).Theory)
  (terms : OrderedFieldTerms L) (graph : E → L.Formula (Fin 2))

set_option linter.style.haveILetI false in
/-- The ordered valued-field and named-power data of a canonical model
of the underlying proper T-convex theory. -/
structure CanonicalQEModel (K : Type z) where
  field : Field K
  order : LinearOrder K
  orderedRing : letI := field; letI := order; IsStrictOrderedRing K
  languageStructure : L.Structure K
  models : letI := languageStructure; K ⊨ T
  orderedTerms : letI := field; letI := order; letI := languageStructure
    InterpretsOrderedFieldTerms (A := K) terms
  ring : letI := field; ValuationSubring K
  convex : letI := field; letI := order; IsOrderConvex ring
  modelsValued : letI := field; letI := languageStructure; letI := convexStructure ring L
    K ⊨ Tconvex
  residueStructure : letI := field; L.Structure (Residue ring)
  powers : letI := field; letI := order; letI := orderedRing; letI := languageStructure
    NamedFieldPowers K graph
  rvPowers : letI := field; letI := order; letI := orderedRing; letI := languageStructure
    NamedRVPowers ring powers.pow

variable {T Tconvex terms graph}

set_option linter.style.haveILetI false in
/-- The canonical sorted expansion of the proper valued field. -/
@[expose]
def CanonicalQEModel.structureOn {K : Type z} (d : CanonicalQEModel T Tconvex terms graph K) :
    letI := d.field
    SortedStructure L E (CanonicalSort d.ring) := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  exact canonicalStructure d.ring d.convex d.rvPowers.pow

set_option linter.style.haveILetI false in
/-- The literature data for all fresh representative adjunctions
between these two proper valued-field models. -/
@[expose]
def CanonicalQEModel.hasAdjunctionInputs {K F : Type z}
    (d : CanonicalQEModel T Tconvex terms graph K)
    (e : CanonicalQEModel T Tconvex terms graph F) : Prop :=
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := e.field
  letI := e.order
  letI := e.orderedRing
  letI := e.languageStructure
  letI := e.residueStructure
  ∀ {R : Set (RV0 d.ring)} (A : FixedRVLift d.structureOn e.structureOn R)
    (a : PositiveField K) (b : F) (s : A.source.carrier .rv),
    s.val ∉ rv d.ring '' A.source.carrier .vf →
    rv d.ring a.val = s.val → rv e.ring b = A.embedding.toEmbedding .rv s →
    HasOneGeneratorTConvexInputs (T := T) terms d.orderedTerms e.orderedTerms
      d.ring e.ring d.powers e.powers d.rvPowers e.rvPowers d.convex e.convex A a b

set_option linter.style.haveILetI false in
/-- Theorem 2.16 for the uniform interpreted theory, from canonical
presentation of its models and the stated one-generator rank and
residue inputs. It uses the generated-field adjunction directly. -/
theorem exists_qf_equivalent_of_tconvex_adjunction_inputs
    [T.IsUniversal] (hQE : EliminatesQuantifiers T) (hQEconvex : EliminatesQuantifiers Tconvex)
    (hOM : IsOMinimalFieldTheory.{u, v, max u v w a} T)
    (I : QuotientInterpretation (convexLanguage L) L E) (minusOne : L.Term Empty)
    (hModel : ∀ {X : TCsort → Type (max u v w a)} (M : SortedStructure L E X),
      (∀ φ ∈ interpretedValuedTheory I minusOne Tconvex, φ.realize M) →
      ∃ d : CanonicalQEModel T Tconvex terms graph (X .vf),
        Nonempty (SortedIsomorphism M d.structureOn))
    (hInputs : ∀ {K F : Type (max u v w a)}
      (d : CanonicalQEModel T Tconvex terms graph K)
      (e : CanonicalQEModel T Tconvex terms graph F), d.hasAdjunctionInputs e)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : (interpretedValuedTheory I minusOne Tconvex).PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  apply exists_qf_equivalent_of_interpreted_representative_step I minusOne hQEconvex _ φ
  intro X Y M N hM hN R A t ht hFresh
  obtain ⟨d, ⟨i⟩⟩ := hModel M hM
  obtain ⟨e, ⟨j⟩⟩ := hModel N hN
  apply A.exists_extension_of_isomorphic_step i j t ht hFresh
  intro W B s hs hsFresh
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  letI := e.field
  letI := e.order
  letI := e.orderedRing
  letI := e.languageStructure
  letI := e.residueStructure
  letI := e.models
  have hn : s ∉ rv d.ring '' B.source.carrier .vf := by
    rwa [← show d.structureOn.rvMap = rv d.ring from funext (canonicalStructure_rvMap d.ring d.convex _)]
  obtain ⟨C, hBC, hC⟩ := exists_fixedRVExtension_of_tconvex_inputs terms
    d.orderedTerms e.orderedTerms d.ring e.ring d.powers e.powers d.rvPowers e.rvPowers
    d.convex e.convex B hOM hQE (hInputs d e B) s hs hn
  refine ⟨C, hBC, ?_⟩
  simpa only [CanonicalQEModel.structureOn, canonicalStructure_rvMap] using hC

set_option linter.style.haveILetI false in
/-- An interpreted model with its recovered valued-field data is
isomorphic to the canonical expansion supplied by those data. -/
theorem CanonicalQEModel.exists_isomorphism_of_recovery
    {X : TCsort → Type z} (M : SortedStructure L E X)
    (d : CanonicalQEModel T Tconvex terms graph (X .vf))
    (I : QuotientInterpretation (convexLanguage L) L E) (minusOne : L.Term Empty)
    (hM : ∀ φ ∈ interpretedValuedTheory I minusOne Tconvex, φ.realize M) :
    letI := d.field
    letI := d.languageStructure
    letI := convexStructure d.ring L
    valuedStructureOfSorted M (recoveredRing M minusOne) = convexStructure d.ring L →
    ∀ R : RealizesQuotientInterpretation I (A := X .vf) d.structureOn,
      (∀ x, R.rep .vf x = x) → (∀ x, R.rep .rv x = rv d.ring x) →
      Nonempty (SortedIsomorphism M d.structureOn) := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := convexStructure d.ring L
  intro hRec R hVF hRV
  obtain ⟨e, _, _⟩ := exists_canonicalIsomorphism_of_interpretedValuedModel M I minusOne
    d.ring d.convex d.rvPowers.pow Tconvex hRec hM R hVF hRV
  exact ⟨e⟩

set_option linter.style.haveILetI false in
/-- The canonical presentation required for QE follows from the
valued-field model data and the uniform interpretation on those models. -/
theorem exists_qf_equivalent_of_recovered_tconvex_inputs
    [T.IsUniversal] (hQE : EliminatesQuantifiers T) (hQEconvex : EliminatesQuantifiers Tconvex)
    (hOM : IsOMinimalFieldTheory.{u, v, max u v w a} T)
    (I : QuotientInterpretation (convexLanguage L) L E) (minusOne : L.Term Empty)
    (hRecover : ∀ (K : Type (max u v w a)) (V : (convexLanguage L).Structure K),
      letI := V
      K ⊨ Tconvex →
      ∃ d : CanonicalQEModel T Tconvex terms graph K,
        letI := d.field
        letI := d.languageStructure
        letI := convexStructure d.ring L
        V = convexStructure d.ring L ∧
          ∃ R : RealizesQuotientInterpretation I (A := K) d.structureOn,
            (∀ x, R.rep .vf x = x) ∧ (∀ x, R.rep .rv x = rv d.ring x))
    (hInputs : ∀ {K F : Type (max u v w a)}
      (d : CanonicalQEModel T Tconvex terms graph K)
      (e : CanonicalQEModel T Tconvex terms graph F), d.hasAdjunctionInputs e)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : (interpretedValuedTheory I minusOne Tconvex).PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  apply exists_qf_equivalent_of_tconvex_adjunction_inputs hQE hQEconvex hOM I minusOne _ hInputs φ
  intro X M hM
  let V := valuedStructureOfSorted M (recoveredRing M minusOne)
  letI := V
  have hV : X .vf ⊨ Tconvex := ((models_interpretedValuedTheory_iff M I minusOne Tconvex).mp hM).1
  obtain ⟨d, hRec, R, hVF, hRV⟩ := hRecover (X .vf) V hV
  exact ⟨d, d.exists_isomorphism_of_recovery M I minusOne hM hRec R hVF hRV⟩

set_option linter.style.haveILetI false in
/-- A field-language substructure gives the VF-generated expansion
with exactly its own leading terms. The cited natural residue map
supplies compatibility with the residue-language primitives. -/
theorem CanonicalQEModel.exists_vfGenerated_over_fieldSubstructure {K : Type z}
    (d : CanonicalQEModel T Tconvex terms graph K) [T.IsUniversal] (hQE : EliminatesQuantifiers T) :
    letI := d.field
    letI := d.order
    letI := d.orderedRing
    letI := d.languageStructure
    letI := d.residueStructure
    ∀ (B : L.Substructure K),
      letI := fieldOnFieldSubstructure terms d.orderedTerms B
      let f := ringInclusionOfFieldSubstructure terms d.orderedTerms B
      let Q := d.ring.comap f
      (∃ R : L.Structure (Residue Q), letI := R
        ∃ i : Residue Q ↪[L] Residue d.ring,
          ∀ x, i x = mapResidue Q d.ring f (fun _ => Iff.rfl) x) →
      ∃ S : SortedSubstructure d.structureOn,
        S.carrier .vf = (B : Set K) ∧ S.carrier .rv = rv d.ring '' (B : Set K) ∧
          S.structureOn.IsVFGenerated := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  intro B
  letI := fieldOnFieldSubstructure terms d.orderedTerms B
  letI := strictOrderedRingOnFieldSubstructure terms d.orderedTerms B
  let f := ringInclusionOfFieldSubstructure terms d.orderedTerms B
  let Q := d.ring.comap f
  change (∃ R : L.Structure (Residue Q), letI := R
    ∃ i : Residue Q ↪[L] Residue d.ring,
      ∀ x, i x = mapResidue Q d.ring f (fun _ => Iff.rfl) x) → _
  rintro ⟨R, res, hres⟩
  letI := R
  let j : B ↪ₑ[L] K := elementaryEmbeddingOfQE hQE B.subtype
  have hj (x : B) : j x = f x := (ringInclusionOfFieldSubstructure_apply terms d.orderedTerms B x).symm
  have hmono : StrictMono f := by
    intro x y h
    rw [ringInclusionOfFieldSubstructure_apply, ringInclusionOfFieldSubstructure_apply]
    exact h
  have hf : RespectsValuationRing Q d.ring f := fun _ => Iff.rfl
  have hQ : IsOrderConvex Q := convex_comap_valuationRing d.ring f d.convex hmono.monotone
  obtain ⟨g⟩ := exists_namedFieldPowers_of_elementary j f hj hmono d.powers
  obtain ⟨P⟩ := exists_namedRVPowers_of_valued_embedding j f hj hmono g d.powers Q d.ring hf d.rvPowers
  obtain ⟨e, hVF, hRV⟩ := exists_canonicalEmbedding_of_elementary_field Q d.ring hQ d.convex
    P.pow d.rvPowers.pow j f hj hf hmono res hres g.pow d.powers.pow graph g.defines d.powers.defines
    P.agrees d.rvPowers.agrees P.offPositive d.rvPowers.offPositive
  let S := e.rangeSubstructure
  have hSurj : (canonicalStructure (L := L) Q hQ P.pow).IsVFGenerated := by
    intro t
    rw [show (canonicalStructure (L := L) Q hQ P.pow).rvMap = rv Q from
      funext (canonicalStructure_rvMap Q hQ P.pow)]
    exact rv_surjective Q t
  refine ⟨S, ?_, ?_, e.rangeSubstructure_isVFGenerated hSurj⟩
  · change Set.range (e.toEmbedding .vf) = (B : Set K)
    rw [show (e.toEmbedding .vf : B → K) = Subtype.val from funext hVF]
    exact Subtype.range_coe
  · change Set.range (e.toEmbedding .rv) = rv d.ring '' (B : Set K)
    ext t
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨x, rfl⟩ := rv_surjective Q r
      refine ⟨x.val, x.property, ?_⟩
      rwa [hRV, mapRV_rv, ringInclusionOfFieldSubstructure_apply] at hr
    · rintro ⟨x, hx, rfl⟩
      refine ⟨rv Q ⟨x, hx⟩, ?_⟩
      rw [hRV, mapRV_rv, ringInclusionOfFieldSubstructure_apply]

set_option linter.style.haveILetI false in
/-- Naming a family of field elements gives a VF-generated
substructure, with field carrier its field-language term closure. -/
theorem CanonicalQEModel.field_termGenerated_isVFGenerated {K : Type z}
    (d : CanonicalQEModel T Tconvex terms graph K) [T.IsUniversal] (hQE : EliminatesQuantifiers T)
    {Var : TCsort → Type*} [IsEmpty (Var .rv)]
    (x : ∀ s, Var s → (letI := d.field; CanonicalSort d.ring s)) :
    letI := d.field
    letI := d.order
    letI := d.orderedRing
    letI := d.languageStructure
    letI := d.residueStructure
    let B := Substructure.closure L (Set.range (x .vf))
    letI := fieldOnFieldSubstructure terms d.orderedTerms B
    let f := ringInclusionOfFieldSubstructure terms d.orderedTerms B
    let Q := d.ring.comap f
    (∃ R : L.Structure (Residue Q), letI := R
      ∃ i : Residue Q ↪[L] Residue d.ring,
        ∀ y, i y = mapResidue Q d.ring f (fun _ => Iff.rfl) y) →
    (d.structureOn.termGenerated x).structureOn.IsVFGenerated := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  let B := Substructure.closure L (Set.range (x .vf))
  letI := fieldOnFieldSubstructure terms d.orderedTerms B
  let f := ringInclusionOfFieldSubstructure terms d.orderedTerms B
  let Q := d.ring.comap f
  change (∃ R : L.Structure (Residue Q), letI := R
    ∃ i : Residue Q ↪[L] Residue d.ring,
      ∀ y, i y = mapResidue Q d.ring f (fun _ => Iff.rfl) y) → _
  intro hRes
  obtain ⟨S, hS, _, hGen⟩ := d.exists_vfGenerated_over_fieldSubstructure hQE B hRes
  exact vfGenerated_termGenerated_by_field d.ring d.convex d.rvPowers.pow x S hS hGen

set_option linter.style.haveILetI false in
/-- Adjoin field representatives of the named leading terms while
keeping exactly the original RV sort, as in Remark 2.27. -/
theorem CanonicalQEModel.exists_vfGenerated_extension {K : Type z}
    (d : CanonicalQEModel T Tconvex terms graph K) [T.IsUniversal]
    (hQE : EliminatesQuantifiers T) (hOM : IsOMinimalFieldTheory.{u, v, z} T)
    (hInput : d.hasAdjunctionInputs d) (S : SortedSubstructure d.structureOn) :
    ∃ B : SortedSubstructure d.structureOn,
      (∀ s, S.carrier s ⊆ B.carrier s) ∧ B.carrier .rv = S.carrier .rv ∧
        B.structureOn.IsVFGenerated := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  let A : FixedRVLift d.structureOn d.structureOn (S.carrier .rv) :=
    ⟨S, rfl, S.inclusion⟩
  obtain ⟨B, hAB, hB⟩ := A.exists_vfGenerated_extension (by
    intro C _ t ht hf
    have hrv : d.structureOn.rvMap = rv d.ring :=
      funext (canonicalStructure_rvMap d.ring d.convex d.rvPowers.pow)
    rw [hrv] at hf ⊢
    exact exists_fixedRVExtension_of_tconvex_inputs terms
      d.orderedTerms d.orderedTerms d.ring d.ring d.powers d.powers d.rvPowers d.rvPowers
      d.convex d.convex C hOM hQE (hInput C) t ht hf)
  exact ⟨B.source, (FixedRVLift.le_iff_extends A B).mp hAB |>.choose, B.rv_eq, hB⟩

set_option linter.style.haveILetI false in
/-- RV definable closure in Remark 2.27 using the representative
construction from Theorem 2.16, including the independent-line
argument at a trivial value base. -/
theorem CanonicalQEModel.rvDefinablyClosed {K : Type (max u v w a)}
    (d : CanonicalQEModel T Tconvex terms graph K) [T.IsUniversal]
    (hQE : EliminatesQuantifiers T) (hOM : IsOMinimalFieldTheory.{u, v, max u v w a} T)
    (hInput : d.hasAdjunctionInputs d) (Tsorted : SortedTheory L E)
    (hQEs : ∀ {Var : TCsort → Type (max u v w a)} (φ : SortedFormula L E Var),
      ∃ ψ, ψ.IsQF ∧ ∀ N : Tsorted.PointedModel Var, N.realizes φ ↔ N.realizes ψ)
    (hM : ∀ φ ∈ Tsorted, φ.realize d.structureOn) :
    letI := d.field
    letI := d.order
    letI := d.orderedRing
    letI := d.languageStructure
    letI := d.residueStructure
    (∀ S : SortedSubstructure d.structureOn, S.structureOn.IsVFGenerated →
      (∃ t ∈ S.carrier .rv, t ≠ 0 ∧ unsignedValue d.ring t ≠ 1) →
      ∀ φ ∈ Tsorted, φ.realize S.structureOn) →
    ∀ (a b : PositiveField K),
      (letI := unsignedValueModule d.ring d.powers.pow d.rvPowers.pow d.rvPowers.agrees
        d.powers.zero d.powers.one d.powers.add d.powers.mul d.rvPowers.units
       LinearIndependent E (![positiveFieldValue d.ring a, positiveFieldValue d.ring b])) →
      ∀ S : SortedSubstructure d.structureOn,
        RVDefinablyClosed d.structureOn (S.carrier .rv) := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  intro hProper a b hab S
  apply rvDefinablyClosed_of_fixedRV_model_extensions.{u, v, w, a}
    d.ring d.convex d.powers.pow d.rvPowers.pow d.rvPowers.agrees
    d.powers.zero d.powers.one d.powers.add d.powers.mul d.rvPowers.units d.rvPowers.offPositive
    Tsorted hQEs hM _ a b hab S
  intro A hA
  obtain ⟨B, _, hBV, hBG⟩ := d.exists_vfGenerated_extension hQE hOM hInput A
  have hB : ∃ t ∈ B.carrier .rv, t ≠ 0 ∧ unsignedValue d.ring t ≠ 1 := hBV.symm ▸ hA
  refine ⟨B, hBV, hProper B hBG hB, ?_⟩
  obtain ⟨t, ht, _⟩ := hB
  intro s
  cases s with
  | rv => exact ⟨⟨t, ht⟩⟩
  | vf => exact ⟨(hBG ⟨t, ht⟩).choose⟩

end GeneralizedEuler.Section2
