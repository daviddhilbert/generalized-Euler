module

public import Section2.GeneratedRVAdjunction
public import Section2.ImmediateFieldLift
public import Section2.ImmediateTranslate
public import Section2.ImmediateBackAndForth

/-! The prescribed map at a translated generator in Lemma 2.22. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z

variable {L : Language.{u, v}} {E : Type w}
  {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (terms : OrderedFieldTerms L) (hK : InterpretsOrderedFieldTerms (A := K) terms)
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)
  {R : Set (RV0 O)}
  (A : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure O hO P) R)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem le_adjoinFieldRepresentative_of_mem (D B : L.Substructure K) (x : K)
    (hD : D ≤ B) (hx : x ∈ B) : adjoinFieldRepresentative D x ≤ B := by
  apply Substructure.closure_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl d => exact hD d.property
  | inr => exact hx

include hK

omit [IsStrictOrderedRing K] in
/-- Translating the generator by an old field element preserves the
generated field. -/
theorem adjoinFieldRepresentative_sub_eq (D : L.Substructure K) (a : K) (d : D) :
    adjoinFieldRepresentative D (a - d.val) = adjoinFieldRepresentative D a := by
  let U := adjoinFieldRepresentative D (a - d.val)
  let V := adjoinFieldRepresentative D a
  have hDU := le_adjoinFieldRepresentative D (a - d.val)
  have hDV := le_adjoinFieldRepresentative D a
  apply le_antisymm
  · apply le_adjoinFieldRepresentative_of_mem D V _ hDV
    let K₀ := subfieldOfFieldSubstructure terms hK V
    exact (mem_subfieldOfFieldSubstructure terms hK V _).mp (K₀.sub_mem
      ((mem_subfieldOfFieldSubstructure terms hK V _).mpr (mem_adjoinFieldRepresentative D a))
      ((mem_subfieldOfFieldSubstructure terms hK V _).mpr (hDV d.property)))
  · apply le_adjoinFieldRepresentative_of_mem D U _ hDU
    let K₀ := subfieldOfFieldSubstructure terms hK U
    have hx := K₀.add_mem
      ((mem_subfieldOfFieldSubstructure terms hK U _).mpr (mem_adjoinFieldRepresentative D (a - d.val)))
      ((mem_subfieldOfFieldSubstructure terms hK U _).mpr (hDU d.property))
    exact (mem_subfieldOfFieldSubstructure terms hK U _).mp (sub_add_cancel a d.val ▸ hx)

omit [IsStrictOrderedRing K] in
/-- Negation of the new generator leaves the field it generates unchanged. -/
theorem adjoinFieldRepresentative_neg_eq (D : L.Substructure K) (a : K) :
    adjoinFieldRepresentative D (-a) = adjoinFieldRepresentative D a := by
  have le_neg (x : K) : adjoinFieldRepresentative D (-x) ≤ adjoinFieldRepresentative D x := by
    apply le_adjoinFieldRepresentative_of_mem _ _ _ (le_adjoinFieldRepresentative D x)
    let B := adjoinFieldRepresentative D x
    let D₀ := subfieldOfFieldSubstructure terms hK B
    exact (mem_subfieldOfFieldSubstructure terms hK B _).mp (D₀.neg_mem
      ((mem_subfieldOfFieldSubstructure terms hK B _).mpr (mem_adjoinFieldRepresentative D x)))
  apply (le_neg a).antisymm
  simpa only [neg_neg] using le_neg (-a)

set_option linter.style.haveILetI false in
/-- A lift at a translated generator sends the original generator to
the requested image, since the translation uses an element of the
old field. -/
theorem fixedRVExtension_sends_original_of_translate
    {C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure O hO P) R}
    (hAC : A ≤ C) (d : A.source.carrier .vf) (a b : K)
    (haC : a - d.val ∈ C.source.carrier .vf)
    (haMap : C.embedding.toEmbedding .vf ⟨a - d.val, haC⟩ = b - A.embedding.toEmbedding .vf d) :
    ∃ hx : a ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨a, hx⟩ = b := by
  obtain ⟨hDom, hMap⟩ := (FixedRVLift.le_iff_extends A C).mp hAC
  let B := vfReductOfSortedSubstructure O hO P C.source
  letI := fieldOnFieldSubstructure terms hK B
  let f := fieldEmbeddingOfSorted O O hO hO P P C.source C.embedding
  let hB := interpretsOrderedFieldTerms_fieldSubstructure terms hK B
  let q := ringHomOfFieldEmbedding terms hB hK f
  let c : B := ⟨a - d.val, haC⟩
  let d' : B := ⟨d.val, hDom .vf d.property⟩
  have hSum : (c + d').val = a := by
    rw [← ringInclusionOfFieldSubstructure_apply terms hK B (c + d'), map_add,
      ringInclusionOfFieldSubstructure_apply, ringInclusionOfFieldSubstructure_apply]
    exact sub_add_cancel a d.val
  have hc : q c = b - A.embedding.toEmbedding .vf d := by
    rw [ringHomOfFieldEmbedding_apply]
    exact haMap
  have hd : q d' = A.embedding.toEmbedding .vf d := by
    rw [ringHomOfFieldEmbedding_apply]
    exact (hMap .vf d).symm
  have hq : f (c + d') = b := by
    rw [← ringHomOfFieldEmbedding_apply terms hB hK f (c + d'), map_add, hc, hd, sub_add_cancel]
  refine ⟨hSum ▸ (c + d').property, ?_⟩
  have he : (⟨a, hSum ▸ (c + d').property⟩ : C.source.carrier .vf) = c + d' := Subtype.ext hSum.symm
  rw [he]
  exact hq

set_option linter.style.haveILetI false in
/-- The sign of the representative can be changed while keeping the
fixed-RV extension at its specified image. -/
theorem fixedRVExtension_sends_original_of_negation
    {C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure O hO P) R}
    (a b : K) (haC : -a ∈ C.source.carrier .vf)
    (haMap : C.embedding.toEmbedding .vf ⟨-a, haC⟩ = -b) :
    ∃ hx : a ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨a, hx⟩ = b := by
  let B := vfReductOfSortedSubstructure O hO P C.source
  letI := fieldOnFieldSubstructure terms hK B
  let f := fieldEmbeddingOfSorted O O hO hO P P C.source C.embedding
  let hB := interpretsOrderedFieldTerms_fieldSubstructure terms hK B
  let q := ringHomOfFieldEmbedding terms hB hK f
  let c : B := ⟨-a, haC⟩
  have hc : (-c).val = a := by
    rw [← ringInclusionOfFieldSubstructure_apply terms hK B (-c), map_neg,
      ringInclusionOfFieldSubstructure_apply]
    exact neg_neg a
  have hqc : q c = -b := by rw [ringHomOfFieldEmbedding_apply]; exact haMap
  have hq : f (-c) = b := by
    rw [← ringHomOfFieldEmbedding_apply terms hB hK f (-c), map_neg, hqc, neg_neg]
  refine ⟨hc ▸ (-c).property, ?_⟩
  have he : (⟨a, hc ▸ (-c).property⟩ : C.source.carrier .vf) = -c := Subtype.ext hc.symm
  rw [he]
  exact hq

include hO in
omit [L.Structure (Residue O)] in
/-- The leading-term and weak-immediacy inputs give the translate
detector used in Lemma 2.22. The old field may be trivially valued. -/
theorem detects_new_RV_of_valuation_properties
    (hCases : ∀ (D : L.Substructure K) (x : K), x ∉ D →
      let V := subfieldOfFieldSubstructure terms hK D
      let B := subfieldOfFieldSubstructure terms hK (adjoinFieldRepresentative D x)
      (∀ y ∈ V, y ≠ 0 → O.valuation y = 1) ∨
        ((∀ y ∈ B, O.valuation y ∉ O.valuation '' (V : Set K) →
          ∃ d ∈ V, O.valuation (x - d) ∉ O.valuation '' (V : Set K)) ∧
          (WeakImmediacyTransfer O V B x ∨
            ∃ Q : ValuationSubring K, IsOrderConvex Q ∧
              ∃ y ∈ B, Q.valuation y ∉ Q.valuation '' (V : Set K) ∧
                (∀ z ∈ B, Q.valuation z ∉ Q.valuation '' (V : Set K) →
                  ∃ d ∈ V, Q.valuation (x - d) ∉ Q.valuation '' (V : Set K))))) :
    ∀ (D : L.Substructure K) (x : K),
      (∃ y ∈ adjoinFieldRepresentative D x, rv O y ∉ rv O '' (D : Set K)) →
      ∃ c : D, rv O (x - c.val) ∉ rv O '' (D : Set K) := by
  intro D x
  rintro ⟨y, hy, hn⟩
  let V := subfieldOfFieldSubstructure terms hK D
  let B := subfieldOfFieldSubstructure terms hK (adjoinFieldRepresentative D x)
  have hx : x ∉ D := fun hx => hn ⟨y, le_adjoinFieldRepresentative_of_mem D D x le_rfl hx hy, rfl⟩
  have hx' : x ∉ V := fun h => hx ((mem_subfieldOfFieldSubstructure terms hK D x).mp h)
  have hV : (V : Set K) = D := Set.ext (mem_subfieldOfFieldSubstructure terms hK D)
  have hVB : V ≤ B := by
    intro z hz
    exact (mem_subfieldOfFieldSubstructure terms hK (adjoinFieldRepresentative D x) z).mpr
      (le_adjoinFieldRepresentative D x ((mem_subfieldOfFieldSubstructure terms hK D z).mp hz))
  have hFresh : fieldRV O B ≠ fieldRV O V := by
    intro he
    have hyB := (mem_subfieldOfFieldSubstructure terms hK (adjoinFieldRepresentative D x) y).mpr hy
    have hm : rv O y ∈ fieldRV O V := he ▸ ⟨y, hyB, rfl⟩
    change rv O y ∈ rv O '' (V : Set K) at hm
    exact hn (hV ▸ hm)
  have hNew : ∃ d ∈ V, rv O (x - d) ∉ fieldRV O V := by
    rcases hCases D x hx with ht | ⟨hVal, hResidue⟩
    · exact exists_new_translate_of_trivially_valued_field O hx' ht
    · exact exists_new_translate_of_changed_fieldRV O hO hVB hx' hFresh hVal hResidue
  obtain ⟨c, hc, hr⟩ := hNew
  exact ⟨⟨c, (mem_subfieldOfFieldSubstructure terms hK D c).mp hc⟩,
    fun h => hr (show rv O (x - c) ∈ rv O '' (V : Set K) from hV.symm ▸ h)⟩

section MatchedTranslates

variable {T : L.Theory} [T.IsUniversal] [K ⊨ T]
  (Aall : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure O hO P) Set.univ)
  (hfix : ∀ t : Aall.source.carrier .rv, Aall.embedding.toEmbedding .rv t = t.val)

include hfix in
omit hK in
private theorem rv_image_of_fixedRV (c : Aall.source.carrier .vf) :
    rv O (Aall.embedding.toEmbedding .vf c) = rv O c.val := by
  have h := Aall.embedding.map_rv c
  rw [canonicalStructure_rvMap, hfix, canonicalSubstructure_rvMap O hO P Aall.source] at h
  exact h.symm

set_option linter.style.haveILetI false in
include hfix in
/-- The two branches of Lemma 2.22. A fresh translated leading term
uses the prescribed adjunction. If the source RV image is unchanged,
a changed target RV image would give a new target translate, in
contradiction with the matching hypothesis. -/
theorem exists_fixedRVExtension_of_matched_translates
    (hOM : IsOMinimalFieldTheory.{u, v, z} T) (hQE : EliminatesQuantifiers T)
    (a b : K) (hMatch : ∀ c : Aall.source.carrier .vf,
      rv O (a - c.val) = rv O (b - Aall.embedding.toEmbedding .vf c))
    (hDetect : ∀ (D : L.Substructure K) (x : K),
      (∃ y ∈ adjoinFieldRepresentative D x, rv O y ∉ rv O '' (D : Set K)) →
      ∃ c : D, rv O (x - c.val) ∉ rv O '' (D : Set K))
    (hPositive : ∀ (x y : K), 0 < x → rv O x = rv O y →
      rv O x ∉ rv O '' Aall.source.carrier .vf →
      ∃ C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure O hO P) Set.univ,
        Aall ≤ C ∧ C.source.carrier .vf =
          (adjoinFieldRepresentative (vfReductOfSortedSubstructure O hO P Aall.source) x : Set K) ∧
        ∃ hx : x ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨x, hx⟩ = y) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure O hO P) Set.univ,
      Aall ≤ C ∧ C.source.carrier .vf =
        (adjoinFieldRepresentative (vfReductOfSortedSubstructure O hO P Aall.source) a : Set K) ∧
      ∃ ha : a ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨a, ha⟩ = b := by
  let D := vfReductOfSortedSubstructure O hO P Aall.source
  let B := adjoinFieldRepresentative D a
  by_cases hNew : ∃ y ∈ B, rv O y ∉ rv O '' Aall.source.carrier .vf
  · obtain ⟨c, hc⟩ := hDetect D a hNew
    let x := a - c.val
    let y := b - Aall.embedding.toEmbedding .vf c
    have hxy : rv O x = rv O y := hMatch c
    have hx0 : x ≠ 0 := by
      intro hx
      apply hc
      exact ⟨0, (mem_subfieldOfFieldSubstructure terms hK D _).mp
        (subfieldOfFieldSubstructure terms hK D).zero_mem, (congrArg (rv O) hx).symm⟩
    suffices extend : ∃ C : FixedRVLift (canonicalStructure (L := L) O hO P)
        (canonicalStructure O hO P) Set.univ,
        Aall ≤ C ∧ C.source.carrier .vf = (adjoinFieldRepresentative D x : Set K) ∧
        ∃ hx : x ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨x, hx⟩ = y by
      obtain ⟨C, hAC, hC, hx, hy⟩ := extend
      exact ⟨C, hAC, by rw [hC, adjoinFieldRepresentative_sub_eq terms hK D a c],
        fixedRVExtension_sends_original_of_translate terms hK O hO P Aall hAC c a b hx hy⟩
    rcases lt_or_gt_of_ne hx0 with h | h
    · have he : rv O (-x) = rv O (-y) := by
        rw [← neg_one_mul x, ← neg_one_mul y, map_mul, map_mul, hxy]
      have hn : rv O (-x) ∉ rv O '' Aall.source.carrier .vf := by
        rintro ⟨d, hd, he⟩
        have hy := congrArg (rv O (-1) * ·) he
        rw [← map_mul, ← map_mul, neg_one_mul, neg_one_mul, neg_neg] at hy
        have hd' : d ∈ subfieldOfFieldSubstructure terms hK D :=
          (mem_subfieldOfFieldSubstructure terms hK D d).mpr hd
        exact hc ⟨-d, (mem_subfieldOfFieldSubstructure terms hK D _).mp
          ((subfieldOfFieldSubstructure terms hK D).neg_mem hd'), hy⟩
      obtain ⟨C, hAC, hC, hX, hY⟩ := hPositive (-x) (-y) (neg_pos.mpr h) he hn
      exact ⟨C, hAC, by rw [hC, adjoinFieldRepresentative_neg_eq terms hK D x],
        fixedRVExtension_sends_original_of_negation terms hK O hO P x y hX hY⟩
    · exact hPositive x y h hxy hc
  · have hOld (x : B) : rv O x.val ∈ rv O '' Aall.source.carrier .vf :=
      Classical.byContradiction (fun hn => hNew ⟨x.val, x.property, hn⟩)
    let k := fieldEmbeddingOfSorted O O hO hO P P Aall.source Aall.embedding
    have hcut : ∀ c : D, (c.val < a ↔ k c < b) ∧ (a < c.val ↔ b < k c) :=
      sameCut_of_equal_translate_rv O hO k hMatch
    let gen : B := ⟨a, mem_adjoinFieldRepresentative D a⟩
    have hf : ∃ f : B ↪[L] K, f gen = b ∧
        ∀ c : D, f ⟨c.val, le_adjoinFieldRepresentative D a c.property⟩ = k c :=
      exists_simpleFieldEmbedding_of_model_cut terms hK hK hOM hQE D k a b hcut
    obtain ⟨f, hf, hField⟩ := hf
    have hRight (x : B) : rv O (f x) ∈ Set.range
        (fun c : Aall.source.carrier .vf => rv O (Aall.embedding.toEmbedding .vf c)) := by
      by_contra hn
      have hRange := adjoinFieldRepresentative_range_eq D k a b f hf hField
      have hY : f x ∈ adjoinFieldRepresentative k.toHom.range b :=
        hRange ▸ f.toHom.mem_range_self x
      have hn' : rv O (f x) ∉ rv O '' (k.toHom.range : Set K) := by
        rintro ⟨y, ⟨c, hc⟩, he⟩
        exact hn ⟨c, (congrArg (rv O) hc).trans he⟩
      obtain ⟨d', hd'⟩ := hDetect k.toHom.range b ⟨f x, hY, hn'⟩
      obtain ⟨d, hd⟩ := d'.property
      have hdB : a - d.val ∈ B := by
        change a - d.val ∈ adjoinFieldRepresentative D a
        rw [← adjoinFieldRepresentative_sub_eq terms hK D a d]
        exact mem_adjoinFieldRepresentative D (a - d.val)
      obtain ⟨c, hc, he⟩ := hOld ⟨a - d.val, hdB⟩
      have hmatch : rv O (a - d.val) = rv O (b - d'.val) :=
        (hMatch d).trans (congrArg (fun t => rv O (b - t)) hd)
      let c' : Aall.source.carrier .vf := ⟨c, hc⟩
      exact hd' ⟨k c', ⟨c', rfl⟩,
        (rv_image_of_fixedRV O hO P Aall hfix c').trans (he.trans hmatch)⟩
    letI := fieldOnFieldSubstructure terms hK B
    letI := strictOrderedRingOnFieldSubstructure terms hK B
    let hB := interpretsOrderedFieldTerms_fieldSubstructure terms hK B
    let p := ringInclusionOfFieldSubstructure terms hK B
    let q := ringHomOfFieldEmbedding terms hB hK f
    let U := (subfieldOfFieldSubstructure terms hK D).comap p
    have hp : StrictMono p := by
      intro x y h
      rw [ringInclusionOfFieldSubstructure_apply, ringInclusionOfFieldSubstructure_apply]
      exact h
    have hU (x : B) : x ∈ U ↔ x.val ∈ D := by
      change p x ∈ subfieldOfFieldSubstructure terms hK D ↔ x.val ∈ D
      rw [ringInclusionOfFieldSubstructure_apply, mem_subfieldOfFieldSubstructure]
    let hbase : Aall.source.carrier .vf ⊆ B := le_adjoinFieldRepresentative D a
    have hRep : Set.range (fun c : Aall.source.carrier .vf => (⟨c.val, hbase c.property⟩ : B)) = (U : Set B) := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact (hU _).mpr c.property
      · intro hx
        exact ⟨⟨x.val, (hU x).mp hx⟩, Subtype.ext rfl⟩
    let m : B := -1
    have hminus : m.val = -1 := by
      rw [← ringInclusionOfFieldSubstructure_apply terms hK B m, map_neg, map_one]
    have hmU : m ∈ U := U.neg_mem U.one_mem
    let minusOne : Aall.source.carrier .vf := ⟨m.val, (hU m).mp hmU⟩
    have hminus' : Aall.embedding.toEmbedding .vf minusOne = -1 := by
      change k minusOne = -1
      rw [← hField minusOne]
      change f m = -1
      rw [← ringHomOfFieldEmbedding_apply terms hB hK f m, map_neg, map_one]
    obtain ⟨C, hAC, hC, hMap⟩ :=
      exists_fixedRVExtension_of_unchanged_RV_images O O hO hO P P Aall B f hbase hField
        p q hp.monotone (strictMono_ringHomOfFieldEmbedding terms hB hK f).monotone
        id Function.surjective_id (ringInclusionOfFieldSubstructure_apply terms hK B)
        (ringHomOfFieldEmbedding_apply terms hB hK f) U hRep minusOne hminus hminus' hOld hRight
    have haC : a ∈ C.source.carrier .vf := hC.symm ▸ gen.property
    exact ⟨C, hAC, hC, haC, (hMap gen haC).trans hf⟩

end MatchedTranslates

section GeneratedIsomorphism

variable [Field E] {T : L.Theory} [T.IsUniversal] [K ⊨ T]
  {graph : E → L.Formula (Fin 2)} (g : NamedFieldPowers K graph) (powers : NamedRVPowers O g.pow)

/-- Lemma 2.22 on the generated sorted structures. The enlargement
with all RV makes the representative available for the proof. The
result restricts to the substructures generated by the original
parameters and the specified field points. -/
theorem exists_immediate_isomorphism_of_matched_translates
    (hOM : IsOMinimalFieldTheory.{u, v, z} T) (hQE : EliminatesQuantifiers T)
    (S : SortedSubstructure (canonicalStructure (L := L) O hO powers.pow))
    (e : SortedEmbedding S.structureOn (canonicalStructure O hO powers.pow))
    (he : ∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val)
    (a b : K) (hMatch : ∀ c : S.carrier .vf, rv O (a - c.val) = rv O (b - e.toEmbedding .vf c))
    (hDetect : ∀ (D : L.Substructure K) (x : K),
      (∃ y ∈ adjoinFieldRepresentative D x, rv O y ∉ rv O '' (D : Set K)) →
      ∃ c : D, rv O (x - c.val) ∉ rv O '' (D : Set K))
    (hInput :
      let B := e.extendImmediateByIdentity S he
      ∀ (x : PositiveField K) (y : K) (s : B.source.carrier .rv),
        s.val ∉ rv O '' B.source.carrier .vf →
        rv O x.val = s.val → rv O y = B.embedding.toEmbedding .rv s →
        HasOneGeneratorTConvexInputs (T := T) terms hK hK O O g g powers powers hO hO B x y) :
    let M := canonicalStructure (L := L) O hO powers.pow
    let Var : TCsort → Type z
      | .vf => S.carrier .vf ⊕ Unit
      | .rv => S.carrier .rv
    let x : ∀ s, Var s → CanonicalSort O s
      | .vf => Sum.elim Subtype.val (fun _ => a)
      | .rv => Subtype.val
    let y : ∀ s, Var s → CanonicalSort O s
      | .vf => Sum.elim (e.toEmbedding .vf) (fun _ => b)
      | .rv => e.toEmbedding .rv
    ∃ f : SortedIsomorphism (M.termGenerated x).structureOn (M.termGenerated y).structureOn,
      (∀ s i, (f.toEmbedding s (M.termGeneratedAssignment x s i)).val = y s i) ∧
      ∀ t : (M.termGenerated x).carrier .rv, (f.toEmbedding .rv t).val = t.val := by
  let M := canonicalStructure (L := L) O hO powers.pow
  let A := e.extendImmediateByIdentity S he
  have hFix := e.extendImmediateByIdentity_fixesRV S he
  have hVF := e.extendImmediateByIdentity_carrier_vf S he
  have hTr (c : A.source.carrier .vf) :
      rv O (a - c.val) = rv O (b - A.embedding.toEmbedding .vf c) := by
    let p : S.carrier .vf := ⟨c.val, hVF ▸ c.property⟩
    rw [e.extendImmediateByIdentity_agrees S he .vf p c.property]
    exact hMatch p
  have hPositive (x y : K) (hx : 0 < x) (hxy : rv O x = rv O y)
      (hNew : rv O x ∉ rv O '' A.source.carrier .vf) :
      ∃ C : FixedRVLift M M Set.univ,
        A ≤ C ∧ C.source.carrier .vf =
          (adjoinFieldRepresentative (vfReductOfSortedSubstructure O hO powers.pow A.source) x : Set K) ∧
        ∃ hx : x ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨x, hx⟩ = y := by
    let s : A.source.carrier .rv := ⟨rv O x, A.rv_eq.symm ▸ Set.mem_univ _⟩
    have hr : rv O y = A.embedding.toEmbedding .rv s := hxy.symm.trans (hFix s).symm
    exact exists_fixedRVExtension_of_generated_adjunction terms hK hK O O g g powers powers
      hO hO A hOM hQE s hNew ⟨x, hx⟩ y rfl hr (hInput ⟨x, hx⟩ y s hNew rfl hr)
  obtain ⟨C, hAC, _, haC, haMap⟩ := exists_fixedRVExtension_of_matched_translates terms hK
    O hO powers.pow A hFix hOM hQE a b hTr hDetect hPositive
  have hFixC := fixesRV_of_extends hAC hFix
  obtain ⟨hDom, hMap⟩ := (FixedRVLift.le_iff_extends A C).mp hAC
  let Var : TCsort → Type z
    | .vf => S.carrier .vf ⊕ Unit
    | .rv => S.carrier .rv
  let x : ∀ s, Var s → CanonicalSort O s
    | .vf => Sum.elim Subtype.val (fun _ => a)
    | .rv => Subtype.val
  let y : ∀ s, Var s → CanonicalSort O s
    | .vf => Sum.elim (e.toEmbedding .vf) (fun _ => b)
    | .rv => e.toEmbedding .rv
  let names : ∀ s, Var s → C.source.carrier s
    | .vf => Sum.elim (fun c => ⟨c.val, hDom .vf (hVF.symm ▸ c.property)⟩) (fun _ => ⟨a, haC⟩)
    | .rv => fun t => ⟨t.val, C.rv_eq.symm ▸ Set.mem_univ _⟩
  have hX : (fun s i => (names s i).val) = x := by
    funext s i
    cases s with
    | vf => cases i <;> rfl
    | rv => rfl
  have hY : (fun s i => C.embedding.toEmbedding s (names s i)) = y := by
    funext s i
    cases s with
    | vf =>
      cases i with
      | inl c =>
        let m : A.source.carrier .vf := ⟨c.val, hVF.symm ▸ c.property⟩
        exact (hMap .vf m).symm.trans (e.extendImmediateByIdentity_agrees S he .vf c m.property)
      | inr i => exact haMap
    | rv => exact (hFixC (names .rv i)).trans (he i).symm
  change ∃ f : SortedIsomorphism (M.termGenerated x).structureOn (M.termGenerated y).structureOn,
    (∀ s (i : Var s), (f.toEmbedding s (M.termGeneratedAssignment x s i)).val = y s i) ∧
    ∀ t : (M.termGenerated x).carrier .rv, (f.toEmbedding .rv t).val = t.val
  rw [← hX, ← hY]
  obtain ⟨f, hf⟩ := exists_isomorphism_of_generated_images M C.source C.embedding names
  refine ⟨f, ?_, ?_⟩
  · intro s i
    rw [hf]
    rfl
  · intro t
    rw [hf]
    exact hFixC _

end GeneratedIsomorphism

end GeneralizedEuler.Section2
