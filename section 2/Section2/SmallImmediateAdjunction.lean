module

public import Section2.ImmediateAdjunction
public import Section2.SmallBackAndForth
public import Section2.CanonicalQuantifierElimination

/-! The representative step and saturation use only small field
domains in the immediate automorphism argument. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language Cardinal

universe u v w

variable {L : Language.{u, v}} {E : Type w}
  {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem card_fieldClosure_le {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (hL : #(Σ i, L.Functions i) ≤ c)
    (B : Set K) (hB : #B ≤ c) : #(Substructure.closure L B) ≤ c := by
  have h : #(Substructure.closure L B) ≤
      max ℵ₀ (#B + #(Σ i, L.Functions i)) := by
    simpa only [Cardinal.lift_id] using Substructure.lift_card_closure_le (L := L) (s := B)
  exact h.trans (max_le hc ((add_le_add hB hL).trans_eq ((Cardinal.add_eq_max hc).trans (max_self c))))

private theorem exists_named_minus_one
    (terms : OrderedFieldTerms L) (hK : InterpretsOrderedFieldTerms terms (A := K))
    (A : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ) :
    ∃ m : A.source.carrier .vf, m.val = -1 ∧ A.embedding.toEmbedding .vf m = -1 := by
  let minus : L.Term Empty := terms.sub.subst ![terms.zero, terms.one]
  have hm : minus.realize (Empty.elim : Empty → K) = -1 := by
    simp only [minus, Term.realize_subst, hK.sub, Matrix.cons_val_zero, Matrix.cons_val_one,
      hK.zero, hK.one, zero_sub]
  let B := vfReductOfSortedSubstructure O hO P A.source
  let m : B := minus.realize (Empty.elim : Empty → B)
  let f : B ↪[L] K := fieldEmbeddingOfSorted O O hO hO P P A.source A.embedding
  have hValue : m.val = -1 := by
    have h := HomClass.realize_term B.subtype (t := minus) (v := (Empty.elim : Empty → B))
    rw [Subsingleton.elim (B.subtype ∘ Empty.elim) (Empty.elim : Empty → K), hm] at h
    exact h.symm
  have hImage : f m = -1 := by
    have h := HomClass.realize_term f (t := minus) (v := (Empty.elim : Empty → B))
    rw [Subsingleton.elim (f ∘ Empty.elim) (Empty.elim : Empty → K), hm] at h
    exact h.symm
  exact ⟨m, hValue, hImage⟩

variable (terms : OrderedFieldTerms L) (hTerms : InterpretsOrderedFieldTerms terms (A := K))
  (convexTerms : FieldTerms (convexLanguage L))
  (hConvexTerms : letI := convexStructure O L; InterpretsFieldTerms (K := K) convexTerms)
  (T : (convexLanguage L).Theory) (hQE : EliminatesQuantifiers T)

include hTerms hConvexTerms hQE

set_option linter.style.haveILetI false in
/-- The two stages of a field-point lift of Lemma 2.20. Saturation is
only used over the old field together with a representative for each
leading term of the desired simple adjunction. -/
theorem exists_small_immediate_field_adjunction {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hμK : μ < #K)
    (hL : #(Σ i, L.Functions i) ≤ μ) :
    letI := convexStructure O L
    ∀ (_ : K ⊨ T)
      (_hSat : ∀ Names : Type u, #Names < #K →
        RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K Names)
      (_hRepresent : ∀ A : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ,
        (∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val) →
        ∀ t ∉ rv O '' A.source.carrier .vf,
          ∃ B : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ,
            A ≤ B ∧ t ∈ rv O '' B.source.carrier .vf)
      (A : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ),
      (∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val) →
      #(A.source.carrier .vf) < #K → ∀ a,
        ∃ B : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ,
          A ≤ B ∧ #(B.source.carrier .vf) ≤ max μ #(A.source.carrier .vf) ∧ a ∈ B.source.carrier .vf := by
  letI := convexStructure O L
  intro hT hSat hRepresent A hA hSmall a
  let B := Substructure.closure L (insert a (A.source.carrier .vf))
  let D := rv O '' (B : Set K)
  let c := max μ #(A.source.carrier .vf)
  have hc : ℵ₀ ≤ c := hμ.trans (le_max_left _ _)
  have hLess : c < #K := max_lt hμK hSmall
  have hLang : #(Σ i, L.Functions i) ≤ c := hL.trans (le_max_left _ _)
  have hStart : #(A.source.carrier .vf) ≤ c := le_max_right _ _
  have hB : #B ≤ c :=
    card_fieldClosure_le hc hLang _ (Cardinal.mk_insert_le.trans
      ((add_le_add hStart (one_le_aleph0.trans hc)).trans_eq (Cardinal.add_eq_max hc |>.trans (max_self c))))
  have hD : #D ≤ c := Cardinal.mk_image_le.trans hB
  obtain ⟨m, hm, him⟩ := exists_named_minus_one O hO P terms hTerms A
  obtain ⟨C, hAC, hCB, ha⟩ := exists_fixedRVExtension_via_representatives A a m hm him
    convexTerms hConvexTerms hConvexTerms hQE hT hT (by
      intro U q hU
      have hOld : #(A.source.carrier .vf ∪ Set.range q : Set K) ≤ c :=
        (Cardinal.mk_union_le _ _).trans
          ((add_le_add hStart (Cardinal.mk_range_le.trans hD)).trans_eq
            ((Cardinal.add_eq_max hc).trans (max_self c)))
      apply hSat
      change #(U.source.carrier .vf) < #K
      rw [hU]
      exact (card_fieldClosure_le hc hLang _ hOld).trans_lt hLess) (by
      intro U hAU t _ ht
      exact hRepresent U (fixesRV_of_extends hAU hA) t ht)
  exact ⟨C, hAC, hCB.symm ▸ hB, ha⟩

set_option linter.style.haveILetI false in
/-- Lemma 2.20, from the prescribed-RV extension step and saturation
over field domains of size below that of the ambient model. -/
theorem exists_immediate_automorphism_of_small_saturation {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hμK : μ < #K)
    (hL : #(Σ i, L.Functions i) ≤ μ) :
    letI := convexStructure O L
    ∀ (_ : K ⊨ T)
      (_hSat : ∀ Names : Type u, #Names < #K →
        RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K Names)
      (_hRepresent : ∀ A : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ,
        (∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val) →
        ∀ t ∉ rv O '' A.source.carrier .vf,
          ∃ B : FixedRVLift (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P) Set.univ,
            A ≤ B ∧ t ∈ rv O '' B.source.carrier .vf)
      (S : SortedSubstructure (canonicalStructure (L := L) O hO P)) (_ : #(S.carrier .vf) ≤ μ)
      (e : SortedEmbedding S.structureOn (canonicalStructure (L := L) O hO P)),
      (∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val) →
      ∃ f : SortedIsomorphism (canonicalStructure (L := L) O hO P) (canonicalStructure (L := L) O hO P),
        (∀ s (x : S.carrier s), f.toEmbedding s x.val = e.toEmbedding s x) ∧
          ∀ t : RV0 O, f.toEmbedding .rv t = t := by
  letI := convexStructure O L
  intro hT hSat hRepresent S hs e he
  let A := e.extendImmediateByIdentity S he
  have hA := e.extendImmediateByIdentity_fixesRV S he
  have hsA : #(A.source.carrier .vf) ≤ μ := by
    rw [e.extendImmediateByIdentity_carrier_vf S he]
    exact hs
  obtain ⟨f, hf, hfix⟩ := exists_immediate_automorphism_of_small_forth hμ hμK A hA hsA
    (exists_small_immediate_field_adjunction O hO P terms hTerms convexTerms hConvexTerms T hQE
      hμ hμK hL hT hSat hRepresent)
  refine ⟨f, fun s x => ?_, hfix⟩
  have hx : x.val ∈ A.source.carrier s := by
    cases s with
    | vf => exact (e.extendImmediateByIdentity_carrier_vf S he).symm ▸ x.property
    | rv => exact A.rv_eq.symm ▸ Set.mem_univ _
  exact (hf s ⟨x.val, hx⟩).trans (e.extendImmediateByIdentity_agrees S he s x hx)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  [L.Structure (Residue O)] hTerms hConvexTerms hQE in
set_option linter.style.haveILetI false in
/-- Lemma 2.20 with the representative step supplied by the
generated adjunction proof. -/
theorem CanonicalQEModel.exists_small_immediate_automorphism
    {K : Type u} [Field E] {T : L.Theory} [T.IsUniversal]
    {Tconvex : (convexLanguage L).Theory} {terms : OrderedFieldTerms L}
    {graph : E → L.Formula (Fin 2)} (d : CanonicalQEModel T Tconvex terms graph K)
    (hInput : d.hasAdjunctionInputs d)
    (hOM : IsOMinimalFieldTheory.{u, v, u} T) (hQE : EliminatesQuantifiers T)
    (hQEconvex : EliminatesQuantifiers Tconvex)
    (convexTerms : FieldTerms (convexLanguage L))
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμK : μ < #K)
    (hL : #(Σ i, L.Functions i) ≤ μ) :
    letI := d.field
    letI := d.languageStructure
    letI := convexStructure d.ring L
    InterpretsFieldTerms (K := K) convexTerms →
    (∀ Names : Type u, #Names < #K →
      RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K Names) →
    ∀ (S : SortedSubstructure d.structureOn), #(S.carrier .vf) ≤ μ →
      ∀ (e : SortedEmbedding S.structureOn d.structureOn),
        (∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val) →
        ∃ f : SortedIsomorphism d.structureOn d.structureOn,
          (∀ s (x : S.carrier s), f.toEmbedding s x.val = e.toEmbedding s x) ∧
          ∀ t : RV0 d.ring, f.toEmbedding .rv t = t := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  letI := convexStructure d.ring L
  intro hConvex hSat S hS e he
  refine exists_immediate_automorphism_of_small_saturation d.ring d.convex d.rvPowers.pow
    terms d.orderedTerms convexTerms hConvex Tconvex hQEconvex hμ hμK hL
    d.modelsValued hSat ?_ S hS e he
  intro A _ t hNew
  exact exists_fixedRVExtension_of_tconvex_inputs terms d.orderedTerms d.orderedTerms
    d.ring d.ring d.powers d.powers d.rvPowers d.rvPowers d.convex d.convex
    A hOM hQE (hInput A) t (Set.mem_univ _) hNew

end GeneralizedEuler.Section2
