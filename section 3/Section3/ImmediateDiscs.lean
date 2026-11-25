module

public import Section2.FieldClosureUnderRV
public import Section3.DiscEnds

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Cardinal

universe u v w
variable {L : Language.{u,v}}

set_option linter.style.haveILetI false in
/-- The prescribed-point version of the Section 2 back-and-forth. This is
the unary step in 3.15 and supplies the invariance input of 3.20. -/
theorem immediate_automorphism_of_matching_translates
    {E : Type w} [Field E] {T : L.Theory} [T.IsUniversal]
    {Tconvex : (convexLanguage L).Theory} {terms : OrderedFieldTerms L}
    {graph : E → L.Formula (Fin 2)} {K : Type u}
    (d : CanonicalQEModel T Tconvex terms graph K)
    (hInput : d.hasAdjunctionInputs d)
    (hOM : IsOMinimalFieldTheory.{u, v, u} T) (hQE : EliminatesQuantifiers T)
    (hQEv : EliminatesQuantifiers Tconvex)
    (F : FieldTerms (convexLanguage L))
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμK : μ < #K)
    (hL : #(Σ i, L.Functions i) ≤ μ) :
    letI := d.field
    letI := d.order
    letI := d.orderedRing
    letI := d.languageStructure
    letI := convexStructure d.ring L
    InterpretsFieldTerms (K := K) F →
    (∀ Names : Type u, #Names < #K →
      RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K Names) →
    (∀ (D : L.Substructure K) (a : K),
      (∃ y ∈ adjoinFieldRepresentative D a, rv d.ring y ∉ rv d.ring '' (D : Set K)) →
      ∃ c : D, rv d.ring (a - c.val) ∉ rv d.ring '' (D : Set K)) →
    ∀ (S : SortedSubstructure d.structureOn), #(S.carrier .vf) ≤ μ →
      ∀ a b : K, (∀ c : S.carrier .vf, rv d.ring (a - c.val) = rv d.ring (b - c.val)) →
        ∃ f : SortedIsomorphism d.structureOn d.structureOn,
          f.toEmbedding .vf a = b ∧
          (∀ x ∈ S.carrier .vf, f.toEmbedding .vf x = x) ∧
          ∀ t : RV0 d.ring, f.toEmbedding .rv t = t := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  letI := convexStructure d.ring L
  intro hF hSat hDetect S hS a b hSame
  have hNames : #(S.carrier .vf ⊕ Unit) ≤ μ := by
    simp only [Cardinal.mk_sum, Cardinal.mk_unit, Cardinal.lift_uzero, Cardinal.lift_one]
    exact Cardinal.add_le_of_le hμ hS (one_le_aleph0.trans hμ)
  let hIdentity (t : S.carrier .rv) : S.inclusion.toEmbedding .rv t = t.val :=
    SortedSubstructure.inclusion_apply S .rv t
  let A := S.inclusion.extendImmediateByIdentity S hIdentity
  have hAVF : A.source.carrier .vf = S.carrier .vf :=
    S.inclusion.extendImmediateByIdentity_carrier_vf S hIdentity
  have hFix : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val :=
    S.inclusion.extendImmediateByIdentity_fixesRV S hIdentity
  have hBase (x : A.source.carrier .vf) : A.embedding.toEmbedding .vf x = x.val := by
    let y : S.carrier .vf := ⟨x.val, hAVF ▸ x.property⟩
    exact (S.inclusion.extendImmediateByIdentity_agrees S hIdentity .vf y x.property).trans
      (SortedSubstructure.inclusion_apply S .vf y)
  have hTranslate (x : A.source.carrier .vf) :
      rv d.ring (a - x.val) = rv d.ring (b - A.embedding.toEmbedding .vf x) := by
    rw [hBase]
    exact hSame ⟨x.val, hAVF ▸ x.property⟩
  have hStep (x y : K) (hx : 0 < x) (hxy : rv d.ring x = rv d.ring y)
      (hNew : rv d.ring x ∉ rv d.ring '' A.source.carrier .vf) :
      ∃ C : FixedRVLift d.structureOn d.structureOn Set.univ,
        A ≤ C ∧ C.source.carrier .vf =
          (adjoinFieldRepresentative (vfReductOfSortedSubstructure d.ring d.convex d.rvPowers.pow A.source) x : Set K) ∧
        ∃ hx : x ∈ C.source.carrier .vf, C.embedding.toEmbedding .vf ⟨x, hx⟩ = y := by
    let s : A.source.carrier .rv := ⟨rv d.ring x, A.rv_eq.symm ▸ Set.mem_univ _⟩
    have hr : rv d.ring y = A.embedding.toEmbedding .rv s := hxy.symm.trans (hFix s).symm
    exact exists_fixedRVExtension_of_generated_adjunction terms d.orderedTerms d.orderedTerms
      d.ring d.ring d.powers d.powers d.rvPowers d.rvPowers d.convex d.convex A
      hOM hQE s hNew ⟨x, hx⟩ y rfl hr (hInput A ⟨x, hx⟩ y s hNew rfl hr)
  obtain ⟨C, hAC, hC, haC, hMap⟩ := exists_fixedRVExtension_of_matched_translates terms
    d.orderedTerms d.ring d.convex d.rvPowers.pow A hFix hOM hQE a b hTranslate hDetect hStep
  have hSmall : #(C.source.carrier .vf) ≤ μ := by
    rw [hC]
    let B := vfReductOfSortedSubstructure d.ring d.convex d.rvPowers.pow A.source
    change #(Substructure.closure L (Set.range (Sum.elim (Subtype.val : B → K)
      (fun _ : Unit => a)))) ≤ μ
    apply card_fieldClosure_le hμ hL _ (Cardinal.mk_range_le.trans ?_)
    change #(A.source.carrier .vf ⊕ Unit) ≤ μ
    rw [hAVF]
    exact hNames
  obtain ⟨f, hf, hRV⟩ := d.exists_small_immediate_automorphism hInput hOM hQE hQEv F
    hμ hμK hL hF hSat C.source hSmall C.embedding (fixesRV_of_extends hAC hFix)
  have hfa : f.toEmbedding .vf a = b := (hf .vf ⟨a, haC⟩).trans hMap
  refine ⟨f, hfa, ?_, hRV⟩
  intro x hx
  obtain ⟨hMem, hAgree⟩ := (FixedRVLift.le_iff_extends A C).mp hAC
  let xA : A.source.carrier .vf := ⟨x, hAVF.symm ▸ hx⟩
  exact (hf .vf ⟨x, hMem .vf xA.property⟩).trans ((hAgree .vf xA).symm.trans (hBase xA))

/-- All points of a disc realize the same translated leading term about
each point outside the disc. -/
theorem rv_translate_constant_off_disc {K : Type*} [Field K] (O : ValuationSubring K)
    {a x y c : K} {r : O.ValueGroup} (hx : x ∈ openDisc O a r)
    (hy : y ∈ openDisc O a r) (hc : c ∉ openDisc O a r) :
    rv O (x - c) = rv O (y - c) := by
  rw [← openDisc_change_center O hy] at hx hc
  have hne : y - c ≠ 0 := sub_ne_zero.mpr (fun h => hc
    (h ▸ mem_openDisc_center O (zero_le.trans_lt (show O.valuation (x - y) < r from hx)).ne' y))
  apply (rv_eq_rv_iff_valuation O hne).mpr
  rw [sub_sub_sub_cancel_right]
  have hfar : r ≤ O.valuation (c - y) := le_of_not_gt hc
  rw [← neg_sub, O.valuation.map_neg] at hfar
  exact lt_of_lt_of_le hx hfar

end GeneralizedEuler.Section3
