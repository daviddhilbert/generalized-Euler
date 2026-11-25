module

public import Section2.DimensionFormulas
public import Section2.SmallImmediateAdjunction
public import Section2.ImmediateTranslateLift

/-! Field definable closure over a small field base and arbitrary RV
parameters, via immediate automorphisms. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language Cardinal

universe u v w

variable {L : Language.{u, v}} {K : Type u} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [L.Structure K] (O : ValuationSubring K)

omit [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] in
private theorem exists_small_perturbation {D : Set K} {a : K} (ha : a ∉ D)
    (hne : O.valuation.IsNontrivial) (C : Finset D) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ c ∈ C, O.valuation δ < O.valuation (a - c.val) := by
  classical
  obtain ⟨ε, hε, hεv⟩ := (Valuation.isNontrivial_iff_exists_lt_one O.valuation).mp hne
  induction C using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert c C _ ih =>
    obtain ⟨δ, hδ, hSmall⟩ := ih
    by_cases h : O.valuation δ < O.valuation (a - c.val)
    · exact ⟨δ, hδ, fun x hx => (Finset.mem_insert.mp hx).elim (fun he => he ▸ h) (hSmall x)⟩
    have hc : a - c.val ≠ 0 := sub_ne_zero.mpr (fun he => ha (he.symm ▸ c.property))
    have hNew : O.valuation (ε * (a - c.val)) < O.valuation (a - c.val) := by
      simpa only [map_mul, one_mul] using
        mul_lt_mul_of_pos_right hεv (pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr hc))
    refine ⟨ε * (a - c.val), mul_ne_zero hε hc, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hNew
    · exact (hNew.trans_le (le_of_not_gt h)).trans (hSmall x hx)

set_option linter.style.haveILetI false in
/-- Saturation realizes the type specifying all old translates of a
field point outside the base together with inequality to that point. -/
theorem exists_ne_of_matching_old_translates (F : FieldTerms (convexLanguage L))
    {D : Set K} {a : K} (ha : a ∉ D) (hne : O.valuation.IsNontrivial) :
    letI := convexStructure O L
    InterpretsFieldTerms (K := K) F →
    RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K (D ⊕ Unit) →
    ∃ b : K, b ≠ a ∧ ∀ c : D, rv O (a - c.val) = rv O (b - c.val) := by
  letI := convexStructure O L
  intro hF hSat
  classical
  let J := convexLanguage L
  let N := D ⊕ Unit
  let p : N → K := Sum.elim Subtype.val (fun _ => a)
  let old : J.Term (N ⊕ Unit) := .var (.inl (.inr ()))
  let fresh : J.Term (N ⊕ Unit) := .var (.inr ())
  let req : N → J.Formula (N ⊕ Unit)
    | .inl c => rvTranslateEqualFormula F old fresh (.var (.inl (.inl c)))
    | .inr _ => (fresh.equal old).not
  have hTrans (b : K) (c : D) :
      (req (.inl c)).Realize (Sum.elim p (fun _ => b)) ↔
        rv O (a - c.val) = rv O (b - c.val) := by
    simp only [req, realize_rvTranslateEqualFormula O hF, old, fresh, Term.realize_var, p,
      Sum.elim_inl, Sum.elim_inr]
  have hNe (b : K) :
      (req (.inr ())).Realize (Sum.elim p (fun _ => b)) ↔ b ≠ a := by
    simp only [req, Formula.realize_not, Formula.realize_equal, fresh, old, Term.realize_var,
      p, Sum.elim_inl, Sum.elim_inr]
  have hFin (U : Finset (J.Formula (N ⊕ Unit))) (hU : (U : Set _) ⊆ Set.range req) :
      ∃ b : K, ∀ ψ ∈ U, ψ.Realize (Sum.elim p (fun _ => b)) := by
    rw [← Set.image_univ] at hU
    obtain ⟨V, _, rfl⟩ := Finset.subset_set_image_iff.mp hU
    let pick : N → Option D
      | .inl c => some c
      | .inr _ => none
    have hPick : ∀ i j : N, ∀ c ∈ pick i, c ∈ pick j → i = j := by
      intro i j c hi hj
      cases i <;> cases j <;> simp_all [pick]
    obtain ⟨δ, hδ, hC⟩ := exists_small_perturbation O ha hne (V.filterMap pick hPick)
    refine ⟨a + δ, ?_⟩
    intro ψ hψ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hψ
    cases i with
    | inl c =>
      apply (hTrans _ c).mpr
      symm
      have hc : a - c.val ≠ 0 := sub_ne_zero.mpr (fun he => ha (he.symm ▸ c.property))
      apply (rv_eq_rv_iff_valuation O hc).mpr
      have hcalc : (a + δ - c.val) - (a - c.val) = δ := by abel
      rw [hcalc]
      exact hC c ((Finset.mem_filterMap pick).mpr ⟨.inl c, hi, rfl⟩)
    | inr i =>
      cases i
      exact (hNe _).mpr (fun h => hδ (add_left_cancel (h.trans (add_zero a).symm)))
  obtain ⟨b, hb⟩ := hSat p (Set.range req) hFin
  exact ⟨b, (hNe b).mp (hb _ (Set.mem_range_self (f := req) (Sum.inr ()))),
    fun c => (hTrans b c).mp (hb _ (Set.mem_range_self (f := req) (Sum.inl c)))⟩

set_option linter.style.haveILetI false in
/-- Any field point outside a small substructure can be moved by an
automorphism fixing that substructure on VF and fixing all of RV. -/
theorem CanonicalQEModel.exists_immediate_automorphism_moving_field
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
    InterpretsFieldTerms (K := K) F → d.ring.valuation.IsNontrivial →
    (∀ Names : Type u, #Names < #K →
      RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K Names) →
    (∀ (D : L.Substructure K) (a : K),
      (∃ y ∈ adjoinFieldRepresentative D a, rv d.ring y ∉ rv d.ring '' (D : Set K)) →
      ∃ c : D, rv d.ring (a - c.val) ∉ rv d.ring '' (D : Set K)) →
    ∀ (S : SortedSubstructure d.structureOn), #(S.carrier .vf) ≤ μ →
      ∀ a ∉ S.carrier .vf,
        ∃ f : SortedIsomorphism d.structureOn d.structureOn,
          f.toEmbedding .vf a ≠ a ∧
          (∀ x ∈ S.carrier .vf, f.toEmbedding .vf x = x) ∧
          ∀ t : RV0 d.ring, f.toEmbedding .rv t = t := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  letI := convexStructure d.ring L
  intro hF hVal hSat hDetect S hS a ha
  have hNames : #(S.carrier .vf ⊕ Unit) ≤ μ := by
    simp only [Cardinal.mk_sum, Cardinal.mk_unit, Cardinal.lift_uzero, Cardinal.lift_one]
    exact Cardinal.add_le_of_le hμ hS (one_le_aleph0.trans hμ)
  obtain ⟨b, hba, hSame⟩ := exists_ne_of_matching_old_translates d.ring F ha hVal hF
    (hSat (S.carrier .vf ⊕ Unit) (hNames.trans_lt hμK))
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
  refine ⟨f, hfa ▸ hba, ?_, hRV⟩
  intro x hx
  obtain ⟨hMem, hAgree⟩ := (FixedRVLift.le_iff_extends A C).mp hAC
  let xA : A.source.carrier .vf := ⟨x, hAVF.symm ▸ hx⟩
  exact (hf .vf ⟨x, hMem .vf xA.property⟩).trans ((hAgree .vf xA).symm.trans (hBase xA))

/-- A uniquely definable tuple over field parameters in a substructure
has all its field coordinates in that substructure when immediate
automorphisms can move every outside field point. RV parameters are
arbitrary. -/
theorem vf_range_subset_of_definable_singleton_of_immediate_movers
    {E : Type w} {X : TCsort → Type*} (M : SortedStructure L E X)
    (S : SortedSubstructure M)
    (hMove : ∀ a ∉ S.carrier .vf, ∃ f : SortedIsomorphism M M,
      f.toEmbedding .vf a ≠ a ∧
        (∀ x ∈ S.carrier .vf, f.toEmbedding .vf x = x) ∧
        ∀ t : X .rv, f.toEmbedding .rv t = t)
    {A : ∀ s, Set (X s)} (hA : A .vf ⊆ S.carrier .vf)
    {Var : TCsort → Type*} {p : ∀ s, Var s → X s}
    (hp : SortedDefinableOver M A {p}) : Set.range (p .vf) ⊆ S.carrier .vf := by
  rintro _ ⟨i, rfl⟩
  by_contra ha
  obtain ⟨f, hMove, hVF, hRV⟩ := hMove (p .vf i) ha
  obtain ⟨φ, hφ⟩ := hp
  let v (s : TCsort) : A s ⊕ Var s → X s := Sum.elim Subtype.val (p s)
  let p' := f.toSortedEmbedding.mapAssignment p
  have hMap : f.toSortedEmbedding.mapAssignment v = fun s => Sum.elim Subtype.val (p' s) := by
    funext s j
    cases j with
    | inr j => simp only [SortedEmbedding.mapAssignment_apply, v, p', Sum.elim_inr]
    | inl j =>
      simp only [SortedEmbedding.mapAssignment_apply, v, Sum.elim_inl]
      cases s with
      | vf => exact hVF _ (hA j.property)
      | rv => exact hRV _
  have hv : φ.realize M v := (hφ p).mp rfl
  have hv' := (f.realize_iff φ v).mpr hv
  rw [hMap] at hv'
  have he : p' = p := (hφ p').mpr hv'
  apply hMove
  simpa only [p', SortedEmbedding.mapAssignment_apply] using congrFun (congrFun he .vf) i

/-- A uniquely definable tuple over a small field base and any RV
parameters has all its field coordinates in the field-language
closure of the named field points. -/
theorem vf_range_subset_fieldClosure_of_small_immediate_movers
    {E : Type w} [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (P : E → RV0 O → RV0 O)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hL : #(Σ i, L.Functions i) ≤ μ) :
    let M := canonicalStructure (L := L) O hO P
    (∀ (S : SortedSubstructure M), #(S.carrier .vf) ≤ μ →
      ∀ a ∉ S.carrier .vf, ∃ f : SortedIsomorphism M M,
        f.toEmbedding .vf a ≠ a ∧
          (∀ x ∈ S.carrier .vf, f.toEmbedding .vf x = x) ∧
          ∀ t : RV0 O, f.toEmbedding .rv t = t) →
    ∀ (A : ∀ s, Set (CanonicalSort O s)), #(A .vf) ≤ μ →
      ∀ {Var : TCsort → Type*} {p : ∀ s, Var s → CanonicalSort O s},
        SortedDefinableOver M A {p} →
        Set.range (p .vf) ⊆ (Substructure.closure L (A .vf) : Set K) := by
  let M := canonicalStructure (L := L) O hO P
  change _ → _
  intro hMove A hA Var p hp
  let B := Substructure.closure L (A .vf)
  let full : SortedSubstructure M := ⟨fun _ => Set.univ, fun _ _ _ => Set.mem_univ _⟩
  let S := enlargeVF O hO P full B (fun _ _ => Set.mem_univ _)
  have hSize : #(S.carrier .vf) ≤ μ := card_fieldClosure_le hμ hL _ hA
  exact vf_range_subset_of_definable_singleton_of_immediate_movers M S (hMove S hSize)
    Substructure.subset_closure hp

section Dimension

variable {J : Language.{u, u}} {E : Type u} [J.Structure K] [J.Structure (Residue O)]
  [TopologicalSpace K] [OrderTopology K] (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

local notation "M₀" => (canonicalStructure (L := J) O hO P)

/-- Lemma 2.26 over a small field base. The immediate automorphisms
supply the field-closure step in the lower bound. -/
theorem isLeast_definableMixedEmbeddingArities_of_small_field_base
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hL : #(Σ i, J.Functions i) ≤ μ)
    (hMove : ∀ (S : SortedSubstructure M₀), #(S.carrier .vf) ≤ μ →
      ∀ a ∉ S.carrier .vf, ∃ f : SortedIsomorphism M₀ M₀,
        f.toEmbedding .vf a ≠ a ∧
          (∀ x ∈ S.carrier .vf, f.toEmbedding .vf x = x) ∧
          ∀ t : RV0 O, f.toEmbedding .rv t = t)
    {n : ℕ} {R : Type} [Finite R]
    (T : SortedTheory J E) (hM : ∀ ψ ∈ T, ψ.realize M₀)
    (le : J.Relations 2) (hLE : InterpretsVFOrder M₀ le)
    (A : ∀ s, Set (CanonicalSort O s)) (hA : #(A .vf) ≤ μ)
    (D : Set (MixedTuple (CanonicalSort O) n R)) (hne : D.Nonempty)
    (φ : SortedFormula J E (NamedChartVariables (fun s => (A s : Type u)) n R))
    (hD : ∀ x : (∀ s, MixedVariables n R s → CanonicalSort O s),
      mixedTuple x ∈ D ↔ φ.realize M₀ (fun s => Sum.elim Subtype.val (x s)))
    (hCharts : HasPointwiseProjectionCharts T le φ)
    (padding : A .vf) (tag : ℕ ↪ RV0 O) (hTag : ∀ i, tag i ∈ A .rv)
    (B : Matroid K)
    (hRank : ∀ (y : R → RV0 O), (sortedFiber D y).Nonempty →
      ∃ x ∈ sortedFiber D y, (B.eRk (Set.range x)).toNat = projectionDimension (sortedFiber D y))
    (hClosure : ∀ U : Set K, (Substructure.closure J (A .vf ∪ U) : Set K) = B.closure U) :
    IsLeast (definableMixedEmbeddingArities M₀ A D) (vfDimension D) := by
  have hN (s : TCsort) : Nonempty (CanonicalSort O s) := by
    cases s
    · exact ⟨(0 : K)⟩
    · exact ⟨(0 : RV0 O)⟩
  apply isLeast_definableMixedEmbeddingArities.{u, u, u, u} T M₀ hM hN le hLE
    A D hne φ hD hCharts padding tag hTag B hRank
  intro j S _ p q hp
  have hq : #(Set.range (q .vf)) ≤ μ := by
    have h : #(Set.range (q .vf)) ≤ (j : Cardinal.{u}) := by
      simpa only [Cardinal.lift_uzero, Cardinal.lift_mk_fin] using
        (Cardinal.mk_range_le_lift (f := q .vf))
    exact h.trans (Cardinal.natCast_le_aleph0.trans hμ)
  have hSmall : #(A .vf ∪ Set.range (q .vf) : Set K) ≤ μ :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hμ hA hq)
  rw [← hClosure]
  exact vf_range_subset_fieldClosure_of_small_immediate_movers O hO P hμ hL hMove
    (fun s => A s ∪ Set.range (q s)) hSmall hp

end Dimension

end GeneralizedEuler.Section2
