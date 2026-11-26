module

public import Section5.RelativeLiftChoices
public import Section5.BoundaryLiftGluing

/-! Definable gluing for the full-arity step of Lemma 5.12. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {U V : Set (labelAssignment n X)}

@[expose] def HasDefinableFieldLift (S : SortedSubstructure M) (e : U ≃ V) : Prop :=
  ∃ lift : fieldLiftDomain M U ≃ fieldLiftDomain M V,
    (∀ x, liftedLabel V (lift x) = e (liftedLabel U x)) ∧
    DefinableRelation M S.carrier
      (fun a b => ∃ ha : a ∈ fieldLiftDomain M U, (lift ⟨a,ha⟩).val = b)

@[expose] def rvPreimage (e : U ≃ V) (C : Set (labelAssignment n X)) : Set (labelAssignment n X) :=
  {a | ∃ ha : a ∈ U, (e ⟨a,ha⟩).val ∈ C}

private theorem rvPreimage_definable (e : U ≃ V) {C : Set (labelAssignment n X)}
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b))
    (hC : SortedDefinableOver M S.carrier C) :
    SortedDefinableOver M S.carrier (rvPreimage e C) := by
  have h := hE.transpose.image hC
  convert h using 1
  ext a
  change (∃ ha : a ∈ U, (e ⟨a,ha⟩).val ∈ C) ↔
    ∃ b ∈ C, ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b
  exact ⟨fun ⟨ha,hC⟩ => ⟨_,hC,ha,rfl⟩, fun ⟨_,hb,ha,he⟩ => ⟨ha,he.symm ▸ hb⟩⟩

/-- At full field arity both boundaries have smaller RV dimension.
The lower-dimensional lift is used on their union and the final graph is
definable by taking a union of the two graphs. -/
theorem definable_full_arity_lift_from_boundary
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (MixedVariables n Empty))
      (BaseAssignments S.carrier (MixedVariables n Empty)))
    (elem : ∀ x : fieldAssignment n X, let B := M.termGenerated (namedFieldAssignment S x)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))
    (e : U ≃ V) (hU : SortedDefinableOver M S.carrier U)
    (hV : SortedDefinableOver M S.carrier V)
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b))
    (surj : Function.Surjective M.rvMap)
    {D : Type*} [LinearOrder D] (dim : Set (labelAssignment n X) → D) (d : D)
    (dimMono : Monotone dim)
    (dimUnion : ∀ A B, dim (A ∪ B) ≤ max (dim A) (dim B))
    (dimPreimage : ∀ C, SortedDefinableOver M S.carrier C → dim (rvPreimage e C) ≤ dim C)
    (boundarySmall : ∀ A, SortedDefinableOver M S.carrier A → dim (rvBoundary (fieldLead M) A) < d)
    (lower : ∀ A : Set U, SortedDefinableOver M S.carrier (Subtype.val '' A) →
      dim (Subtype.val '' A) < d →
      ∃ f : ((liftedLabel (M := M) U) ⁻¹' A) ≃ ((liftedLabel (M := M) V) ⁻¹' (e '' A)),
        (∀ x, liftedLabel V (f x).val = e (liftedLabel U x.val)) ∧
        DefinableRelation M S.carrier (fun a b =>
          ∃ ha : a ∈ fieldLiftDomain M U, ∃ hA : liftedLabel U ⟨a,ha⟩ ∈ A,
            (f ⟨⟨a,ha⟩,hA⟩).val.val = b)) :
    HasDefinableFieldLift S e := by
  classical
  obtain ⟨h,g,hLabel,hInv,hGraph,hRange,gRange⟩ := relative_lift_choices sat elem e hU hV hE surj
  let p := liftedLabel (M := M) U
  let q := liftedLabel (M := M) V
  let A := boundaryGood p q e h g
  let B := rvBoundary (fieldLead M) (Subtype.val '' Set.range h)
  let C := rvBoundary (fieldLead M) (Subtype.val '' Set.range g)
  have hB : rvBoundary q (Set.range h) = Subtype.val ⁻¹' B :=
    rvBoundary_on_pullback (fieldLead M) V _
  have hC : rvBoundary p (Set.range g) = Subtype.val ⁻¹' C :=
    rvBoundary_on_pullback (fieldLead M) U _
  have hBad : Subtype.val '' Aᶜ = rvPreimage e B ∪ (U ∩ C) := by
    have hParts := congrArg₂ (fun B' C' => e ⁻¹' B' ∪ C') hB hC
    rw [(boundaryBad_eq p q e h g).trans hParts]
    ext a
    change (∃ u : U, ((e u).val ∈ B ∨ u.val ∈ C) ∧ u.val = a) ↔
      (∃ ha : a ∈ U, (e ⟨a,ha⟩).val ∈ B) ∨ (a ∈ U ∧ a ∈ C)
    constructor
    · rintro ⟨⟨u,hu⟩,hb | hc,rfl⟩
      · exact Or.inl ⟨hu,hb⟩
      · exact Or.inr ⟨hu,hc⟩
    · rintro (⟨ha,hb⟩ | ⟨ha,hc⟩)
      · exact ⟨⟨a,ha⟩,Or.inl hb,rfl⟩
      · exact ⟨⟨a,ha⟩,Or.inr hc,rfl⟩
  have bDef := definable_fieldLead_boundary hRange
  have cDef := definable_fieldLead_boundary gRange
  have badDef : SortedDefinableOver M S.carrier (Subtype.val '' Aᶜ) := by
    rw [hBad]
    exact (rvPreimage_definable e hE bDef).union (hU.inter cDef)
  have badDim : dim (Subtype.val '' Aᶜ) < d := by
    rw [hBad]
    apply (dimUnion _ _).trans_lt
    exact max_lt ((dimPreimage B bDef).trans_lt (boundarySmall _ hRange))
      ((dimMono Set.inter_subset_right).trans_lt (boundarySmall _ gRange))
  obtain ⟨f,hF,fDef⟩ := lower Aᶜ badDef badDim
  let changeTarget : (q ⁻¹' (e '' Aᶜ) : Set (fieldLiftDomain M V)) ≃
      ((q ⁻¹' (e '' A))ᶜ : Set (fieldLiftDomain M V)) :=
    let eq := image_label_compl e A
    { toFun := fun x => ⟨x.val,by
        change q x.val ∈ (e '' A)ᶜ
        rw [← eq]
        exact x.property⟩
      invFun := fun y => ⟨y.val,by
        change q y.val ∈ e '' Aᶜ
        rw [eq]
        exact y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f' := f.trans changeTarget
  have agree (x : (p ⁻¹' Aᶜ : Set (fieldLiftDomain M U))) : (f' x).val = (f x).val := rfl
  have hBij : Set.BijOn h (p ⁻¹' A) (q ⁻¹' (e '' A)) :=
    bijOn_lift_off_boundaries p q e h hLabel g hInv
  obtain ⟨lift,good,bad⟩ := equivalence_of_bijOn_and_complement h hBij f'
  have agreesBad (x : (p ⁻¹' Aᶜ : Set (fieldLiftDomain M U))) :
      lift x.val = (f x).val := (bad x).trans (agree x)
  refine ⟨lift,?_,?_⟩
  · intro x
    by_cases hx : p x ∈ A
    · rw [good x hx]
      exact hLabel x
    · exact (congrArg q (agreesBad ⟨x,hx⟩)).trans (hF ⟨x,hx⟩)
  · have goodDef : SortedDefinableOver M S.carrier (fieldLead M ⁻¹' (Subtype.val '' Aᶜ)ᶜ) :=
      definable_fieldLead_preimage badDef.compl
    have goodGraph := hGraph.inter_left goodDef
    exact (goodGraph.union fDef).congr (by
      intro a b
      constructor
      · rintro (⟨⟨ha,he⟩,ha'⟩ | ⟨ha,hA,he⟩)
        · refine ⟨ha,?_⟩
          rw [good ⟨a,ha⟩ (by
            by_contra hn
            exact ha' ⟨p ⟨a,ha⟩,hn,rfl⟩)]
          exact he
        · exact ⟨ha,(congrArg Subtype.val (agreesBad ⟨⟨a,ha⟩,hA⟩)).trans he⟩
      · rintro ⟨ha,he⟩
        by_cases hA : p ⟨a,ha⟩ ∈ A
        · refine Or.inl ⟨⟨ha,?_⟩,?_⟩
          · rwa [← good ⟨a,ha⟩ hA]
          · rintro ⟨r,hr,hr'⟩
            have hEq : r = p ⟨a,ha⟩ := Subtype.ext hr'
            exact hr (hEq.symm ▸ hA)
        · refine Or.inr ⟨ha,hA,?_⟩
          exact (congrArg Subtype.val (agreesBad ⟨⟨a,ha⟩,hA⟩)).symm.trans he)

end GeneralizedEuler.Section5
