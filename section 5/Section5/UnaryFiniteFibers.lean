module

public import Section5.ReindexedUnarySteps

/-! A unary pullback has finite RV fibers exactly when its labels
have finite fibers over the active term. Finite focus images preserve
the field-fiber condition, including after the old label is appended. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) {T : Type*}

abbrev UnaryFiniteFibers (A : Set (K × T)) : Prop := ∀ x, {t | (x,t) ∈ A}.Finite

theorem unaryLeadFibers_finite {A : Set (K × T)} (full : IsUnaryPullback O A)
    (finite : UnaryFiniteFibers A) (lead : RV0 O) :
    {t | ∃ x : K, (x,t) ∈ A ∧ rv O x = lead}.Finite := by
  obtain ⟨x,hx⟩ := rv_surjective O lead
  apply (finite x).subset
  rintro t ⟨y,hy,hlead⟩
  exact full (y,t) hy (x,t) (Prod.ext (hlead.trans hx.symm) rfl)

theorem recodeUnaryTranslation_finiteFibers (T₁ : RelativeTranslation O (id : T → T))
    (A : Set (K × T)) (finite : UnaryFiniteFibers A)
    (offsets : (Set.range (fun p : T × RV0 O => T₁.offset p.1 p.2)).Finite) :
    UnaryFiniteFibers (recodeUnaryTranslation O T₁ '' A) := by
  intro y
  let C := (fun d : K => y+d) '' Set.range (fun p : T × RV0 O => T₁.offset p.1 p.2)
  let labels (z : K) := (fun t : T => (t,rv O z)) '' {t : T | (z,t) ∈ A}
  have fin : (⋃ z ∈ C, labels z).Finite := (offsets.image _).biUnion (fun z _ => (finite z).image _)
  apply fin.subset
  rintro t ⟨x,hx,eq⟩
  have field : x.1 - T₁.offset x.2 (rv O x.1) = y := congrArg (fun z : K × (T × RV0 O) => z.1) eq
  have tag : (x.2,rv O x.1) = t := congrArg (fun z : K × (T × RV0 O) => z.2) eq
  have mem : x.1 ∈ C := ⟨_,⟨(x.2,rv O x.1),rfl⟩,(eq_add_of_sub_eq field).symm⟩
  exact Set.mem_iUnion₂.2 ⟨x.1,mem,x.2,hx,tag⟩

omit O [Field K] in
theorem reindexUnaryImage_finiteFibers {T' : Type*} (p : T ≃ T') (A : Set (K × T))
    (finite : UnaryFiniteFibers A) : UnaryFiniteFibers (reindexUnaryPoint p '' A) := by
  intro y
  apply ((finite y).image p).subset
  rintro t ⟨x,hx,he⟩
  have field : x.1 = y := congrArg Prod.fst he
  have tag : p x.2 = t := congrArg (fun z : K × T' => z.2) he
  exact ⟨x.2,show (y,x.2) ∈ A from field ▸ hx,tag⟩

theorem encodedUnaryImage_finiteFibers {I : Type} (A : Set (K × (I → RV0 O)))
    (T₁ : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (finite : UnaryFiniteFibers A)
    (offsets : (Set.range (fun p : (I → RV0 O) × RV0 O => T₁.offset p.1 p.2)).Finite) :
    UnaryFiniteFibers (encodedUnaryImage O A T₁) :=
  reindexUnaryImage_finiteFibers (unaryTagAppend O) _ (recodeUnaryTranslation_finiteFibers O T₁ A finite offsets)

end GeneralizedEuler.Section5
