module

public import Section5.UnaryCenterChains
public import Section5.DefinablePullbackLabels

/-! A definable mixed bijection has a single finite list of inverse
label tests over the original VF base, uniformly in every old RV tag. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I J : Type} [Finite I] [Finite J]
  {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
  (e : A ≃ B)

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- The graph is in mixed variables throughout, even though the
underlying equivalence is written as a map on pairs. -/
abbrev UnaryMixedGraphDefinable :=
  DefinableRelation 𝓜 S.carrier
    (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
      (b : SortedAssignment (CanonicalSort O) (MixedVariables 1 J)) =>
      ∃ ha : (a .vf 0,a .rv) ∈ A, (e ⟨(a .vf 0,a .rv),ha⟩).val = (b .vf 0,b .rv))

@[expose] def encodeUnaryLabel (x : K × (I → RV0 O)) : Fin 1 ⊕ I → RV0 O :=
  Sum.elim (fun _ => rv O x.1) x.2

omit [LinearOrder K] [IsStrictOrderedRing K] [Finite I] in
private theorem encodeUnaryLabel_injective_on_labels
    {a b : K × (I → RV0 O)} (he : encodeUnaryLabel O a = encodeUnaryLabel O b) :
    unaryMixedLabel O a = unaryMixedLabel O b :=
  Prod.ext (congrFun he (.inl 0)) (funext fun i => congrFun he (.inr i))

@[expose] def inverseUnaryTestDomain : Set (K × ((J ⊕ (Fin 1 ⊕ I)) → RV0 O)) :=
  {x | ∃ h : (x.1,x.2 ∘ Sum.inl) ∈ B,
      encodeUnaryLabel O (e.symm ⟨(x.1,x.2 ∘ Sum.inl),h⟩).val = x.2 ∘ Sum.inr}

omit [Finite J] in
theorem inverseUnaryTestDomain_definable (eDef : UnaryMixedGraphDefinable O hO power S e) :
    SortedDefinableOver 𝓜 S.carrier
      {x : SortedAssignment (CanonicalSort O) (MixedVariables 1 (J ⊕ (Fin 1 ⊕ I))) |
        (x .vf 0,x .rv) ∈ inverseUnaryTestDomain O e} := by
  have inv := eDef.transpose
  have labels := packPullbackLabel_definable hO power S (n := 1) (I := I)
  have mixed := inv.comp labels
  let r : ∀ s, SumVariables (MixedVariables 1 J) (RVVariables (Fin 1 ⊕ I)) s →
      MixedVariables 1 (J ⊕ (Fin 1 ⊕ I)) s
    | .vf => Sum.elim id PEmpty.elim
    | .rv => id
  unfold DefinableRelation at mixed
  convert mixed.pullback_relabel r using 1
  ext w
  let x := (w .vf 0,w .rv ∘ Sum.inl)
  let ξ := w .rv ∘ Sum.inr
  change (∃ hx : x ∈ B, encodeUnaryLabel O (e.symm ⟨x,hx⟩).val = ξ) ↔
    ∃ a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I),
      (∃ ha : (a .vf 0,a .rv) ∈ A, (e ⟨(a .vf 0,a .rv),ha⟩).val = x) ∧
      packPullbackLabel (mixedTuple a) = ξ
  have packed (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)) :
      packPullbackLabel (mixedTuple a) = encodeUnaryLabel O (a .vf 0,a .rv) := by
    funext i
    cases i with
    | inl j => rw [Subsingleton.elim j (0 : Fin 1)]; rfl
    | inr j => rfl
  constructor
  · rintro ⟨hx,h⟩
    let a := e.symm ⟨x,hx⟩
    let w' : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)
      | .vf => fun _ => a.val.1
      | .rv => a.val.2
    exact ⟨w',⟨a.property,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩,
      (packed w').trans h⟩
  · rintro ⟨a,⟨ha,he⟩,hh⟩
    let t : A := ⟨(a .vf 0,a .rv),ha⟩
    have hx : x ∈ B := he ▸ (e t).property
    have eq : e.symm ⟨x,hx⟩ = t := e.symm_apply_eq.2 (Subtype.ext he.symm)
    exact ⟨hx,(congrArg (fun p : A => encodeUnaryLabel O p.val) eq).trans ((packed a).symm.trans hh)⟩

omit [Finite J] in
theorem inverse_label_tests_at_finite_centers
    (eDef : UnaryMixedGraphDefinable O hO power S e)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (J ⊕ (Fin 1 ⊕ I)))
      (CenterTestAssignments S.carrier (J ⊕ (Fin 1 ⊕ I))))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t) :
    ∃ C : Finset (S.carrier .vf), ∀ x y : B, x.val.2 = y.val.2 →
      (∀ c ∈ C, rv O (x.val.1-c.val) = rv O (y.val.1-c.val)) →
      unaryMixedLabel O (e.symm x).val = unaryMixedLabel O (e.symm y).val := by
  obtain ⟨C,hC⟩ := finite_centers_of_definable O hO power S minusOne hm F hF sat immediate
    (inverseUnaryTestDomain O e) (inverseUnaryTestDomain_definable O hO power S e eDef)
  refine ⟨C,?_⟩
  intro x y tags tests
  let ξ := Sum.elim x.val.2 (encodeUnaryLabel O (e.symm x).val)
  have hx : (x.val.1,ξ) ∈ inverseUnaryTestDomain O e := ⟨x.property,rfl⟩
  obtain ⟨hy,eq⟩ := (hC x.val.1 y.val.1 ξ tests).1 hx
  have he : (⟨(y.val.1,ξ ∘ Sum.inl),hy⟩ : B) = y := Subtype.ext (Prod.ext rfl tags)
  rw [he] at eq
  exact encodeUnaryLabel_injective_on_labels O eq.symm

omit [Finite J] in
/-- The paired preparation on initially prepared pullbacks. The
definable inverse graph supplies the finite list of target centers. -/
theorem simultaneous_unary_preparation_on_pullbacks
    (graph : UnaryMixedGraphDefinable O hO power S e)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (chart : UnaryDiscCharts O e)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (J ⊕ (Fin 1 ⊕ I)))
      (CenterTestAssignments S.carrier (J ⊕ (Fin 1 ⊕ I))))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t) :
    ∃ (R T : Type z) (A' : Set (K × R)) (B' : Set (K × T)) (g : A ≃ A') (h : B ≃ B'),
      UnaryTranslationChain O A A' g ∧ UnaryTargetFocusChain O B B' h ∧
      IsUnaryPullback O A' ∧ IsUnaryPullback O B' ∧
      Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val)
        (g.symm.trans (e.trans h)) ∧
      Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val)
        (g.symm.trans (e.trans h)).symm := by
  classical
  obtain ⟨C,tests⟩ := inverse_label_tests_at_finite_centers O hO power S e graph
    minusOne hm F hF sat immediate
  let center (c : S.carrier .vf) : (J → RV0 O) → K := fun _ => c.val
  obtain ⟨T,B',h,chain,_,decides⟩ := unary_target_chain_prepares_centers O (C.toList.map center) fullB
  have inverse : Contractible (fun y : B => unaryMixedLabel O (h y).val)
      (unaryMixedLabel O ∘ Subtype.val) e.symm := by
    intro x y hh
    have old := unaryTargetFocusChain_refines O chain x y hh
    apply tests x y (congrArg (fun p : RV0 O × (J → RV0 O) => p.2) old)
    intro c hc
    exact decides x y hh (center c) (List.mem_map.2 ⟨c,Finset.mem_toList.2 hc,rfl⟩)
  obtain ⟨R,A',g,gChain,pA,pB,forw,back⟩ :=
    paired_unary_focus_chain O chain e fullA fullB chart forward inverse
  exact ⟨R,T,A',B',g,h,gChain,chain,pA,pB,forw,back⟩

end GeneralizedEuler.Section5
