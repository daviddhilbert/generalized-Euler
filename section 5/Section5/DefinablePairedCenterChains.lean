module

public import Section5.ReindexedUnarySteps
public import Section5.DefinableCenterFocus
public import Section5.ShiftedCenterGraphs
public import Section5.DefinableUnaryOffsetFiniteness
import all Section5.UnaryCenterChains

/-! The finite target-center construction and its paired source steps
have definable graphs over the base of the original bijection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K)

inductive EncodedFocusChain (cert : ∀ I : Type, RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)) → Prop) :
    {I J : Type} →
    (A : Set (K × (I → RV0 O))) → (B : Set (K × (J → RV0 O))) → (A ≃ B) → Prop
  | nil {I : Type} (A : Set (K × (I → RV0 O))) : EncodedFocusChain cert A A (Equiv.refl A)
  | cons {I J : Type} (A : Set (K × (I → RV0 O)))
      (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
      (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t)
      (certificate : cert I T)
      {B : Set (K × (J → RV0 O))} (tail : encodedUnaryImage O A T ≃ B)
      (next : EncodedFocusChain cert (encodedUnaryImage O A T) B tail) :
      EncodedFocusChain cert A B ((encodedUnaryStep O A T).trans tail)

abbrev CenterTest (J : Type) := (J → RV0 O) → K

@[expose] def shiftCenterTest {J : Type}
    (T : RelativeTranslation O (id : (J → RV0 O) → (J → RV0 O)))
    (c : CenterTest O J) : CenterTest O (J ⊕ Unit) :=
  fun t => c (t ∘ Sum.inl) - T.offset (t ∘ Sum.inl) (t (.inr ()))

@[expose] def centerTestValue {J : Type} (c : CenterTest O J) (x : K × (J → RV0 O)) : RV0 O :=
  rv O (x.1-c x.2)

private theorem shifted_test_value {J : Type} {A : Set (K × (J → RV0 O))}
    (T : RelativeTranslation O (id : (J → RV0 O) → (J → RV0 O)))
    (c : CenterTest O J) (x : A) :
    centerTestValue O (shiftCenterTest O T c) (encodedUnaryStep O A T x).val = centerTestValue O c x.val := by
  change rv O ((x.val.1-T.offset x.val.2 (rv O x.val.1))-
    (c x.val.2 - T.offset x.val.2 (rv O x.val.1))) = rv O (x.val.1-c x.val.2)
  rw [sub_sub_sub_cancel_right]

theorem original_label_of_encoded_label {J : Type} {A : Set (K × (J → RV0 O))}
    (T : RelativeTranslation O (id : (J → RV0 O) → (J → RV0 O))) {x y : A}
    (h : unaryMixedLabel O (encodedUnaryStep O A T x).val = unaryMixedLabel O (encodedUnaryStep O A T y).val) :
    unaryMixedLabel O x.val = unaryMixedLabel O y.val := by
  have raw := (reindexUnaryPoint_label_eq O (unaryTagAppend O)
    (recodeUnaryTranslation O T x.val) (recodeUnaryTranslation O T y.val)).1 h
  exact congrArg (fun l : RV0 O × ((J → RV0 O) × RV0 O) => (l.2.2,l.2.1)) raw

theorem EncodedFocusChain.refines_labels {I J : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} {e : A ≃ B}
    {cert : ∀ I : Type, RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)) → Prop}
    (chain : EncodedFocusChain O cert A B e) :
    ∀ x y : A, unaryMixedLabel O (e x).val = unaryMixedLabel O (e y).val →
      unaryMixedLabel O x.val = unaryMixedLabel O y.val := by
  induction chain with
  | nil A => exact fun _ _ h => h
  | cons A T valid defT tail next ih =>
    intro x y same
    exact original_label_of_encoded_label O T (ih (encodedUnaryStep O A T x) (encodedUnaryStep O A T y) same)

private theorem encoded_step_inverse_tests {I J : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
    (e : A ≃ B) (full : IsUnaryPullback O B) (chart : UnaryDiscCharts O e)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e)
    (c : CenterTest O J) (a : B) (rest : List (CenterTest O J))
    (back : ∀ x y : B, unaryMixedLabel O x.val = unaryMixedLabel O y.val →
      (∀ d ∈ c :: rest, centerTestValue O d x.val = centerTestValue O d y.val) →
      unaryMixedLabel O (e.symm x).val = unaryMixedLabel O (e.symm y).val) :
    let C := centerLocus (A := B) O c
    let f := centerFocus O c a
    let T := pairedTargetTranslation O C f
    let g := encodedPairedConjugate O e C f
    ∀ x y : encodedUnaryImage O B T, unaryMixedLabel O x.val = unaryMixedLabel O y.val →
      (∀ d ∈ rest.map (shiftCenterTest O T), centerTestValue O d x.val = centerTestValue O d y.val) →
      unaryMixedLabel O (g.symm x).val = unaryMixedLabel O (g.symm y).val := by
  intro C f T g
  let Q := reindexUnaryImage (unaryTagAppend O) (recodeUnaryTranslation O T '' B)
  let P := reindexUnaryImage (unaryTagAppend O) (recodeUnaryTranslation O (pairedSourceTranslation O e C f) '' A)
  let raw := pairedUnaryConjugate O e C f
  let final (x : recodeUnaryTranslation O T '' B) :=
    (unaryMixedLabel O (Q x).val,fun d : {d // d ∈ rest} => centerTestValue O (shiftCenterTest O T d.val) (Q x).val)
  have refines (x y : recodeUnaryTranslation O T '' B) (h : final x = final y) :
      unaryMixedLabel O x.val = unaryMixedLabel O y.val :=
    (reindexUnaryPoint_label_eq O (unaryTagAppend O) x.val y.val).1 (congrArg Prod.fst h)
  have old : Contractible (final ∘ unaryImageIso O B T) (unaryMixedLabel O ∘ Subtype.val) e.symm := by
    intro x y h
    have labels : unaryMixedLabel O (encodedUnaryStep O B T x).val =
        unaryMixedLabel O (encodedUnaryStep O B T y).val := congrArg Prod.fst h
    apply back x y (original_label_of_encoded_label O T labels)
    intro d hd
    rcases List.mem_cons.1 hd with eq | hd
    · rw [eq]
      exact center_step_decides O c a full x y (refines _ _ h)
    · have test := congrFun (congrArg Prod.snd h) (⟨d,hd⟩ : {d // d ∈ rest})
      change centerTestValue O (shiftCenterTest O T d) (encodedUnaryStep O B T x).val =
        centerTestValue O (shiftCenterTest O T d) (encodedUnaryStep O B T y).val at test
      simpa only [shifted_test_value] using test
  have rawBack := paired_unary_step_inverse_contracts O e C f forward chart
    (fun _ h => centerFocus_valid O c a h) final old refines
  have backEq (x : recodeUnaryTranslation O T '' B) : g.symm (Q x) = P (raw.symm x) :=
    reindexUnaryEquiv_symm_apply (unaryTagAppend O) (unaryTagAppend O) raw x
  intro x y same tests
  obtain ⟨x,rfl⟩ := Q.surjective x
  obtain ⟨y,rfl⟩ := Q.surjective y
  rw [backEq,backEq]
  apply (reindexUnaryPoint_label_eq O (unaryTagAppend O) (raw.symm x).val (raw.symm y).val).2
  apply rawBack x y
  exact Prod.ext same (funext fun d => tests _ (List.mem_map.2 ⟨d.val,d.property,rfl⟩))

section DefinableChains

variable [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (F : FieldTerms (convexLanguage L))
  (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

local notation "𝓜" => canonicalStructure (L := L) O hO power

abbrev CenterTestDefinable {J : Type} (c : CenterTest O J) :=
  DefinableRelation 𝓜 S.carrier (fun
    (t : SortedAssignment (CanonicalSort O) (RVVariables J))
    (v : fieldAssignment 1 (CanonicalSort O)) => v .vf 0 = c (t .rv))

abbrev UnaryPullbackDefinable {I : Type} (A : Set (K × (I → RV0 O))) :=
  SortedDefinableOver 𝓜 S.carrier
    {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I) | unaryPair O a ∈ A}

abbrev DefinablePairedUnaryPreparation {I J : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} (e : A ≃ B)
    (tests : List (CenterTest O J) := []) :=
  ∃ (I' J' : Type) (_ : Finite I') (_ : Finite J')
    (A' : Set (K × (I' → RV0 O))) (B' : Set (K × (J' → RV0 O))) (s : A ≃ A') (t : B ≃ B'),
    EncodedFocusChain O (fun _ T => UnaryOffsetDefinable O hO power S T) A A' s ∧
    EncodedFocusChain O (fun _ T => UnaryOffsetDefinable O hO power S T) B B' t ∧
    UnaryMixedGraphDefinable O hO power S s ∧ UnaryMixedGraphDefinable O hO power S t ∧
    IsUnaryPullback O A' ∧ IsUnaryPullback O B' ∧
    Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) (s.symm.trans (e.trans t)) ∧
    Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) (s.symm.trans (e.trans t)).symm ∧
    ∀ x y : B, unaryMixedLabel O (t x).val = unaryMixedLabel O (t y).val →
      ∀ c ∈ tests, centerTestValue O c x.val = centerTestValue O c y.val

theorem DefinablePairedUnaryPreparation.without_tests {I J : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} {e : A ≃ B}
    (tests : List (CenterTest O J)) (h : DefinablePairedUnaryPreparation O hO power S e tests) :
    DefinablePairedUnaryPreparation O hO power S e := by
  obtain ⟨I',J',hi,hj,A',B',s,t,hs,ht,gs,gt,fa,fb,f,g,_⟩ := h
  exact ⟨I',J',hi,hj,A',B',s,t,hs,ht,gs,gt,fa,fb,f,g,fun _ _ _ _ h => (List.not_mem_nil h).elim⟩

include hm hF in
theorem definable_paired_center_chains {I J : Type} [Finite I] [Finite J]
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} (e : A ≃ B)
    (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
    (defE : UnaryMixedGraphDefinable O hO power S e)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (chart : UnaryDiscCharts O e)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e)
    (centers : List (CenterTest O J)) (defC : ∀ c ∈ centers, CenterTestDefinable O hO power S c)
    (back : ∀ x y : B, unaryMixedLabel O x.val = unaryMixedLabel O y.val →
      (∀ d ∈ centers, centerTestValue O d x.val = centerTestValue O d y.val) →
      unaryMixedLabel O (e.symm x).val = unaryMixedLabel O (e.symm y).val) :
    DefinablePairedUnaryPreparation O hO power S e centers := by
  classical
  generalize len : centers.length = n
  induction n generalizing I J A B centers with
  | zero =>
    have nil := List.length_eq_zero_iff.mp len
    subst centers
    exact ⟨I,J,inferInstance,inferInstance,A,B,Equiv.refl A,Equiv.refl B,.nil A,.nil B,
      unaryMixedGraph_refl O hO power S A defA,unaryMixedGraph_refl O hO power S B defB,
      fullA,fullB,forward,(fun x y he => back x y he (fun _ h => (List.not_mem_nil h).elim)),
      fun _ _ _ _ h => (List.not_mem_nil h).elim⟩
  | succ n ih =>
    cases centers with
    | nil => simp at len
    | cons c cs =>
      by_cases ne : B.Nonempty
      · let a : B := ⟨ne.choose,ne.choose_spec⟩
        let C := centerLocus (A := B) O c
        let f := centerFocus O c a
        let U := pairedSourceTranslation O e C f
        let V := pairedTargetTranslation O C f
        let s₀ := encodedUnaryStep O A U
        let t₀ := encodedUnaryStep O B V
        let g := encodedPairedConjugate O e C f
        have val (l) (hl : l ∈ C) := centerFocus_valid O c a hl
        have hg := centerFocus_graph_definable O hO power S c a defB
          ((defC c (List.mem_cons_self)).congr fun _ _ => eq_comm)
        have sd := pairedSourceOffset_definable O hO power S e C f defE hg fullA forward
        have td := pairedTargetOffset_definable O hO power S C f hg
        have gs := encodedUnaryStep_definable O hO power S F minusOne hm hF A U defA sd
        have gt := encodedUnaryStep_definable O hO power S F minusOne hm hF B V defB td
        have gg := encodedPairedConjugate_definable O hO power S F minusOne hm hF e C f defE hg fullA forward
        obtain ⟨fa,fb⟩ := paired_unary_step_preserves_pullbacks O e C f fullA fullB val
        have pba := reindexUnaryImage_is_pullback O (unaryTagAppend O) _ fa
        have pbb := reindexUnaryImage_is_pullback O (unaryTagAppend O) _ fb
        have ch := reindexUnaryEquiv_charts O (unaryTagAppend O) (unaryTagAppend O) _
          (paired_unary_step_preserves_charts O e C f fullA forward chart)
        have fw := reindexUnaryEquiv_contractible O (unaryTagAppend O) (unaryTagAppend O) _
          (paired_unary_step_contracts O e C f forward chart val)
        have bk := encoded_step_inverse_tests O e fullB chart forward c a cs back
        have shifted (b) (hb : b ∈ cs.map (shiftCenterTest O V)) : CenterTestDefinable O hO power S b := by
          obtain ⟨d,hd,rfl⟩ := List.mem_map.1 hb
          exact shiftedCenter_definable O hO power S C f F minusOne hm hF hg d
            (defC d (List.mem_cons_of_mem c hd))
        have hlen : (cs.map (shiftCenterTest O V)).length = n := by simpa using len
        obtain ⟨I',J',fI,fJ,A',B',s,t,hs,ht,ds,dt,hA,hB,hfor,hback,test⟩ := ih g
          (unary_mixed_image_definable O hO power S s₀ gs)
          (unary_mixed_image_definable O hO power S t₀ gt) gg pba pbb ch fw _ shifted bk hlen
        have eq : (s₀.trans s).symm.trans (e.trans (t₀.trans t)) = s.symm.trans (g.trans t) := by
          apply Equiv.ext
          intro x
          change t (t₀ (e (s₀.symm (s.symm x)))) = t (g (s.symm x))
          have eval := encodedPairedConjugate_apply O e C f (s₀.symm (s.symm x))
          change g (s₀ (s₀.symm (s.symm x))) = _ at eval
          rw [Equiv.apply_symm_apply] at eval
          exact congrArg t eval.symm
        refine ⟨I',J',fI,fJ,A',B',s₀.trans s,t₀.trans t,
          .cons A U (fun _ _ h => pairedSourceTranslation_focus_lead O e C f h) sd s hs,
          .cons B V (fun r l hl => congrArg (fun p : RV0 O × (J → RV0 O) => p.1) (val (l,r) hl)) td t ht,
          unaryMixedGraph_trans O hO power S s₀ s gs ds,unaryMixedGraph_trans O hO power S t₀ t gt dt,hA,hB,?_⟩
        rw [eq]
        refine ⟨hfor,hback,?_⟩
        intro x y same d hd
        have hsame : unaryMixedLabel O (t (t₀ x)).val = unaryMixedLabel O (t (t₀ y)).val := same
        rcases List.mem_cons.1 hd with he | hd
        · rw [he]
          have raw := (reindexUnaryPoint_label_eq O (unaryTagAppend O) _ _).1
            (ht.refines_labels O (t₀ x) (t₀ y) hsame)
          exact center_step_decides O c a fullB x y raw
        · have result := test (t₀ x) (t₀ y) hsame (shiftCenterTest O V d) (List.mem_map.2 ⟨d,hd,rfl⟩)
          exact (shifted_test_value O V d x).symm.trans (result.trans (shifted_test_value O V d y))
      · exact ⟨I,J,inferInstance,inferInstance,A,B,Equiv.refl A,Equiv.refl B,.nil A,.nil B,
          unaryMixedGraph_refl O hO power S A defA,unaryMixedGraph_refl O hO power S B defB,
          fullA,fullB,forward,(fun x => (ne ⟨x.val,x.property⟩).elim),fun x => (ne ⟨x.val,x.property⟩).elim⟩

include hm hF in
theorem definable_simultaneous_preparation_on_pullbacks {I J : Type} [Finite I] [Finite J]
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} (e : A ≃ B)
    (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
    (graph : UnaryMixedGraphDefinable O hO power S e)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (chart : UnaryDiscCharts O e)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (J ⊕ (Fin 1 ⊕ I)))
      (CenterTestAssignments S.carrier (J ⊕ (Fin 1 ⊕ I))))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t) :
    DefinablePairedUnaryPreparation O hO power S e := by
  obtain ⟨C,decides⟩ := inverse_label_tests_at_finite_centers O hO power S e graph minusOne hm F hF sat immediate
  let tagCenter (c : S.carrier .vf) : CenterTest O J := fun _ => c.val
  let centers := C.toList.map tagCenter
  apply DefinablePairedUnaryPreparation.without_tests O hO power S centers
  apply definable_paired_center_chains O hO power S F minusOne hm hF e defA defB graph fullA fullB chart forward centers
  · intro d hd
    obtain ⟨c,_,rfl⟩ := List.mem_map.1 hd
    exact SortedDefinableOver.coordinate_eq_parameter (M := 𝓜) (A := S.carrier)
      (Var := SumVariables (RVVariables J) (MixedVariables 1 Empty)) .vf (.inr 0) c
  · intro x y tags h
    apply decides x y (congrArg (fun t : RV0 O × (J → RV0 O) => t.2) tags)
    intro c hc
    exact h (tagCenter c) (List.mem_map.2 ⟨c,Finset.mem_toList.2 hc,rfl⟩)

end DefinableChains

end GeneralizedEuler.Section5
