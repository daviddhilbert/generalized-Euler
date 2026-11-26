module

public import Section5.UnaryTagReindexing

/-! Encode the images and graphs of paired unary translations in
the finite variable indices used for the next step. -/

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

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def encodedUnaryImage (A : Set (K × (I → RV0 O)))
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O))) : Set (K × (I ⊕ Unit → RV0 O)) :=
  reindexUnaryPoint (unaryTagAppend O) '' (recodeUnaryTranslation O T '' A)

@[expose] def encodedUnaryStep (A : Set (K × (I → RV0 O)))
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O))) : A ≃ encodedUnaryImage O A T :=
  (unaryImageIso O A T).trans (reindexUnaryImage (unaryTagAppend O) _)

omit [LinearOrder K] [IsStrictOrderedRing K] [Finite I] in
private theorem encode_extendedPair_eq (b : SortedAssignment (CanonicalSort O) (MixedVariables 1 (I ⊕ Unit))) :
    reindexUnaryPoint (unaryTagAppend O) (extendedUnaryPair O b) = unaryPair O b :=
  Prod.ext rfl ((unaryTagAppend O).apply_symm_apply (b .rv))

variable (F : FieldTerms (convexLanguage L))
  (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

include hm hF in
theorem encodedUnaryStep_definable (A : Set (K × (I → RV0 O)))
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (defA : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I) | unaryPair O a ∈ A})
    (defOffset : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
        (v : fieldAssignment 1 (CanonicalSort O)) => v .vf 0 = T.offset (a .rv) (rv O (a .vf 0)))) :
    UnaryMixedGraphDefinable O hO power S (encodedUnaryStep O A T) := by
  refine ((recodeUnaryTranslation_graph_definable O hO power S T F minusOne hm hF defOffset).inter_left defA).congr ?_
  intro a b
  constructor
  · rintro ⟨h,ha⟩
    refine ⟨ha,?_⟩
    change reindexUnaryPoint (unaryTagAppend O) (recodeUnaryTranslation O T (unaryPair O a)) = unaryPair O b
    rw [h,encode_extendedPair_eq]
  · rintro ⟨ha,h⟩
    refine ⟨(reindexUnaryPoint (unaryTagAppend O)).injective ?_,ha⟩
    rw [encode_extendedPair_eq]
    exact h

omit [Finite J] in
theorem unary_mixed_image_definable {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
    (e : A ≃ B) (graph : UnaryMixedGraphDefinable O hO power S e) :
    SortedDefinableOver 𝓜 S.carrier
      {b : SortedAssignment (CanonicalSort O) (MixedVariables 1 J) | unaryPair O b ∈ B} := by
  let all : Set (SortedAssignment (CanonicalSort O) (MixedVariables 1 I)) := Set.univ
  have allDef : SortedDefinableOver 𝓜 S.carrier all :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  convert graph.image allDef using 1
  ext b
  change unaryPair O b ∈ B ↔ ∃ a, a ∈ all ∧ ∃ ha : unaryPair O a ∈ A, (e ⟨_,ha⟩).val = unaryPair O b
  constructor
  · intro hb
    obtain ⟨x,hx⟩ := e.surjective ⟨unaryPair O b,hb⟩
    let a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)
      | .vf => fun _ => x.val.1
      | .rv => x.val.2
    exact ⟨a,Set.mem_univ _,x.property,congrArg Subtype.val hx⟩
  · rintro ⟨a,_,ha,he⟩
    exact he ▸ (e ⟨unaryPair O a,ha⟩).property

theorem unaryMixedGraph_refl (A : Set (K × (I → RV0 O)))
    (defA : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I) | unaryPair O a ∈ A}) :
    UnaryMixedGraphDefinable O hO power S (Equiv.refl A) := by
  have diag := DefinableRelation.diagonal (M := 𝓜) (A := S.carrier) (U := MixedVariables 1 I)
  refine (diag.inter_left defA).congr ?_
  intro a b
  constructor
  · rintro ⟨rfl,h⟩
    exact ⟨h,rfl⟩
  · rintro ⟨h,eq⟩
    refine ⟨?_,h⟩
    funext s i
    cases s
    · rw [Subsingleton.elim i (0 : Fin 1)]
      exact congrArg Prod.fst eq
    · exact congrFun (congrArg Prod.snd eq) i

omit [Finite I] in
theorem unaryMixedGraph_trans {H : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} {D : Set (K × (H → RV0 O))}
    (e : A ≃ B) (f : B ≃ D) (he : UnaryMixedGraphDefinable O hO power S e)
    (hf : UnaryMixedGraphDefinable O hO power S f) :
    UnaryMixedGraphDefinable O hO power S (e.trans f) := by
  refine (he.comp hf).congr ?_
  intro a d
  constructor
  · rintro ⟨b,⟨ha,hab⟩,⟨hb,hbd⟩⟩
    have eq : e ⟨unaryPair O a,ha⟩ = ⟨unaryPair O b,hb⟩ := Subtype.ext hab
    refine ⟨ha,?_⟩
    change (f (e ⟨unaryPair O a,ha⟩)).val = unaryPair O d
    rw [eq]
    exact hbd
  · rintro ⟨ha,hd⟩
    let b := e ⟨unaryPair O a,ha⟩
    let w : SortedAssignment (CanonicalSort O) (MixedVariables 1 J)
      | .vf => fun _ => b.val.1
      | .rv => b.val.2
    exact ⟨w,⟨ha,rfl⟩,⟨b.property,hd⟩⟩

omit [Finite I] [Finite J] in
theorem unaryMixedGraph_symm {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
    (e : A ≃ B) (he : UnaryMixedGraphDefinable O hO power S e) :
    UnaryMixedGraphDefinable O hO power S e.symm := by
  refine he.transpose.congr ?_
  intro b a
  constructor
  · rintro ⟨ha,eq⟩
    change (e ⟨unaryPair O a,ha⟩).val = unaryPair O b at eq
    have hb : unaryPair O b ∈ B := eq ▸ (e ⟨unaryPair O a,ha⟩).property
    have matchB : e ⟨unaryPair O a,ha⟩ = ⟨unaryPair O b,hb⟩ := Subtype.ext eq
    refine ⟨hb,?_⟩
    change (e.symm ⟨unaryPair O b,hb⟩).val = unaryPair O a
    rw [← matchB,e.symm_apply_apply]
  · rintro ⟨hb,eq⟩
    change (e.symm ⟨unaryPair O b,hb⟩).val = unaryPair O a at eq
    have ha : unaryPair O a ∈ A := eq ▸ (e.symm ⟨unaryPair O b,hb⟩).property
    have matchA : e.symm ⟨unaryPair O b,hb⟩ = ⟨unaryPair O a,ha⟩ := Subtype.ext eq
    refine ⟨ha,?_⟩
    change (e ⟨unaryPair O a,ha⟩).val = unaryPair O b
    rw [← matchA,e.apply_symm_apply]

variable {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
  (e : A ≃ B) (C : Set (RV0 O × (J → RV0 O))) (focus : RV0 O × (J → RV0 O) → B)

local notation "T₁" => pairedSourceTranslation O e C focus
local notation "T₂" => pairedTargetTranslation O C focus

@[expose] def encodedPairedConjugate : encodedUnaryImage O A T₁ ≃ encodedUnaryImage O B T₂ :=
  reindexUnaryEquiv (unaryTagAppend O) (unaryTagAppend O) (pairedUnaryConjugate O e C focus)

omit [LinearOrder K] [IsStrictOrderedRing K] [Finite I] [Finite J] in
theorem encodedPairedConjugate_apply (x : A) :
    encodedPairedConjugate O e C focus (encodedUnaryStep O A T₁ x) = encodedUnaryStep O B T₂ (e x) := by
  unfold encodedPairedConjugate
  change reindexUnaryEquiv (unaryTagAppend O) (unaryTagAppend O) (pairedUnaryConjugate O e C focus)
    (reindexUnaryImage _ _ (unaryImageIso O A T₁ x)) = _
  rw [reindexUnaryEquiv_apply]
  apply congrArg (reindexUnaryImage _ _)
  apply Subtype.ext
  exact pairedUnaryConjugate_apply O e C focus x

include hm hF in
theorem encodedPairedConjugate_definable
    (defE : UnaryMixedGraphDefinable O hO power S e)
    (defFocus : targetFocusGraphDefinable O hO power S C focus)
    (full : IsUnaryPullback O A)
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e) :
    UnaryMixedGraphDefinable O hO power S (encodedPairedConjugate O e C focus) := by
  refine (pairedUnaryConjugate_definable O hO power S e C focus defE defFocus full contract F minusOne hm hF).congr ?_
  intro a b
  let p := reindexUnaryImage (unaryTagAppend O) (recodeUnaryTranslation O T₁ '' A)
  let q := reindexUnaryImage (unaryTagAppend O) (recodeUnaryTranslation O T₂ '' B)
  have ap : reindexUnaryPoint (unaryTagAppend O) (extendedUnaryPair O a) = unaryPair O a := encode_extendedPair_eq O a
  have bp : reindexUnaryPoint (unaryTagAppend O) (extendedUnaryPair O b) = unaryPair O b := encode_extendedPair_eq O b
  constructor
  · rintro ⟨ha,he⟩
    let x : (recodeUnaryTranslation O T₁ '' A) := ⟨extendedUnaryPair O a,ha⟩
    have hx : (p x).val = unaryPair O a := ap
    have hm : unaryPair O a ∈ encodedUnaryImage O A T₁ := hx ▸ (p x).property
    refine ⟨hm,?_⟩
    have ep : (⟨unaryPair O a,hm⟩ : encodedUnaryImage O A T₁) = p x := Subtype.ext hx.symm
    rw [ep,encodedPairedConjugate]
    change (reindexUnaryEquiv (unaryTagAppend O) (unaryTagAppend O) (pairedUnaryConjugate O e C focus)
      (reindexUnaryImage (unaryTagAppend O) _ x)).val = _
    rw [reindexUnaryEquiv_apply]
    change reindexUnaryPoint (unaryTagAppend O) (pairedUnaryConjugate O e C focus x).val = unaryPair O b
    rw [he,bp]
  · rintro ⟨ha,he⟩
    obtain ⟨x,hx⟩ := p.surjective ⟨unaryPair O a,ha⟩
    have hraw : x.val = extendedUnaryPair O a :=
      (reindexUnaryPoint (unaryTagAppend O)).injective ((congrArg Subtype.val hx).trans ap.symm)
    have hm : extendedUnaryPair O a ∈ recodeUnaryTranslation O T₁ '' A := hraw ▸ x.property
    refine ⟨hm,?_⟩
    have ep : (⟨extendedUnaryPair O a,hm⟩ : (recodeUnaryTranslation O T₁ '' A)) = x := Subtype.ext hraw.symm
    rw [ep]
    apply (reindexUnaryPoint (unaryTagAppend O)).injective
    rw [bp]
    change (q (pairedUnaryConjugate O e C focus x)).val = unaryPair O b
    rw [← reindexUnaryEquiv_apply]
    change (encodedPairedConjugate O e C focus (p x)).val = unaryPair O b
    rw [hx]
    exact he

end GeneralizedEuler.Section5
