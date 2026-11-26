module

public import Section5.UnaryTranslationClass
public import Section5.UnaryFiniteFocusChains
public import Section5.UnaryNormalization

/-! Follow the two special preparations by forward blowups until
their graded labels agree. This proves the unary kernel comparison
with the initial disc charts and forward label contraction supplied. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (F : FieldTerms (convexLanguage L))
  (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
  (sat : ∀ H : Type, Finite H → RealizesFinitelySatisfiableTypes
    (canonicalStructure (L := L) O hO power) (CenterTestVariables S.carrier H) (CenterTestAssignments S.carrier H))
  (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
    ∃ a : SortedIsomorphism (canonicalStructure (L := L) O hO power) (canonicalStructure (L := L) O hO power),
      a.toEmbedding .vf x = y ∧ (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
  {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
  (hneg : rv O (-1) ∈ S.carrier .rv)

local notation "step" => ElementaryClassStep O hO power S hneg
local notation "cert" => fun _ T => UnaryOffsetDefinable O hO power S T
local notation "uc" => unaryLabelClass O hO power S

include hm hF sat immediate he small in
theorem EncodedFocusChain.label_blowups {I J : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} {e : A ≃ B}
    (chain : EncodedFocusChain O cert A B e) :
    ∀ [Finite I] [Finite J] {m n : ℕ} (idx : Fin m ≃ Fin 1 ⊕ I) (idy : Fin n ≃ Fin 1 ⊕ J)
      (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
      (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
      (finA : UnaryFiniteFibers A) (finB : UnaryFiniteFibers B),
      ∃ l, BlowupSteps step l (uc A idx defA fullA finA) (uc B idy defB fullB finB) := by
  induction chain with
  | nil A =>
    intro _ _ _ _ idx idy defA defB fullA fullB finiteA finiteB
    have refl : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) (Equiv.refl A) :=
      fun _ _ h => h
    obtain ⟨z,p⟩ := unary_label_classes_of_mutual_contraction O hO power S idx idy defA defB fullA fullB finiteA finiteB
      (Equiv.refl A) (unaryMixedGraph_refl O hO power S A defA) refl refl he small
    exact ⟨0,congrArg₂ (· + ·) z p⟩
  | cons A T valid defT tail next ih =>
    intro _ _ _ _ idx idy defA defB fullA fullB finiteA finiteB
    let C := encodedUnaryImage O A T
    have defC := unary_mixed_image_definable O hO power S (encodedUnaryStep O A T)
      (encodedUnaryStep_definable O hO power S F minusOne hm hF A T defA defT)
    have fullC := reindexUnaryImage_is_pullback O (unaryTagAppend O) _
      (recodeUnaryTranslation_preserves_pullback O T A fullA valid)
    have offsets := unary_offset_finite_range O hO power S F minusOne hm hF (sat _ inferInstance) immediate he small T defT
    have finiteC := encodedUnaryImage_finiteFibers O A T finiteA offsets
    obtain ⟨l,hl⟩ := ih (unaryPostIndex idx) idy defC defB fullC fullB finiteC finiteB
    refine ⟨l+1,uc C (unaryPostIndex idx) defC fullC finiteC,?_,hl⟩
    exact unary_translation_is_elementary_blowup O hO power S A idx T defT defA fullA finiteA valid offsets defC hneg

include hm hF sat immediate he small in
theorem prepared_unary_common_blowup {I J : Type} [Finite I] [Finite J] {m n : ℕ}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} (e : A ≃ B)
    (idx : Fin m ≃ Fin 1 ⊕ I) (idy : Fin n ≃ Fin 1 ⊕ J)
    (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
    (defE : UnaryMixedGraphDefinable O hO power S e)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (finA : UnaryFiniteFibers A) (finB : UnaryFiniteFibers B)
    (charts : UnaryDiscCharts O e)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e) :
    CommonBlowup step (uc A idx defA fullA finA) (uc B idy defB fullB finB) := by
  have prep := definable_simultaneous_preparation_on_pullbacks O hO power S F minusOne hm hF e defA defB defE
    fullA fullB charts forward (sat _ inferInstance) immediate
  obtain ⟨I',J',m',n',fI,fJ,A',B',idx',idy',s,t,defA',defB',fullA',fullB',finA',finB',hs,ht,z,p⟩ :=
    paired_unary_preparations_compare_classes O hO power S F minusOne hm hF sat immediate he small e defE finA finB prep
  let := fI
  let := fJ
  obtain ⟨lenA,hA⟩ := EncodedFocusChain.label_blowups O hO power S F minusOne hm hF sat immediate he small hneg hs
    idx idx' defA defA' fullA fullA' finA finA'
  obtain ⟨lenB,hB⟩ := EncodedFocusChain.label_blowups O hO power S F minusOne hm hF sat immediate he small hneg ht
    idy idy' defB defB' fullB fullB' finB finB'
  have eq : uc A' idx' defA' fullA' finA' = uc B' idy' defB' fullB' finB' := congrArg₂ (· + ·) z p
  exact ⟨_,lenA,lenB,hA,eq.symm ▸ hB⟩

include hm hF sat immediate he small in
theorem unary_common_blowup_of_chart_partition {I J H : Type} [Finite I] [Finite J] [Finite H] {m n : ℕ}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} (e : A ≃ B)
    (P : UnaryChartPartition O hO power S e H)
    (idx : Fin m ≃ Fin 1 ⊕ I) (idy : Fin n ≃ Fin 1 ⊕ J)
    (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
    (defE : UnaryMixedGraphDefinable O hO power S e)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (finA : UnaryFiniteFibers A) (finB : UnaryFiniteFibers B) :
    CommonBlowup step (uc A idx defA fullA finA) (uc B idy defB fullB finB) := by
  obtain ⟨I',inst,A',s,hs,defS,fullS,chart,forw⟩ :=
    normalize_unary_source O hO power S e P F minusOne hm hF sat immediate defA fullA defE
  let := inst
  let := Fintype.ofFinite (Fin 1 ⊕ I')
  let idx' := (Fintype.equivFin (Fin 1 ⊕ I')).symm
  have defA' := unary_mixed_image_definable O hO power S s defS
  have finA' := EncodedFocusChain.preserves_finite_fibers O hO power S F minusOne hm hF sat immediate he small hs
    inferInstance finA
  have graph := unaryMixedGraph_trans O hO power S s.symm e (unaryMixedGraph_symm O hO power S s defS) defE
  obtain ⟨c,l,r,ha,hb⟩ := prepared_unary_common_blowup O hO power S F minusOne hm hF sat immediate he small hneg
    (s.symm.trans e) idx' idy defA' defB graph fullS fullB finA' finB chart forw
  obtain ⟨k,hk⟩ := EncodedFocusChain.label_blowups O hO power S F minusOne hm hF sat immediate he small hneg hs
    idx idx' defA defA' fullA fullS finA finA'
  exact ⟨c,k+l,r,blowupSteps_trans step hk ha,hb⟩

end GeneralizedEuler.Section5
