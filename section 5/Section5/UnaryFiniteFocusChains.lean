module

public import Section5.UnaryGradedClassComparison

/-! Finite RV fibers survive a fixed-base unary focus chain. Thus
the mutually contracted endpoints can be compared in the graded
positive RV semiring. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (F : FieldTerms (convexLanguage L))
  (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cert" => fun _ T => UnaryOffsetDefinable O hO power S T

variable (sat : ∀ H : Type, Finite H → RealizesFinitelySatisfiableTypes
    (canonicalStructure (L := L) O hO power) (CenterTestVariables S.carrier H) (CenterTestAssignments S.carrier H))
  (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
    ∃ a : SortedIsomorphism (canonicalStructure (L := L) O hO power) (canonicalStructure (L := L) O hO power),
      a.toEmbedding .vf x = y ∧ (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
  {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)

include hm hF sat immediate he small in
theorem EncodedFocusChain.preserves_finite_fibers {I J : Type}
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} {e : A ≃ B}
    (chain : EncodedFocusChain O cert A B e) : Finite I → UnaryFiniteFibers A → UnaryFiniteFibers B := by
  induction chain with
  | nil _ => exact fun _ h => h
  | @cons I J A T valid defT B tail next ih =>
    intro finiteI finite
    let := finiteI
    apply ih (inferInstance : Finite (I ⊕ Unit))
    exact encodedUnaryImage_finiteFibers O A T finite
      (unary_offset_finite_range O hO power S F minusOne hm hF (sat _ inferInstance) immediate he small T defT)

include hm hF sat immediate he small in
theorem paired_unary_preparations_compare_classes {I J : Type} [Finite I] [Finite J]
    {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} (e : A ≃ B)
    (defE : UnaryMixedGraphDefinable O hO power S e)
    (finiteA : UnaryFiniteFibers A) (finiteB : UnaryFiniteFibers B)
    (prep : DefinablePairedUnaryPreparation O hO power S e) :
    ∃ (I' J' : Type) (m n : ℕ) (fi : Finite I') (fj : Finite J')
      (A' : Set (K × (I' → RV0 O))) (B' : Set (K × (J' → RV0 O)))
      (idx : Fin m ≃ Fin 1 ⊕ I') (idy : Fin n ≃ Fin 1 ⊕ J')
      (s : A ≃ A') (t : B ≃ B')
      (defA : UnaryPullbackDefinable O hO power S A') (defB : UnaryPullbackDefinable O hO power S B')
      (fullA : IsUnaryPullback O A') (fullB : IsUnaryPullback O B')
      (finA : UnaryFiniteFibers A') (finB : UnaryFiniteFibers B'),
      EncodedFocusChain O cert A A' s ∧ EncodedFocusChain O cert B B' t ∧
      letI := fi
      letI := fj
      let a := unaryLabelObjects O hO power S A' idx defA fullA finA
      let b := unaryLabelObjects O hO power S B' idy defB fullB finB
      objectClass 𝓜 S ⟨0,a.1⟩ = objectClass 𝓜 S ⟨0,b.1⟩ ∧
      objectClass 𝓜 S ⟨1,a.2⟩ = objectClass 𝓜 S ⟨1,b.2⟩ := by
  obtain ⟨I',J',fI,fJ,A',B',s,t,hs,ht,gs,gt,fullA,fullB,hfor,hback,_⟩ := prep
  let := fI
  let := fJ
  let defA := unary_mixed_image_definable O hO power S s gs
  let defB := unary_mixed_image_definable O hO power S t gt
  let finA := EncodedFocusChain.preserves_finite_fibers O hO power S F minusOne hm hF sat immediate he small hs
    inferInstance finiteA
  let finB := EncodedFocusChain.preserves_finite_fibers O hO power S F minusOne hm hF sat immediate he small ht
    inferInstance finiteB
  let := Fintype.ofFinite (Fin 1 ⊕ I')
  let := Fintype.ofFinite (Fin 1 ⊕ J')
  let idx := (Fintype.equivFin (Fin 1 ⊕ I')).symm
  let idy := (Fintype.equivFin (Fin 1 ⊕ J')).symm
  have graph := unaryMixedGraph_trans O hO power S s.symm (e.trans t)
    (unaryMixedGraph_symm O hO power S s gs) (unaryMixedGraph_trans O hO power S e t defE gt)
  refine ⟨I',J',_,_,fI,fJ,A',B',idx,idy,s,t,defA,defB,fullA,fullB,finA,finB,hs,ht,?_⟩
  exact unary_label_classes_of_mutual_contraction O hO power S idx idy defA defB fullA fullB finA finB
    (s.symm.trans (e.trans t)) graph hfor hback he small

end GeneralizedEuler.Section5
