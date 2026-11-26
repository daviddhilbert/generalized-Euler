module

public import Section5.FiberProductTests
public import Section5.TagPartitionOrderComparison
public import Section5.TaggedBalancedContractionComparison
public import Section5.TaggedProductContractionComparison

/-! The product and balanced parts of a tagged family can use
different contractions. Exact comparisons on each part give the
comparison of any runs on the original family. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n k l a b c d : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem contraction_commonBlowup_of_exact_endpoints
    (hyp : FieldwiseContractionHypotheses S)
    (A : RetainedFieldFamily 𝓜 S n k) (p : Equiv.Perm (Fin n))
    {U V W X : RetainedFieldFamily 𝓜 S 0 l}
    (u : HeadContractionRun A U) (v : HeadContractionRun (A.permuteVF p) V)
    (w : HeadContractionRun A W) (x : HeadContractionRun (A.permuteVF p) X)
    (iu : Fin a ≃ U.tags) (iv : Fin b ≃ V.tags) (iw : Fin c ≃ W.tags) (ix : Fin d ≃ X.tags)
    (same : W.terminalGradedClass iw (baseRVZero S) rfl = X.terminalGradedClass ix (baseRVZero S) rfl) :
    terminalCommonBlowup S neg U V iu iv := by
  let : Finite A.tags := A.finiteTags
  let ia : Fin (Nat.card A.tags) ≃ A.tags := (Finite.equivFin _).symm
  have one := fieldwise_contraction_runs_common_blowup S neg hyp u w ia ia iu iw
    (by intro p; exact ⟨_,0,0,rfl,rfl⟩)
  have two := fieldwise_contraction_runs_common_blowup S neg hyp x v ia ia ix iv
    (by intro p; exact ⟨_,0,0,rfl,rfl⟩)
  unfold terminalCommonBlowup at one two ⊢
  rw [same] at one
  let eq := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
    (fun {_ _ _} => elementaryClassStep_diamond O hO power S neg)
  exact eq.trans one two

theorem balanced_refinements_compare_runs
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S 2 k)
    (data : ∃ (U : TwoHeadRefinement A) (V : TwoHeadRefinement (A.permuteVF (Equiv.swap 0 1))),
      U.second.target.terminalGradedClass U.enumerate (baseRVZero S) rfl =
      V.second.target.terminalGradedClass V.enumerate (baseRVZero S) rfl)
    {W X : RetainedFieldFamily 𝓜 S 0 (k+2)}
    (u : HeadContractionRun A W) (v : HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) X)
    (iw : Fin a ≃ W.tags) (ix : Fin b ≃ X.tags) :
    terminalCommonBlowup S neg W X iw ix := by
  obtain ⟨U,V,eq⟩ := data
  have first := U.compare S neg hyp head u iw
  have last := V.compare S neg hyp head v ix
  unfold terminalCommonBlowup at first last ⊢
  rw [eq] at first
  let atom := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
    (fun {_ _ _} => elementaryClassStep_diamond O hO power S neg)
  exact atom.trans first (atom.symm last)

theorem product_and_balanced_tags_compare_runs
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S 2 k)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier A.tags)
      (CenterTestAssignments S.carrier A.tags))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (balanced : let C := A.restrictTags A.productFibersᶜ A.productFibers_definable.compl
      ∃ (U : TwoHeadRefinement C) (V : TwoHeadRefinement (C.permuteVF (Equiv.swap 0 1))),
        U.second.target.terminalGradedClass U.enumerate (baseRVZero S) rfl =
        V.second.target.terminalGradedClass V.enumerate (baseRVZero S) rfl)
    {W X : RetainedFieldFamily 𝓜 S 0 (k+2)}
    (u : HeadContractionRun A W) (v : HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) X)
    (iw : Fin a ≃ W.tags) (ix : Fin b ≃ X.tags) :
    terminalCommonBlowup S neg W X iw ix := by
  classical
  let cut (b : Bool) := if b then A.productFibers else A.productFibersᶜ
  have defCut (b : Bool) : isRVSet 𝓜 S (cut b) := by
    cases b
    · exact A.productFibers_definable.compl
    · exact A.productFibers_definable
  have disj : Pairwise (fun b c => Disjoint (cut b) (cut c)) := by
    intro b c h
    cases b <;> cases c
    · exact (h rfl).elim
    · exact Set.disjoint_left.2 (fun _ hn hp => hn hp)
    · exact Set.disjoint_left.2 (fun _ hp hn => hn hp)
    · exact (h rfl).elim
  have cover (t : A.tags → RV0 O) : ∃ b, t ∈ cut b := by
    by_cases h : t ∈ A.productFibers
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  apply contraction_comparison_of_tag_partition S neg A (Equiv.swap 0 1) cut defCut disj cover ?_ iw ix u v
  intro b Y Z' iy iz yl zr
  cases b
  · exact balanced_refinements_compare_runs S neg hyp head _ balanced yl zr iy iz
  · let Q := A.restrictTags A.productFibers A.productFibers_definable
    have shape (b : Fin 2 → K) (t : Q.tags → RV0 O) :
        (b,t) ∈ Q.carrier ↔ (b 0,t) ∈ Q.factorProjection 0 ∧ (b 1,t) ∈ Q.factorProjection 1 := by
      constructor
      · intro h
        exact ⟨⟨b,h,rfl⟩,⟨b,h,rfl⟩⟩
      · rintro ⟨⟨x,⟨h,tGood⟩,e⟩,⟨y,⟨j,_⟩,f⟩⟩
        exact ⟨tGood b ⟨x,h,e⟩ ⟨y,j,f⟩,tGood⟩
    obtain ⟨U,V,_,_,iu,iv,ul,vr,eq⟩ :=
      tagged_product_contraction_orders_of_definable_factors O hO power S Q _ _ shape
        (Q.factorProjection_mixed_definable 0) (Q.factorProjection_mixed_definable 1)
        head.fieldTerms head.minusOne head.minusOne_realizes head.fieldTerms_realize sat immediate (baseRVZero S) rfl
    exact contraction_commonBlowup_of_exact_endpoints S neg hyp Q (Equiv.swap 0 1) yl zr ul vr iy iz iu iv eq

end GeneralizedEuler.Section5
