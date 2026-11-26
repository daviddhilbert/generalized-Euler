module

public import Section5.TaggedPositioningInverses
public import Section5.ProductAndBalancedOrderComparison
public import Section5.BalancedContractionClasses

/-! Every tagged family supplied with a fixed-base two-cell
description has equivalent outputs in the two contraction orders. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)
  {k a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem tagged_two_cell_compare_runs
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    (A : RetainedFieldFamily 𝓜 S 2 k) (C : TaggedTwoCellGeometry A)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier A.tags)
      (CenterTestAssignments S.carrier A.tags))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    {U V : RetainedFieldFamily 𝓜 S 0 (k+2)}
    (u : HeadContractionRun A U) (v : HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V)
    (iu : Fin a ≃ U.tags) (iv : Fin b ≃ V.tags) :
    terminalCommonBlowup S neg U V iu iv := by
  classical
  apply product_and_balanced_tags_compare_runs S neg hyp head A sat immediate ?_ u v iu iv
  let Q := A.restrictTags A.productFibersᶜ A.productFibers_definable.compl
  let f := C.position
  let t := C.paradigm
  obtain ⟨g,defG,ginv⟩ := C.definable_inverse_on_nonproduct zero
  choose ca cb ra rb slope hra hrb src dst affine radius using C.nonproduct_chart
  let r (q : A.tags → RV0 O) :=
    if h : q ∉ A.productFibers then oppositeParadigm O (t q) (slope q h) else t q
  have zeroAgree (q : A.tags → RV0 O) : r q = 0 ↔ t q = 0 := by
    by_cases h : q ∉ A.productFibers
    · rw [show r q = oppositeParadigm O (t q) (slope q h) from dite_eq_left h]
      exact opposite_paradigm_zero_iff O _ _
    · rw [show r q = t q from dite_eq_right h]
  let D : Set (K × (A.tags → RV0 O)) := {p | p.2 ∉ A.productFibers ∧ p.1 ∈ A.firstDomain p.2}
  let E' : Set (K × (A.tags → RV0 O)) :=
    {p | p.2 ∉ A.productFibers ∧ p.1 ∈ ((fun x => f x p.2) '' A.firstDomain p.2)}
  let W := MixedVariables 1 A.tags
  let R := RVVariables A.tags
  let add (s : TCsort) : R s → W s := match s with
    | .vf => PEmpty.elim
    | .rv => id
  have defD : SortedDefinableOver 𝓜 S.carrier {a : SortedAssignment Z W | (a .vf 0,a .rv) ∈ D} :=
    (A.productFibers_definable.compl.pullback_relabel add).inter (A.factorProjection_mixed_definable 0)
  have reverse (q : A.tags → RV0 O) (h : q ∉ A.productFibers) (x y : K) :
      (x,y) ∈ A.pairFiber q ↔ (y,q) ∈ E' ∧ rv O (x-g y q) = r q := by
    let B := openDisc O (cb q h) (rb q h)
    have eSrc : A.firstDomain q = openDisc O (ca q h) (ra q h) := src q h
    have eDst : (fun x => f x q) '' A.firstDomain q = B := dst q h
    have aff : RVAffineOn O (openDisc O (ca q h) (ra q h)) (fun x => f x q) (slope q h) :=
      eSrc ▸ affine q h
    have eImg : (fun x => f x q) '' openDisc O (ca q h) (ra q h) = B :=
      (congrArg ((fun x => f x q) '' ·) eSrc).symm.trans eDst
    have short := oppositeParadigm_small_of_target_radius O (hra q h) aff eImg (radius q h)
    have target (p : K × K) (hp : p ∈ positionedCell O (openDisc O (ca q h) (ra q h)) (fun x => f x q) (t q)) :
        p.2 ∈ B := by
      have inside : f p.1 q ∈ B := eImg ▸ Set.mem_image_of_mem (fun x => f x q) hp.1
      change p.2 ∈ openDisc O (cb q h) (rb q h)
      rw [← openDisc_change_center O inside]
      change O.valuation (p.2-f p.1 q) < rb q h
      rw [← unsignedValue_rv,show rv O (p.2-f p.1 q) = t q from hp.2]
      exact radius q h
    have inv (y : K) (hy : y ∈ B) : g y q ∈ openDisc O (ca q h) (ra q h) ∧ f (g y q) q = y := by
      obtain ⟨x,hx,eq⟩ := eDst.symm ▸ hy
      have e : g y q = x := eq ▸ ginv q h x hx
      exact ⟨e.symm ▸ eSrc ▸ hx,(congrArg (fun w => f w q) e).trans eq⟩
    rw [C.shapes,eSrc]
    refine (positionedCell_reverse_mem O B aff short target inv x y).trans ?_
    refine and_congr ?_ ?_
    · exact ⟨fun hy => ⟨h,eDst.symm ▸ hy⟩,fun hy => eDst ▸ hy.2⟩
    · rw [show r q = oppositeParadigm O (t q) (slope q h) from dite_eq_left h]
  have left (x : K) (b : Fin 1 → K) (q : A.tags → RV0 O) :
      (x,b,q) ∈ Q.verticalCarrier ↔ (b 0,q) ∈ E' ∧ rv O (x-g (b 0) q) = r q := by
    change ((x,b,q) ∈ A.verticalCarrier ∧ q ∉ A.productFibers) ↔ _
    by_cases h : q ∉ A.productFibers
    · have eq := (A.verticalCarrier_pairFiber q b x).trans (reverse q h x (b 0))
      exact ⟨fun h' => eq.1 h'.1,fun h' => ⟨eq.2 h',h⟩⟩
    · exact ⟨fun x => (h x.2).elim,fun x => (h x.1.1).elim⟩
  have right (x : K) (b : Fin 1 → K) (q : A.tags → RV0 O) :
      (x,b,q) ∈ (Q.permuteVF (Equiv.swap 0 1)).verticalCarrier ↔ (b 0,q) ∈ D ∧ rv O (x-f (b 0) q) = t q := by
    change ((x,b,q) ∈ (A.permuteVF (Equiv.swap 0 1)).verticalCarrier ∧ q ∉ A.productFibers) ↔ _
    rw [A.swapped_verticalCarrier_pairFiber,C.shapes]
    exact ⟨fun ⟨⟨d,e⟩,h⟩ => ⟨⟨h,d⟩,e⟩,fun ⟨⟨h,d⟩,e⟩ => ⟨⟨d,e⟩,h⟩⟩
  have bij (q : A.tags → RV0 O) : Set.BijOn (fun y => g y q) {y | (y,q) ∈ E'} {x | (x,q) ∈ D} := by
    refine ⟨?_,?_,?_⟩
    · rintro y ⟨h,x,hx,eq⟩
      have e : g y q = x := (congrArg (fun y => g y q) (show f x q = y from eq)).symm.trans (ginv q h x hx)
      refine ⟨h,?_⟩
      change g y q ∈ A.firstDomain q
      rwa [e]
    · rintro y ⟨h,x,hx,ex⟩ z ⟨_,w,hw,ew⟩ eq
      change f x q = y at ex
      change f w q = z at ew
      change g y q = g z q at eq
      have a : g y q = x := (congrArg (fun y => g y q) ex).symm.trans (ginv q h x hx)
      have b : g z q = w := (congrArg (fun y => g y q) ew).symm.trans (ginv q h w hw)
      exact ex.symm.trans ((congrArg (fun u => f u q) (a.symm.trans (eq.trans b))).trans ew)
    · rintro x ⟨h,hx⟩
      exact ⟨f x q,⟨h,x,hx,rfl⟩,ginv q h x hx⟩
  exact tagged_balanced_two_head_refinements O hO power S head he small zero hz Q D E' f g t r
    C.positionDef defG C.paradigmDef left right bij zeroAgree defD sat immediate

end GeneralizedEuler.Section5
