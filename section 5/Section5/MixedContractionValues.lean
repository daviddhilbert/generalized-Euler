module

public import Section5.ContractionValues
public import Section5.UnaryFactorizationComparison
public import Section5.UnaryFactorizationInduction
public import Section5.MixedFiniteFamilies

/-! The contraction class of a definable mixed carrier with finite
field fibers respects the finite cuts and arrows of a unary factorization. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n : ℕ} {I J : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

@[expose] def HasFiniteFieldFibers {m : ℕ} (D : MixedCarrier Z m I) : Prop :=
  ∀ x : Fin m → K, {a : D | a.val .vf = x}.Finite

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem HasFiniteFieldFibers.mono {A D : MixedCarrier Z n I}
    (finite : HasFiniteFieldFibers A) (sub : D ⊆ A) : HasFiniteFieldFibers D := by
  intro x
  let f (a : D) : A := ⟨a.val,sub a.property⟩
  have inj : Function.Injective f := fun _ _ eq => Subtype.ext (congrArg (fun a : A => a.val) eq)
  exact (finite x).preimage inj.injOn

@[expose] def mixedContractionValue [Finite I] (head : HeadPreparationHypotheses O hO power S)
    (A : MixedCarrier Z (n+1) I) (d : SortedDefinableOver 𝓜 S.carrier A)
    (finite : HasFiniteFieldFibers A) : (Q).Quotient :=
  contractionValue S neg head (RetainedFieldFamily.ofFiniteMixedCarrier A d finite)

theorem mixedContractionValue_partition [Finite I]
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A : MixedCarrier Z (n+1) I) (d : SortedDefinableOver 𝓜 S.carrier A)
    (finite : HasFiniteFieldFibers A) {q : ℕ} (D : Fin q → MixedCarrier Z (n+1) I)
    (defD : ∀ i, SortedDefinableOver 𝓜 S.carrier (D i)) (sub : ∀ i, D i ⊆ A)
    (disj : Pairwise (fun i j => Disjoint (D i) (D j))) (cover : (⋃ i, D i) = A) :
    mixedContractionValue S neg head A d finite =
      ∑ i, mixedContractionValue S neg head (D i) (defD i) (finite.mono (sub i)) := by
  let F := RetainedFieldFamily.ofFiniteMixedCarrier A d finite
  have asSet := RetainedFieldFamily.ofFiniteMixedCarrier_as_set A d finite
  have sub' (i : Fin q) : D i ⊆ {a | mixedTuple a ∈ F.carrier} := asSet.symm ▸ sub i
  exact contractionValue_partition S neg hyp head F D defD sub' disj
    (fun a h => Set.mem_iUnion.1 (cover.symm ▸ (asSet ▸ h : a ∈ A)))

private def MixedGraphIso.onEqualSets
    {A A' : MixedCarrier Z n I} {B B' : MixedCarrier Z n J}
    (f : MixedGraphIso 𝓜 S A B) (eA : A' = A) (eB : B' = B) :
    MixedGraphIso 𝓜 S A' B' := by
  subst A'
  subst B'
  exact f

private theorem MixedGraphIso.onEqualSets_apply
    {A A' : MixedCarrier Z n I} {B B' : MixedCarrier Z n J}
    (f : MixedGraphIso 𝓜 S A B) (eA : A' = A) (eB : B' = B) (a : A') :
    ((f.onEqualSets S eA eB).equiv a).val = (f.equiv ⟨a.val,eA ▸ a.property⟩).val := by
  subst A'
  subst B'
  rfl

theorem mixedContractionValue_of_relatively_unary [Finite I] [Finite J]
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg)
    {A : MixedCarrier Z (n+1) I} {B : MixedCarrier Z (n+1) J}
    (f : MixedGraphIso 𝓜 S A B) (i : Fin (n+1)) (fix : FixesOutside f {i})
    (da : SortedDefinableOver 𝓜 S.carrier A) (db : SortedDefinableOver 𝓜 S.carrier B)
    (fa : HasFiniteFieldFibers A) (fb : HasFiniteFieldFibers B) :
    mixedContractionValue S neg head A da fa = mixedContractionValue S neg head B db fb := by
  let F := RetainedFieldFamily.ofFiniteMixedCarrier A da fa
  let G := RetainedFieldFamily.ofFiniteMixedCarrier B db fb
  have es := RetainedFieldFamily.ofFiniteMixedCarrier_as_set A da fa
  have et := RetainedFieldFamily.ofFiniteMixedCarrier_as_set B db fb
  let g := f.onEqualSets S es et
  apply contractionValue_of_relatively_unary S neg hyp head pair (A := F) (B := G) g i
  · intro a j ne
    change ((f.onEqualSets S es et).equiv a).val .vf j = a.val .vf j
    exact (congrArg (fun b : SortedAssignment Z (MixedVariables (n+1) J) => b .vf j)
      (MixedGraphIso.onEqualSets_apply S f es et a)).trans
      (fix ⟨a.val,es ▸ a.property⟩ j (fun h => ne (Finset.mem_singleton.1 h)))
  · intro a
    exact Subsingleton.elim _ _

theorem UnaryPiecewise.mixedContractionValue_eq
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (basePoint : S.carrier .vf)
    {A : MixedCarrier Z (n+1) I} {B : MixedCarrier Z (n+1) J}
    {moving : Finset (Fin (n+1))} {f : MixedGraphIso 𝓜 S A B} (h : UnaryPiecewise 𝓜 S (n+1) moving f) :
    ∀ [Finite I] [Finite J] (da : SortedDefinableOver 𝓜 S.carrier A)
      (db : SortedDefinableOver 𝓜 S.carrier B) (fa : HasFiniteFieldFibers A) (fb : HasFiniteFieldFibers B),
      mixedContractionValue S neg head A da fa = mixedContractionValue S neg head B db fb := by
  induction h with
  | fixed f fix =>
    intro _ _ da db fa fb
    exact mixedContractionValue_of_relatively_unary S neg hyp head pair f 0
      (fun a j _ => fix a j (Finset.notMem_empty j)) da db fa fb
  | unary f i _ fix =>
    intro _ _ da db fa fb
    exact mixedContractionValue_of_relatively_unary S neg hyp head pair f i fix da db fa fb
  | @trans moving I J T finiteJ A B C f g _ _ ihf ihg =>
    intro _ _ da dc fa fc
    have db := f.target_definable da
    have fb := f.target_finiteFieldFibers O hO power S head he small basePoint fa
    exact (ihf da db fa fb).trans (ihg db dc fb fc)
  | symm _ ih =>
    intro _ _ db da fb fa
    exact (ih da db fa fb).symm
  | widen _ _ ih => exact ih
  | @partition moving I J A B f q D defD sub disj cover _ ih =>
    intro _ _ da db fa fb
    let R (i : Fin q) := f.rangeOver (sub i)
    have subR (i : Fin q) : R i ⊆ B := by
      rintro _ ⟨a,rfl⟩
      exact (f.equiv ⟨a.val,sub i a.property⟩).property
    have defR (i : Fin q) := (f.restrict (sub i) (defD i)).target_definable (defD i)
    obtain ⟨disjR,coverR⟩ := f.rangeOver_partition D sub disj cover
    calc
      _ = ∑ i, mixedContractionValue S neg head (D i) (defD i) (fa.mono (sub i)) :=
        mixedContractionValue_partition S neg hyp head A da fa D defD sub disj cover
      _ = ∑ i, mixedContractionValue S neg head (R i) (defR i) (fb.mono (subR i)) :=
        Finset.sum_congr rfl (fun i _ => ih i (defD i) (defR i) (fa.mono (sub i)) (fb.mono (subR i)))
      _ = _ := (mixedContractionValue_partition S neg hyp head B db fb R defR subR disjR coverR).symm

end GeneralizedEuler.Section5
