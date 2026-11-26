module

public import Section5.MixedContractionValues

/-! Use fixed-base recovery and exchange to compare the contraction
classes of arbitrary mixed bijections in a common ambient field arity. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n : ℕ} {I J : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

set_option linter.style.haveILetI false in
structure UnaryRecoveryHypotheses where
  saturated : ∀ n (I : Type), Finite I → RealizesFinitelySatisfiableTypes 𝓜
    (WithBase S.carrier (MixedVariables n I)) (BaseAssignments S.carrier (MixedVariables n I))
  exchange : letI := valuedStructureOfSorted 𝓜 ∅
    ∀ (D : Set K) (x y : K),
      y ∈ Substructure.closure (convexLanguage L) (insert x D) →
      y ∉ Substructure.closure (convexLanguage L) D →
      x ∈ Substructure.closure (convexLanguage L) (insert y D)
  move : letI := valuedStructureOfSorted 𝓜 ∅
    ∀ n (a : Fin n → K) (y : K),
      y ∉ Substructure.closure (convexLanguage L) (S.carrier .vf ∪ Set.range a) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf y ≠ y ∧
        (∀ x ∈ S.carrier .vf ∪ Set.range a, e.toEmbedding .vf x = x) ∧
        ∀ t : RV0 O, e.toEmbedding .rv t = t

theorem mixedContractionValue_of_iso [Finite I] [Finite J]
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (recovery : UnaryRecoveryHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (basePoint : S.carrier .vf)
    {A : MixedCarrier Z (n+1) I} {B : MixedCarrier Z (n+1) J}
    (f : MixedGraphIso 𝓜 S A B)
    (da : SortedDefinableOver 𝓜 S.carrier A) (db : SortedDefinableOver 𝓜 S.carrier B)
    (fa : HasFiniteFieldFibers A) (fb : HasFiniteFieldFibers B) :
    mixedContractionValue S neg head A da fa = mixedContractionValue S neg head B db fb := by
  classical
  have outside : FixesOutside f Finset.univ := fun _ i h => (h (Finset.mem_univ i)).elim
  have chain := unary_piecewise_factorization O hO power S head.fieldTerms head.minusOne
    head.minusOne_realizes head.fieldTerms_realize (recovery.saturated (n+1))
    recovery.exchange (recovery.move (n+1)) Finset.univ f da outside
  exact chain.mixedContractionValue_eq S neg hyp head pair he small basePoint da db fa fb

omit [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)] in
theorem RetainedFieldFamily.finite_mixed_fibers
    {M : SortedStructure L E (CanonicalSort O)} {T : SortedSubstructure M}
    (A : RetainedFieldFamily M T n 0) :
    HasFiniteFieldFibers {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier} := by
  intro x
  let C := {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier}
  let F := {a : C | a.val .vf = x}
  let g (a : F) : A.tags → RV0 O := a.val.val .rv
  have inj : Function.Injective g := by
    intro a b e
    apply Subtype.ext
    apply Subtype.ext
    calc
      a.val.val = mixedAssignment x (g a) := by
        rw [← a.property]
        exact (mixedAssignment_eta a.val.val).symm
      _ = mixedAssignment x (g b) := congrArg (mixedAssignment x) e
      _ = b.val.val := by
        rw [← b.property]
        exact mixedAssignment_eta b.val.val
  let mem (a : F) : g a ∈ {q : A.tags → RV0 O | (x,q) ∈ A.carrier ∧ q ∘ A.select = Fin.elim0} := by
    have source := a.val.property
    change (a.val.val .vf,a.val.val .rv) ∈ A.carrier at source
    exact ⟨a.property ▸ source,Subsingleton.elim _ _⟩
  let read (a : C) : A.tags → RV0 O := a.val .rv
  have image : (read '' F).Finite := by
    apply (A.finiteFibers x Fin.elim0).subset
    rintro _ ⟨a,ha,rfl⟩
    exact mem ⟨a,ha⟩
  exact image.of_finite_image (fun a ha b hb eq =>
    congrArg (fun y : F => y.val) (inj (show g ⟨a,ha⟩ = g ⟨b,hb⟩ from eq)))

omit [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)] in
theorem RetainedFieldFamily.of_own_mixed_carrier
    {M : SortedStructure L E (CanonicalSort O)} {T : SortedSubstructure M}
    (A : RetainedFieldFamily M T n 0) :
    letI := A.finiteTags
    ofFiniteMixedCarrier _ A.definable A.finite_mixed_fibers = A := by
  cases A with
  | mk tags finiteTags select carrier definable finiteFibers =>
    have eq : select = Fin.elim0 := Subsingleton.elim _ _
    subst select
    rfl

theorem contractionValue_of_mixed_iso
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (recovery : UnaryRecoveryHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (basePoint : S.carrier .vf)
    {A B : RetainedFieldFamily 𝓜 S (n+1) 0}
    (f : MixedDefinablyEquivalent 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier}) :
    contractionValue S neg head A = contractionValue S neg head B := by
  let := A.finiteTags
  let := B.finiteTags
  obtain ⟨e,defe⟩ := f
  have eq := mixedContractionValue_of_iso S neg hyp head pair recovery he small basePoint
    ⟨e,defe⟩ A.definable B.definable A.finite_mixed_fibers B.finite_mixed_fibers
  unfold mixedContractionValue at eq
  rwa [A.of_own_mixed_carrier,B.of_own_mixed_carrier] at eq

end GeneralizedEuler.Section5
