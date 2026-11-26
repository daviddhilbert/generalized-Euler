module

public import Section5.TaggedContractionValues
public import Section5.PaddedLiftKernel
public import Section5.FieldScissorRealization
public import Section5.PositiveRVClasses

/-! Equality of positive VF lift classes gives a tagged mixed
bijection between padded lifts. Contraction of its graph cuts gives
common blowups of the original positive RV classes. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

section PaddedPieces

variable {r n : ℕ}
  (U : Fin r → GradedObject (canonicalStructure (L := L) O hO power) S)
  (p : ∀ i, Fin (U i).1 ↪ Fin n)

@[expose] def paddedMixedPieces (i : Fin r) : MixedCarrier Z n (Fin (U i).2.arity) :=
  {x : SortedAssignment Z (MixedVariables n (Fin (U i).2.arity)) |
    mixedTuple x ∈ (paddedLiftFamily O hO power S (U i).2 (p i)).carrier}

omit [TopologicalSpace K] in
theorem paddedMixedPieces_definable (i : Fin r) :
    SortedDefinableOver 𝓜 S.carrier (paddedMixedPieces S U p i) :=
  (paddedLiftFamily O hO power S (U i).2 (p i)).definable

omit [TopologicalSpace K] in
theorem paddedMixedPieces_finite (i : Fin r) : HasFiniteFieldFibers (paddedMixedPieces S U p i) :=
  (paddedLiftFamily O hO power S (U i).2 (p i)).finite_mixed_fibers

theorem padded_pieces_iso_lift_pieces :
    (taggedMixedCarriers S (fun i => Fin (U i).2.arity) (paddedMixedPieces S U p)
      (paddedMixedPieces_definable S U p)).Iso
      (MixedTaggedFamily.fieldObjectPieces (fun i => ⟨(U i).1,liftFieldObject (U i).2⟩)) := by
  apply MixedTaggedFamily.iso_retag _ _ (Equiv.refl (Fin r))
  intro i
  change MixedDefinablyEquivalent 𝓜 S (paddedMixedPieces S U p i) (ObjectLift.carrier (U i).2)
  unfold paddedMixedPieces
  rw [paddedLiftFamily_carrier_eq S]
  exact paddedLift_iso O hO power S (U i).2 (p i) (Equiv.refl _)

end PaddedPieces

omit [TopologicalSpace K] in
theorem paddedMixedPieces_value
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (zero : S.carrier .vf) (hz : zero.val = 0) {r n : ℕ}
    (U : Fin r → GradedObject 𝓜 S) (p : ∀ i, Fin (U i).1 ↪ Fin (n+1)) (i : Fin r) :
    mixedContractionValue S neg head (paddedMixedPieces S U p i) (paddedMixedPieces_definable S U p i)
      (paddedMixedPieces_finite S U p i) = ((Q).mk') (objectClass 𝓜 S (U i)) := by
  unfold mixedContractionValue
  let A := paddedLiftFamily O hO power S (U i).2 (p i)
  have h := congrArg (contractionValue S neg head) A.of_own_mixed_carrier
  exact h.trans (contractionValue_padded_lift S neg hyp head zero hz (U i).2 (p i))

theorem common_blowup_of_equal_lift_sums
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (recovery : UnaryRecoveryHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (zero : S.carrier .vf) (hz : zero.val = 0)
    {r s : ℕ} (U : Fin r → GradedObject 𝓜 S) (V : Fin s → GradedObject 𝓜 S)
    (eq : ∑ i, liftObjectClass (U i) = ∑ j, liftObjectClass (V j)) :
    CommonBlowup (ElementaryClassStep O hO power S neg)
      (∑ i, objectClass 𝓜 S (U i)) (∑ j, objectClass 𝓜 S (V j)) := by
  let n := max (Finset.univ.sup (fun i => (U i).1)) (Finset.univ.sup (fun j => (V j).1))
  let p (i : Fin r) : Fin (U i).1 ↪ Fin (n+1) :=
    Fin.castLEEmb ((Finset.le_sup (f := fun i => (U i).1) (Finset.mem_univ i)).trans
      ((le_max_left _ _).trans (Nat.le_succ n)))
  let q (j : Fin s) : Fin (V j).1 ↪ Fin (n+1) :=
    Fin.castLEEmb ((Finset.le_sup (f := fun j => (V j).1) (Finset.mem_univ j)).trans
      ((le_max_right _ _).trans (Nat.le_succ n)))
  let A (i : Fin r) : VFObject 𝓜 S := ⟨(U i).1,liftFieldObject (U i).2⟩
  let B (j : Fin s) : VFObject 𝓜 S := ⟨(V j).1,liftFieldObject (V j).2⟩
  have f := MixedTaggedFamily.equal_field_scissors_iso A B eq
  have a := padded_pieces_iso_lift_pieces S U p
  have b := padded_pieces_iso_lift_pieces S V q
  have g := MixedTaggedFamily.iso_trans _ _ _ a (MixedTaggedFamily.iso_trans _ _ _ f (MixedTaggedFamily.iso_symm _ _ b))
  have value := sum_mixedContractionValue_of_tagged_iso S neg hyp head pair recovery he small zero _ _
    (paddedMixedPieces S U p) (paddedMixedPieces S V q)
    (paddedMixedPieces_definable S U p) (paddedMixedPieces_definable S V q)
    (paddedMixedPieces_finite S U p) (paddedMixedPieces_finite S V q) g
  have sameClass : ((Q).mk') (∑ i, objectClass 𝓜 S (U i)) =
      ((Q).mk') (∑ j, objectClass 𝓜 S (V j)) := by
    rw [map_sum,map_sum]
    have left := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => paddedMixedPieces_value S neg hyp head zero hz U p i)
    have right := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => paddedMixedPieces_value S neg hyp head zero hz V q j)
    exact left.symm.trans (value.trans right)
  exact Quotient.exact sameClass

theorem common_blowup_of_equal_lift_classes
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (recovery : UnaryRecoveryHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (zero : S.carrier .vf) (hz : zero.val = 0)
    (liftIso : LiftsRVIsomorphisms 𝓜 S) {a b : RVSemiring 𝓜 S}
    (eq : liftClassHom liftIso a = liftClassHom liftIso b) :
    CommonBlowup (ElementaryClassStep O hO power S neg) a b := by
  obtain ⟨r,U,rfl⟩ := positive_class_represented 𝓜 S a
  obtain ⟨s,V,rfl⟩ := positive_class_represented 𝓜 S b
  rw [map_sum,map_sum] at eq
  simp only [liftClassHom_class] at eq
  exact common_blowup_of_equal_lift_sums S neg hyp head pair recovery he small zero hz U V eq

end GeneralizedEuler.Section5
