module

public import Section5.PositioningLeafAnnotations
public import Section5.TaggedTwoCellOrderComparison
public import Section5.ContractionAnnotations

/-! For a positioned family, use the finite partition of valid leaf
schemes, annotate each part, and compare its contractions. The class
comparison glues across the original tag partition. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {k a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem positioned_family_compare_runs
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    (A : RetainedFieldFamily 𝓜 S 2 k) (C : TaggedPositioningData A)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (RVVariables A.tags))
      (BaseAssignments S.carrier (RVVariables A.tags)))
    (satCenters : ∀ I : Type, Finite I → RealizesFinitelySatisfiableTypes 𝓜
      (CenterTestVariables S.carrier I) (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (localLeaves : ∀ p : SortedAssignment Z (RVVariables A.tags), ∃ W : PositioningLeafScheme 𝓜 S (RVVariables A.tags),
      W.valid O hO power S A.positioningDomainScheme C.graphScheme p)
    {U V : RetainedFieldFamily 𝓜 S 0 (k+2)}
    (u : HeadContractionRun A U) (v : HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V)
    (iu : Fin a ≃ U.tags) (iv : Fin b ≃ V.tags) :
    terminalCommonBlowup S neg U V iu iv := by
  let P := RVVariables A.tags
  have top : SortedDefinableOver 𝓜 S.carrier (Set.univ : Set (SortedAssignment Z P)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  obtain ⟨K',parts,defParts,valid,disj,cover⟩ :=
    uniform_positioning_leaf_schemes O hO power S head.fieldTerms head.minusOne head.minusOne_realizes
      head.fieldTerms_realize sat Set.univ top A.positioningDomainScheme C.graphScheme A.positioningDomainScheme_definable
      C.graphScheme_definable (fun p _ => localLeaves p)
  let : Fintype K' := Fintype.ofFinite K'
  let idx := (Fintype.equivFin K').symm
  let Q (i : Fin (Fintype.card K')) : Set (A.tags → RV0 O) := {t | rvAssignment t ∈ parts (idx i)}
  have defQ (i : Fin (Fintype.card K')) : isRVSet 𝓜 S (Q i) := by
    unfold isRVSet
    convert defParts (idx i) using 1
    ext p
    change rvAssignment (p .rv) ∈ parts (idx i) ↔ p ∈ parts (idx i)
    rw [rvAssignment_eta]
  have disjQ : Pairwise (fun i j => Disjoint (Q i) (Q j)) := by
    intro i j ne
    exact Set.disjoint_left.2 (fun _ hi hj => Set.disjoint_left.1 (disj (fun eq => ne (idx.injective eq))) hi hj)
  have coverQ (r : A.tags → RV0 O) : ∃ i, r ∈ Q i := by
    have hr : rvAssignment r ∈ ⋃ i, parts i := by rw [cover]; trivial
    obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hr
    refine ⟨idx.symm i,?_⟩
    change rvAssignment r ∈ parts (idx (idx.symm i))
    rwa [idx.apply_symm_apply]
  apply contraction_comparison_of_tag_partition S neg A (Equiv.swap 0 1) Q defQ disjQ coverQ ?_ iu iv u v
  intro i L R il ir rl rr
  obtain ⟨B,geometry,e,fix,keep⟩ := C.leaf_annotation (Q i) (defQ i) (idx i).val
    (fun q h => valid (idx i) (rvAssignment q) h)
  apply two_coordinate_comparison_of_field_fixed_annotation S neg hyp head (A.restrictTags (Q i) (defQ i))
    B e fix keep ?_ L R il ir rl rr
  intro _ _ X Y x y ix iy
  exact tagged_two_cell_compare_runs S neg hyp head he small zero hz B geometry (satCenters B.tags B.finiteTags)
    immediate x y ix iy

end GeneralizedEuler.Section5
