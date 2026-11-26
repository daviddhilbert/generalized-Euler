module

public import Section5.PositioningLeafLabelFunctions
public import Section5.LocalPositioningLeafSchemes

/-! Separate the unary chart inputs from the first-order
construction of leaf labels. The inputs are applied over the
original base with the RV tuple named. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

/-- Section 3 supplies constant and concentric branches and the
branchwise mean-value data. The statements below retain both sorts
of the generated base. -/
structure PositioningChartHypotheses where
  saturatedRV : ∀ I : Type, Finite I → RealizesFinitelySatisfiableTypes 𝓜
    (WithBase S.carrier (RVVariables I)) (BaseAssignments S.carrier (RVVariables I))
  saturatedCenters : ∀ I : Type, Finite I → RealizesFinitelySatisfiableTypes 𝓜
    (CenterTestVariables S.carrier I) (CenterTestAssignments S.carrier I)
  saturatedLocalCenters : ∀ I : Type, Finite I → ∀ p : SortedAssignment Z (RVVariables I),
    let T := (𝓜).termGenerated (namedTuple S p)
    RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables T.carrier (Empty ⊕ Bool))
      (CenterTestAssignments T.carrier (Empty ⊕ Bool))
  immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
    ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
      (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t
  localImmediate : ∀ I : Type, Finite I → ∀ p : SortedAssignment Z (RVVariables I),
    let T := (𝓜).termGenerated (namedTuple S p)
    ∀ x y : K, (∀ c : T.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ T.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t
  branches : ∀ (I : Type), Finite I → ∀ p : SortedAssignment Z (RVVariables I),
    let T := (𝓜).termGenerated (namedTuple S p)
    ∀ (D : Set K) (f : K → K),
      DefinableRelation 𝓜 T.carrier (fun a b : fieldAssignment 1 Z =>
        a .vf 0 ∈ D ∧ f (a .vf 0) = b .vf 0) →
      ∃ (d : K → K) (code : K → RV0 O),
        SortedDefinableOver 𝓜 T.carrier
          {w : SortedAssignment Z (MixedVariables 1 (Empty ⊕ Bool)) |
            w .vf 0 ∈ D ∧ w .rv ∘ Sum.inr = affineData O code d (w .vf 0)} ∧
        (∀ a ∈ D, ∀ b ∈ D, code a = code b → a ≠ b →
          ∃ c ∈ Set.uIcc a b, f a - f b = d c * (a - b)) ∧
        ∀ t, let B := {x ∈ D | code x = t}
          (∀ x ∈ B, ∀ y ∈ B, f x = f y) ∨ (Set.InjOn f B ∧ ConcentricOn O B f)

theorem TaggedPositioningData.leaf_scheme_exists
    (head : HeadPreparationHypotheses O hO power S) (chart : PositioningChartHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    {A : RetainedFieldFamily 𝓜 S 2 k} (C : TaggedPositioningData A)
    (p : SortedAssignment Z (RVVariables A.tags)) :
    ∃ W : PositioningLeafScheme 𝓜 S (RVVariables A.tags),
      W.valid O hO power S A.positioningDomainScheme C.graphScheme p := by
  let T := (𝓜).termGenerated (namedTuple S p)
  let D := A.firstDomain (p .rv)
  let f (x : K) := C.position x (p .rv)
  let U := MixedVariables 1 Empty
  let R := RVVariables A.tags
  let W := SumVariables (SumVariables R U) U
  let V := SumVariables R (SumVariables U U)
  let ren : (s : TCsort) → W s → V s :=
    fun _ => Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  let dom : (s : TCsort) → SumVariables R U s → V s := fun _ => Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have raw := (C.graphScheme_definable.pullback_relabel ren).inter (A.positioningDomainScheme_definable.pullback_relabel dom)
  have graph : DefinableRelation 𝓜 T.carrier (fun a b : fieldAssignment 1 Z =>
      a .vf 0 ∈ D ∧ f (a .vf 0) = b .vf 0) := by
    unfold DefinableRelation
    convert definable_scheme_at_fiber p _ raw using 1
    ext a
    change (_ ∧ _) ↔ C.position (a .vf (.inl 0)) (p .rv) = a .vf (.inr 0) ∧ a .vf (.inl 0) ∈ D
    exact and_comm
  obtain ⟨d,code,data,mvt,branches⟩ := chart.branches A.tags A.finiteTags p D f graph
  obtain ⟨cs,defP,leaves⟩ :=
    positioning_leaves_from_branch_data O hO power T head.minusOne head.minusOne_realizes head.fieldTerms
      head.fieldTerms_realize (chart.saturatedLocalCenters A.tags A.finiteTags p)
      (chart.localImmediate A.tags A.finiteTags p) D f d code data mvt branches he small
  refine positioning_leaf_scheme_of_prepared_charts O hO power S p A.positioningDomainScheme_definable D f
    (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl) _ defP ?_
  intro x hx
  obtain ⟨sub,_,leaf⟩ := leaves x hx
  exact ⟨sub,leaf⟩

end GeneralizedEuler.Section5
