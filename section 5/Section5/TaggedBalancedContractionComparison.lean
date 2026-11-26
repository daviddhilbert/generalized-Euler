module

public import Section5.PositionedTwoHeadRefinements

/-! Compare both orders for a family of balanced cells. The two
orders prepare the same unary domain and retain the original tags.
Their only difference is which paradigm they record. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem tagged_balanced_two_head_refinements
    (hyp : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    (A : RetainedFieldFamily 𝓜 S 2 k) (D E' : Set (K × (A.tags → RV0 O)))
    (f g : K → (A.tags → RV0 O) → K)
    (t r : (A.tags → RV0 O) → RV0 O)
    (defF : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 A.tags)) (v : fieldAssignment 1 Z) =>
        f (a .vf 0) (a .rv) = v .vf 0))
    (defG : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 A.tags)) (v : fieldAssignment 1 Z) =>
        g (a .vf 0) (a .rv) = v .vf 0))
    (defT : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (RVVariables A.tags)) (v : SortedAssignment Z (RVVariables (Fin 1))) =>
        t (a .rv) = v .rv 0))
    (left : ∀ x b a, (x,b,a) ∈ A.verticalCarrier ↔ (b 0,a) ∈ E' ∧ rv O (x-g (b 0) a) = r a)
    (right : ∀ x b a, (x,b,a) ∈ (A.permuteVF (Equiv.swap 0 1)).verticalCarrier ↔
      (b 0,a) ∈ D ∧ rv O (x-f (b 0) a) = t a)
    (inverse : ∀ a, Set.BijOn (fun y => g y a) {x | (x,a) ∈ E'} {x | (x,a) ∈ D})
    (sameZero : ∀ a, r a = 0 ↔ t a = 0)
    (defD : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment Z (MixedVariables 1 A.tags) | (a .vf 0,a .rv) ∈ D})
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier A.tags)
      (CenterTestAssignments S.carrier A.tags))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t) :
    ∃ (U : TwoHeadRefinement A) (V : TwoHeadRefinement (A.permuteVF (Equiv.swap 0 1))),
      U.second.target.terminalGradedClass U.enumerate (baseRVZero S) rfl =
      V.second.target.terminalGradedClass V.enumerate (baseRVZero S) rfl := by
  obtain ⟨cs,_,_,stable,_⟩ :=
    unary_deformation O hO power S hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms hyp.fieldTerms_realize
      sat immediate D defD
  let B := A.permuteVF (Equiv.swap 0 1)
  have defId : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 B.tags)) (b : fieldAssignment 1 Z) =>
        a .vf 0 = b .vf 0) := by
    let X := SumVariables (MixedVariables 1 B.tags) (MixedVariables 1 Empty)
    exact SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := X) .vf (.inl 0) (.inr 0)
  have identity (a : B.tags → RV0 O) : Set.BijOn id {x | (x,a) ∈ D} {x | (x,a) ∈ D} :=
    ⟨Set.mapsTo_id _,Set.injOn_id _,Set.surjOn_id _⟩
  obtain ⟨U⟩ := positioned_two_head_refinement O hO power S hyp he small zero hz A E' D g g r
    defG defG left inverse cs stable
  obtain ⟨V⟩ := positioned_two_head_refinement O hO power S hyp he small zero hz B D D f (fun y _ => y) t
    defF defId right identity cs stable
  exact ⟨U.setup,V.setup,U.terminal_class_eq V defT (baseRVZero S) rfl sameZero⟩

end GeneralizedEuler.Section5
