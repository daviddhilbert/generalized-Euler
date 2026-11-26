module

public import Section5.SpecialSuccessor

/-! Fixed-base graphs for transitions between prepared prefixes. Each
prefix can be defined by its action before the initial tail map is lifted. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder UnaryPreparation

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n : ℕ} {I C R Q : Type}

theorem PointMapDefinable.prefixTransition [Finite I]
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) R}
    {g : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) Q}
    (hf : PointMapDefinable M S f) (hg : PointMapDefinable M S g) :
    DefinableRelation M S.carrier
      (fun a : SortedAssignment (CanonicalSort O) (MixedVariables n R) =>
        fun b : SortedAssignment (CanonicalSort O) (MixedVariables n Q) =>
          ∃ p, f p = mixedTuple a ∧ g p = mixedTuple b) := by
  unfold PointMapDefinable at hf hg
  exact (DefinableRelation.transport hf hg).congr fun a b => by
    constructor
    · rintro ⟨x,hx,hy⟩
      exact ⟨mixedTuple x,hx,hy⟩
    · rintro ⟨p,hp,hq⟩
      obtain ⟨x,rfl⟩ := mixedTuple_surjective p
      exact ⟨x,hp,hq⟩

theorem transportedHeadPrefix_definable [Finite I]
    (center : (Fin n → K) → Option C → K)
    (first : PreparedMap M S (CenterDifferenceTests (O := O) (I := I) center))
    (cs : List C)
    (hhead : PointMapDefinable M S (headMap (I := I)
      (fun b => centerPreparation (O := O) (center b) cs))) :
    PointMapDefinable M S (headFamilyMap (transportedCenters center first) cs ∘ liftTailMap first.map) := by
  have he : headFamilyMap (transportedCenters center first) cs ∘ liftTailMap first.map =
      liftTailMap (mapKeepingTags first.map) ∘
        headMap (fun b => centerPreparation (O := O) (center b) cs) :=
    funext (transportedHeadMap center first cs)
  rw [he]
  exact hhead.comp first.definable.keepTags.liftTail

end GeneralizedEuler.Section5
