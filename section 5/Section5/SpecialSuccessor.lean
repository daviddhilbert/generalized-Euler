module

public import Section5.SpecialHeadPreparation

/-! Replay the sequence with the difference-preparing tail map first.
Its output labels determine the loci of all subsequent head steps. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n : ℕ} {I C : Type}

variable (center : (Fin n → K) → Option C → K)

abbrev CenterDifferenceTests :=
  {p : PreparationPoint O (Fin n) I × (Option C × Option C → RV0 O) |
    ∀ i j, p.2 (i,j) = rv O (center p.1.1 i - center p.1.1 j)}

variable (first : PreparedMap M S (CenterDifferenceTests (O := O) (I := I) center))

/-- The first tail map transports the functions used as centers.
Outside its image the auxiliary definition is zero. -/
def transportedCenters (y : PreparationPoint O (Fin n) first.tags) (i : Option C) : K := by
  classical
  exact if hy : y ∈ Set.range first.map then center hy.choose.1 i else 0

theorem transportedCenters_at_image (b : PreparationPoint O (Fin n) I) :
    transportedCenters center first (first.map b) = center b.1 := by
  classical
  funext i
  have hb : first.map b ∈ Set.range first.map := Set.mem_range_self b
  have hchosen : hb.choose = b := first.injective hb.choose_spec
  simp only [transportedCenters, dite_eq_left hb, hchosen]

theorem transportedCenters_zero (hzero : ∀ b, center b none = 0)
    (y : PreparationPoint O (Fin n) first.tags) : transportedCenters center first y none = 0 := by
  classical
  unfold transportedCenters
  split
  · exact hzero _
  · rfl

theorem transportedCenters_stable (y z : PreparationPoint O (Fin n) first.tags)
    (he : preparationLabel y = preparationLabel z) (i j : Option C) :
    rv O (transportedCenters center first y i - transportedCenters center first y j) =
      rv O (transportedCenters center first z i - transportedCenters center first z j) := by
  classical
  by_cases hy : y ∈ Set.range first.map
  · have hz := (first.whole _ _ he).1 hy
    obtain ⟨a,rfl⟩ := hy
    obtain ⟨b,rfl⟩ := hz
    let d (p : Option C × Option C) := rv O (center a.1 p.1 - center a.1 p.2)
    have ha : (a,d) ∈ CenterDifferenceTests center := fun _ _ => rfl
    have h := (first.tests a b he d).1 ha i j
    rw [transportedCenters_at_image, transportedCenters_at_image]
    exact h
  · have hz := (not_congr (first.whole _ _ he)).1 hy
    simp [transportedCenters, hy, hz]

/-- Applying the head map in the first prepared tail coordinates
commutes with transporting its original tail and history. -/
theorem transportedHeadMap (cs : List C) (p : PreparationPoint O (Fin (n+1)) I) :
    headFamilyMap (transportedCenters center first) cs (liftTailMap first.map p) =
      liftTailMap (mapKeepingTags first.map)
        (headMap (fun b => centerPreparation (O := O) (center b) cs) p) := by
  unfold headFamilyMap
  have he : tailPoint (liftTailMap first.map p) = first.map (tailPoint p) := rfl
  rw [he]
  dsimp only
  rw [transportedCenters_at_image]
  rfl

/-- The map computed in the successor step has a special chain. The
center-difference test is used here to verify the loci of the head steps. -/
theorem specialSuccessor (cs : List C) (hzero : ∀ b, center b none = 0)
    (firstSpecial : SpecialChain O (Fin n) Set.univ first.map)
    {R : Type}
    (last : PreparationPoint O (Fin n) (first.tags ⊕ HistoryIndex cs.length) →
      PreparationPoint O (Fin n) R)
    (lastSpecial : SpecialChain O (Fin n) Set.univ last) :
    SpecialChain O (Fin (n+1)) Set.univ
      (liftTailMap last ∘ liftTailMap (mapKeepingTags first.map) ∘
        headMap (fun b => centerPreparation (O := O) (center b) cs)) := by
  have hfirst : SpecialChain O (Fin (n+1)) Set.univ (liftTailMap first.map) := by
    simpa only [Set.preimage_univ] using firstSpecial.liftTail
  have hhead := specialHeadFamily (transportedCenters center first)
    (transportedCenters_zero center first hzero) (transportedCenters_stable center first) cs
    (liftTailMap first.map '' Set.univ)
  have hlast : SpecialChain O (Fin (n+1)) Set.univ (liftTailMap last) := by
    simpa only [Set.preimage_univ] using lastSpecial.liftTail
  have hmiddle := SpecialChain.append hfirst hhead
  have hcombined := SpecialChain.append hmiddle (hlast.restrict (Set.subset_univ _))
  refine hcombined.congr ?_
  intro p _
  exact congrArg (liftTailMap last) (transportedHeadMap center first cs p)

end GeneralizedEuler.Section5
