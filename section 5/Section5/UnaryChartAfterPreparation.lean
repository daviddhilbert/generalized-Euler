module

public import Section5.UnaryChainFibers
public import Mathlib.Tactic.Abel

/-! Restrict an old disc-to-disc chart to the preimage of a prepared
label fiber, then translate the source coordinate of the chart. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {cert : ∀ I : Type, RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)) → Prop}
  {I J : Type} {T : Type*} {A : Set (K × (I → RV0 O))} {A' : Set (K × (J → RV0 O))} {B : Set (K × T)}
  (s : A ≃ A') (e : A ≃ B)

theorem unary_charts_after_preparation (chain : EncodedFocusChain O cert A A' s)
    (full : IsUnaryPullback O A')
    (old : ∀ x : A, ∃ (D E : Set K) (f g : K → K), DiscToDiscOn O D E f g ∧
      ∀ y : A, unaryMixedLabel O (s y).val = unaryMixedLabel O (s x).val →
        y.val.1 ∈ D ∧ f y.val.1 = (e y).val.1) :
    UnaryDiscCharts O (s.symm.trans e) := by
  intro u nz
  obtain ⟨x,rfl⟩ := s.surjective u
  obtain ⟨D,E,f,g,chart,agree⟩ := old x
  let r := O.valuation (s x).val.1
  let C := openDisc O x.val.1 r
  let d := x.val.1 - (s x).val.1
  have hr : r ≠ 0 := (map_ne_zero _).2 nz
  have inv := chain.label_fiber_openDisc O full x nz
  have sub : C ⊆ D := by
    intro w hw
    change w ∈ openDisc O x.val.1 (O.valuation (s x).val.1) at hw
    have src : w ∈ {u | ∃ y : A, y.val.1 = u ∧ unaryMixedLabel O (s y).val = unaryMixedLabel O (s x).val} :=
      inv.symm ▸ hw
    obtain ⟨y,hy,h⟩ := src
    exact hy ▸ (agree y h).1
  have restr := discToDisc_restrict_image O chart sub
  obtain ⟨b,r',hr',image⟩ := restr.2.2.1 x.val.1 r hr Set.Subset.rfl
  have form : {y | y + d ∈ C} = openDisc O (s x).val.1 r := by
    ext y
    change O.valuation (y + d - x.val.1) < r ↔ O.valuation (y - (s x).val.1) < r
    have eq : y + d - x.val.1 = y - (s x).val.1 := by dsimp [d]; abel
    rw [eq]
  have shifted := discToDisc_translated O restr d 0
  simp only [form,add_zero,sub_zero] at shifted
  change DiscToDiscOn O (openDisc O (s x).val.1 r) (f '' C) (fun y => f (y+d)) (fun y => g y-d) at shifted
  change f '' C = openDisc O b r' at image
  rw [image] at shifted
  refine ⟨b,r',fun y => f (y+d),fun y => g y-d,hr',shifted,?_,?_⟩
  · intro v same
    obtain ⟨y,rfl⟩ := s.surjective v
    have diff := (chain.on_label_fiber O x y same.symm).2
    have field : (s y).val.1+d = y.val.1 := by
      change (s y).val.1 + (x.val.1 - (s x).val.1) = y.val.1
      calc
        _ = ((s y).val.1-(s x).val.1) + x.val.1 := by abel
        _ = y.val.1 := by rw [diff,sub_add_cancel]
    change f ((s y).val.1+d) = ((s.symm.trans e) (s y)).val.1
    rw [field]
    have eq : (s.symm.trans e) (s y) = e y := by
      change e (s.symm (s y)) = e y
      rw [s.symm_apply_apply]
    rw [eq]
    exact (agree y same).2
  · intro y hy
    have lab : unaryMixedLabel O (y,(s x).val.2) = unaryMixedLabel O (s x).val :=
      Prod.ext ((rv_eq_rv_iff_valuation O nz).2 hy) rfl
    exact ⟨⟨_,full (s x).val (s x).property _ lab.symm⟩,rfl,lab⟩

end GeneralizedEuler.Section5
