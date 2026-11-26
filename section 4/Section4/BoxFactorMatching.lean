module

public import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Interval.Finset.Basic

/-! Cumulative scale counts give an actual matching of box factors.
The ordered labels can include the padding point and a largest ray. -/
public section
namespace GeneralizedEuler.Section4
variable {I J C : Type*} [Fintype I] [Fintype J] [LinearOrder C]

theorem match_box_factors_of_tail_counts (a : I → C) (b : J → C)
    (counts : ∀ i, (Finset.univ.filter (fun k => a i ≤ a k)).card ≤
      (Finset.univ.filter (fun j => a i ≤ b j)).card) :
    ∃ f : I ↪ J, ∀ i, a i ≤ b (f i) := by
  classical
  obtain ⟨f,hf,above⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective (fun i j => a i ≤ b j)).mp (by
    intro s
    rcases s.eq_empty_or_nonempty with rfl|nonempty
    · exact Nat.zero_le _
    · obtain ⟨i,hi,minimum⟩ := s.exists_min_image a nonempty
      calc
        s.card ≤ (Finset.univ.filter (fun k => a i ≤ a k)).card :=
          Finset.card_le_card (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _,minimum k hk⟩)
        _ ≤ _ := counts i
        _ ≤ _ := Finset.card_le_card (fun j hj =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,(Finset.mem_filter.mp hj).2⟩))
  exact ⟨⟨f,hf⟩,above⟩

end GeneralizedEuler.Section4
