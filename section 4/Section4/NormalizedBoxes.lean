module

public import Section4.BoxFactorMatching
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic

/-! Finite products of scale labels, in canonical nondecreasing order.
Their order is read exactly by the numbers of coordinates above every
threshold, including when there are repeated labels. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
namespace PaddedBox
variable {C R : Type*} [LinearOrder C] [CommMonoid R] {k : ℕ}

abbrev Shape (C : Type*) [LinearOrder C] (k : ℕ) := Fin k →o C

def normalize (x : Fin k → C) : Shape C k := ⟨x ∘ Tuple.sort x,Tuple.monotone_sort x⟩

def tails (x : Fin k → C) (c : C) : ℕ := (Finset.univ.filter (fun i => c < x i)).card

@[simp] theorem normalize_sorted (x : Shape C k) : normalize x = x := by
  apply OrderHom.ext; funext i
  simp [normalize,Tuple.sort_eq_refl_iff_monotone.mpr x.monotone]

theorem tails_permute (x : Fin k → C) (e : Equiv.Perm (Fin k)) :
    tails (x ∘ e) = tails x := by
  funext c
  let perm : {i // c < x (e i)} ≃ {j // c < x j} := e.subtypeEquiv (fun _ => Iff.rfl)
  simpa only [tails,Function.comp_apply,← Fintype.card_subtype] using Fintype.card_congr perm

@[simp] theorem tails_normalize (x : Fin k → C) : tails (normalize x) = tails x :=
  tails_permute x (Tuple.sort x)

theorem tails_le_iff (x y : Shape C k) : tails x ≤ tails y ↔ x ≤ y := by
  constructor
  · intro le i
    let c := y i
    have split (z : Fin k → C) : (Finset.univ.filter (fun j => z j ≤ c)).card + tails z c = k := by
      simpa [tails] using (Finset.univ : Finset (Fin k)).card_filter_add_card_filter_not (fun j => z j ≤ c)
    have iy : i.val < (Finset.univ.filter (fun j => y j ≤ c)).card :=
      (Tuple.lt_card_le_iff_apply_le_of_monotone y.monotone).mpr le_rfl
    apply (Tuple.lt_card_le_iff_apply_le_of_monotone x.monotone).mp
    change i.val < (Finset.univ.filter (fun j => x j ≤ c)).card
    have hxy : tails x c ≤ tails y c := le c
    have sx := split x
    have sy := split y
    omega
  · intro le c
    exact Finset.card_le_card (fun i h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp h).2).trans_le (le i)⟩)

theorem normalize_mono {x y : Fin k → C} (xy : x ≤ y) : normalize x ≤ normalize y := by
  apply (tails_le_iff _ _).mp
  rw [tails_normalize,tails_normalize]
  exact fun c => Finset.card_le_card (fun i h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp h).2).trans_le (xy i)⟩)

theorem weight_normalize (w : C → R) (x : Fin k → C) :
    (∏ i, w (normalize x i)) = ∏ i, w (x i) := Equiv.prod_comp (Tuple.sort x) (fun i => w (x i))

end PaddedBox
end GeneralizedEuler.Section4
