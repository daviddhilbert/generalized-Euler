module

public import Section4.OrderedBoxCuts
import all Section4.NormalizedBoxes
import all Section4.OrderedBoxCuts

/-! A regular box duplicates along a bounded coordinate or along a pair
of rays. Replacing one selected coordinate by a padding point gives its
lower-dimensional face. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open Function Finset
variable {C R : Type*} [LinearOrder C] [OrderBot C] [OrderTop C] [Nontrivial C] [CommSemiring R]
  (w : C → R) {k : ℕ}

def pointShape (k : ℕ) : Shape C k := OrderHom.const _ ⊥

def rayShape (k : ℕ) : Shape C (k+1) := normalize (fun j : Fin (k+1) => if j=0 then (⊤ : C) else ⊥)

def boxDim (s : Shape C k) := tails s ⊥

omit [Nontrivial C] in
private theorem swap_single (i : Fin (k+1)) :
    normalize (fun j => if j=i then (⊤ : C) else ⊥) = rayShape (C := C) k := by
  apply OrderHom.ext; funext j
  let v (t : Fin (k+1)) : C := if t=0 then ⊤ else ⊥
  have swap : (fun j => if j=i then (⊤ : C) else ⊥) = v ∘ Equiv.swap 0 i := by
    funext t
    by_cases h : t=i
    · subst t; simp [v]
    · have hn : Equiv.swap 0 i t ≠ 0 := fun e => h ((Equiv.swap 0 i).injective (e.trans (Equiv.swap_apply_right 0 i).symm))
      simp [v,h,hn]
  rw [swap]
  exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := v) (σ := Equiv.swap 0 i)) j

omit [OrderBot C] [OrderTop C] [Nontrivial C] in
private theorem face_product (s : Shape C k) (i : Fin k) (z : C) :
    boxWeight w (normalize (update s i z)) = w z * ∏ j ∈ univ.erase i, w (s j) := by
  rw [boxWeight,weight_normalize]
  rw [← mul_prod_erase univ (fun j => w (update s i z j)) (mem_univ i),update_self]
  congr 1
  exact prod_congr rfl (fun j hj => by rw [update_of_ne (mem_erase.mp hj).1])

omit [OrderTop C] [Nontrivial C] in
private theorem face_decreases (s : Shape C k) (i : Fin k) (active : ⊥ < s i) :
    boxDim (normalize (update s i ⊥)) < boxDim s := by
  unfold boxDim
  rw [congrFun (tails_normalize (update s i ⊥)) ⊥]
  unfold tails
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨i,?_,?_⟩
  · intro j hj
    obtain ⟨_,good⟩ := mem_filter.mp hj
    by_cases h : j=i
    · simp [h] at good
    · exact mem_filter.mpr ⟨mem_univ _,by simpa [update_of_ne h] using good⟩
  · exact mem_filter.mpr ⟨mem_univ _,active⟩
  · simp

omit [Nontrivial C] in
theorem duplicated_box_face
    (mid : ∀ c : C, c ≠ ⊥ → c ≠ ⊤ → w c = w c + (w c + w ⊥))
    (rays : w ⊤ * w ⊤ = w ⊤ * w ⊤ + (w ⊤ * w ⊤ + w ⊥ * w ⊤))
    (s : Shape C (k+1)) (regular : s ≠ pointShape _ ∧ s ≠ rayShape k) :
    ∃ t : Shape C (k+1), t ≤ s ∧ boxDim t < boxDim s ∧
      boxWeight w s = boxWeight w s + (boxWeight w s + boxWeight w t) := by
  classical
  have active : ∃ i, s i ≠ ⊥ := by
    by_contra! h; exact regular.1 (OrderHom.ext _ _ (funext h))
  suffices step : ∃ i, s i ≠ ⊥ ∧
      w (s i) * (∏ j ∈ univ.erase i, w (s j)) =
        w (s i) * (∏ j ∈ univ.erase i, w (s j)) +
        (w (s i) * (∏ j ∈ univ.erase i, w (s j)) + w ⊥ * ∏ j ∈ univ.erase i, w (s j)) by
    obtain ⟨i,hi,eq⟩ := step
    refine ⟨normalize (update s i ⊥),?_,face_decreases s i (bot_lt_iff_ne_bot.mpr hi),?_⟩
    · rw [← normalize_sorted s]
      apply normalize_mono
      intro j; by_cases e : j=i <;> simp [e,normalize_sorted]
    · rw [face_product,boxWeight,← mul_prod_erase univ (fun j => w (s j)) (mem_univ i)]
      exact eq
  by_cases bounded : ∃ i, s i ≠ ⊥ ∧ s i ≠ ⊤
  · obtain ⟨i,lo,hi⟩ := bounded
    exact ⟨i,lo,by simpa only [add_mul] using congrArg (· * ∏ j ∈ univ.erase i, w (s j)) (mid _ lo hi)⟩
  · obtain ⟨i,hi⟩ := active
    have top {j} (hj : s j ≠ ⊥) : s j = ⊤ := by_contra (fun h => bounded ⟨j,hj,h⟩)
    have second : ∃ j, j ≠ i ∧ s j ≠ ⊥ := by
      by_contra! h
      apply regular.2
      have eq : (s : Fin (k+1) → C) = fun j => if j=i then ⊤ else ⊥ := by
        funext j; by_cases e : j=i
        · subst j; simp [top hi]
        · simp [e,h j e]
      rw [← normalize_sorted s,eq,swap_single]
    obtain ⟨j,ne,hj⟩ := second
    refine ⟨i,hi,?_⟩
    rw [← mul_prod_erase (univ.erase i) (fun m => w (s m)) (mem_erase.mpr ⟨ne,mem_univ j⟩),top hi,top hj]
    simpa only [add_mul,mul_assoc] using congrArg (· * ∏ m ∈ (univ.erase i).erase j, w (s m)) rays

end GeneralizedEuler.Section4.PaddedBox
