module

public import Section4.BoxScaleProfiles
public import Section4.IntervalScaleBijection
import all Section4.IntervalScales
import all Section4.ValueBoxes

/-! Differences of neighboring cutoff counts recover the multiplicity of
every width scale. Pair the resulting fibers to match individual factors. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Set
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

theorem width_scale_total {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    scaleSpace F a ≤ scaleSpace F b ∨ scaleSpace F b ≤ scaleSpace F a := by
  rcases le_total a b with h|h
  · exact Or.inl (scaleSpace_mono F (scaleSpace_interval F ha h))
  · exact Or.inr (scaleSpace_mono F (scaleSpace_interval F hb h))

variable {I J : Type*} [Fintype I] [Fintype J]

def widthTail (f : I → V) (t : V) : ℕ := Nat.card {i // f i ∉ scaleSpace F t}

private theorem split_tail (f : I → V) (p t : V) (above : ∀ i, f i ∉ scaleSpace F p ↔ t ∈ scaleSpace F (f i))
    (positive : ∀ i, 0 ≤ f i) (ht : 0 ≤ t) :
    widthTail (F := F) f p = widthTail (F := F) f t + Nat.card {i // scaleSpace F (f i) = scaleSpace F t} := by
  classical
  simp only [widthTail,Nat.card_eq_fintype_card,Fintype.card_subtype]
  let s := Finset.univ.filter (fun i => f i ∉ scaleSpace F p)
  have cut := s.card_filter_add_card_filter_not (fun i => f i ∉ scaleSpace F t)
  have small (i) : f i ∉ scaleSpace F t → t ∈ scaleSpace F (f i) := by
    intro h
    rcases width_scale_total (F := F) (positive i) ht with h₁|h₂
    · exact (h (h₁ (self_mem_scaleSpace F _))).elim
    · exact h₂ (self_mem_scaleSpace F _)
  have left : s.filter (fun i => f i ∉ scaleSpace F t) = Finset.univ.filter (fun i => f i ∉ scaleSpace F t) := by
    ext i; simp [s,above,and_iff_right_of_imp (small i)]
  have right : s.filter (fun i => ¬ f i ∉ scaleSpace F t) = Finset.univ.filter (fun i => scaleSpace F (f i) = scaleSpace F t) := by
    ext i; simp only [s,Finset.mem_filter,Finset.mem_univ,true_and,not_not]
    rw [above]; simp only [← scaleSpace_le_iff]
    exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩
  rw [left,right] at cut
  exact cut.symm

theorem pair_widths_of_counts (G : Submodule F V) (a : I → V) (b : J → V)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (ba : ∀ i, a i ∈ G) (bb : ∀ j, b j ∈ G)
    (eq : ∀ t ∈ G, 0 ≤ t → widthTail (F := F) a t = widthTail (F := F) b t) :
    ∃ e : I ≃ J, ∀ i, scaleSpace F (a i) = scaleSpace F (b (e i)) := by
  classical
  let widths := Sum.elim a b
  have pos : ∀ l, 0 < widths l := by rintro (i|j); exact ha i; exact hb j
  have base : ∀ l, widths l ∈ G := by rintro (i|j); exact ba i; exact bb j
  let keyA i := scaleSpace F (a i)
  let keyB j := scaleSpace F (b j)
  have fibers (H : Submodule F V) : Nat.card {i // keyA i = H} = Nat.card {j // keyB j = H} := by
    by_cases present : ∃ l, scaleSpace F (widths l) = H
    · obtain ⟨l,rfl⟩ := present
      let t := widths l
      obtain ⟨p,pg,w,nested⟩ := preceding_box_scale G widths base (fun x => (pos x).le) (.bounded t)
        (fun x e => (BoxSide.bounded.inj e) ▸ pos l)
      have out := w t rfl
      have q (i) : widths i ∉ scaleSpace F p ↔ t ∈ scaleSpace F (widths i) := by
        constructor
        · intro hi; by_contra miss
          exact hi ((nested i miss) (self_mem_scaleSpace F _))
        · intro h small; exact out (scaleSpace_mono F small h)
      have ca := split_tail a p t (fun i => q (.inl i)) (fun i => (ha i).le) (pos l).le
      have cb := split_tail b p t (fun j => q (.inr j)) (fun j => (hb j).le) (pos l).le
      have e0 : widthTail (F := F) a p = widthTail (F := F) b p := by
        by_cases hp : 0 ≤ p
        · exact eq p pg hp
        · have same : scaleSpace F p = scaleSpace F (-p) := by
            apply le_antisymm <;> apply scaleSpace_mono <;> exact ⟨1,zero_le_one,by simp⟩
          simpa [widthTail,same] using eq (-p) (G.neg_mem pg) (neg_nonneg.mpr (le_of_not_ge hp))
      have e1 := eq t (base l) (pos l).le
      rw [ca,cb,e1] at e0
      exact Nat.add_left_cancel e0
    · have emptyA : IsEmpty {i // keyA i = H} := ⟨fun i => present ⟨.inl i.val,i.property⟩⟩
      have emptyB : IsEmpty {j // keyB j = H} := ⟨fun j => present ⟨.inr j.val,j.property⟩⟩
      simp
  let e (H) := Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using fibers H)
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

end GeneralizedEuler.Section4
