module

public import Section4.BoxPresentations
public import Mathlib.Order.WithBot
import all Section4.IntervalScales

/-! Choose one old representative of each bounded scale occurring in a
finite pair of presentations. Adjoin a bottom padding symbol and a top
ray. No parameter is added to the base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open Set FirstOrder
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup V] [LinearOrder V]
  [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V] (G : Submodule F V)

/-- The displayed finite chain covers every requested width and includes
an interior filler for cuts of a ray whose point is extracted. -/
theorem exists_finite_alphabet (D : Finset V) (old : ∀ x ∈ D, x ∈ G) (pos : ∀ x ∈ D, 0 < x)
    (nonempty : D.Nonempty) :
    ∃ (n : ℕ) (B : Alphabet G (Fin (n+3))), ∀ x ∈ D, ∃ c : Fin (n+3),
      c ≠ ⊥ ∧ c ≠ ⊤ ∧ scaleSpace F (B.width c) = scaleSpace F x := by
  classical
  let scales := D.image (scaleSpace F)
  have repr (H : scales) : ∃ x ∈ D, scaleSpace F x = H.val := Finset.mem_image.mp H.property
  choose pick mem image using repr
  let widths := Finset.univ.image pick
  have inD (x : V) (hx : x ∈ widths) : x ∈ D := by
    obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hx; exact mem H
  have unique (x y : widths) (same : scaleSpace F x.val = scaleSpace F y.val) : x = y := by
    obtain ⟨H,_,e⟩ := Finset.mem_image.mp x.property
    obtain ⟨J,_,f⟩ := Finset.mem_image.mp y.property
    rw [← e,← f,image,image] at same
    exact Subtype.ext (e.symm.trans ((congrArg pick (Subtype.ext same)).trans f))
  obtain ⟨x,hx⟩ := nonempty
  let h : scales := ⟨scaleSpace F x,Finset.mem_image_of_mem _ hx⟩
  have live : widths.Nonempty := ⟨pick h,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let n := widths.card - 1
  have size : widths.card = n+1 := by have := Finset.card_pos.mpr live; dsimp [n]; omega
  let order : Fin (n+1) ≃o widths := widths.orderIsoOfFin size
  let idx (c : Fin (n+3)) (lo : c ≠ ⊥) (hi : c ≠ ⊤) : Fin (n+1) := ⟨c.val - 1,by
    have ctop : c.val < n+2 := by
      have := (lt_top_iff_ne_top.mpr hi)
      exact this
    have cp : 0 < c.val := (show (⊥ : Fin (n+3)) < c from bot_lt_iff_ne_bot.mpr lo)
    omega⟩
  let index (j : Fin (n+1)) : Fin (n+3) := ⟨j.val+1,by omega⟩
  have low (j) : index j ≠ ⊥ := by intro e; have := congrArg Fin.val e; change j.val+1=0 at this; omega
  have high (j) : index j ≠ ⊤ := by intro e; have := congrArg Fin.val e; change j.val+1=n+2 at this; omega
  let width (c : Fin (n+3)) : V := if h : c ≠ ⊥ ∧ c ≠ ⊤ then (order (idx c h.1 h.2)).val else 0
  have inside {c} (lo : c ≠ ⊥) (hi : c ≠ ⊤) : width c = (order (idx c lo hi)).val := by simp [width,lo,hi]
  have root (j) : width (index j) = (order j).val := by rw [inside (low j) (high j)]; rfl
  let B : Alphabet G (Fin (n+3)) := {
    width := width
    old := fun c => by unfold width; split; exact old _ (inD _ (order _).property); exact G.zero_mem
    positive := fun c lo hi => by rw [inside lo hi]; exact pos _ (inD _ (order _).property)
    increasing := by
      intro a b lo hi lt
      have al := (lt.trans_le le_top).ne
      have bl := (bot_le.trans_lt lt).ne'
      rw [inside lo al,inside bl hi]
      have ij : idx a lo al < idx b bl hi := by
        have az : 0 < a.val := (show (⊥ : Fin (n+3)) < a from bot_lt_iff_ne_bot.mpr lo)
        change a.val-1 < b.val-1; change a.val < b.val at lt; omega
      have ab := order.strictMono ij
      let u := order (idx a lo al)
      let v := order (idx b bl hi)
      have incl : scaleSpace F u.val ≤ scaleSpace F v.val :=
        scaleSpace_mono F (scaleSpace_interval F (pos u.val (inD _ u.property)).le ab.le)
      intro back
      exact ab.ne (unique u v (le_antisymm incl (scaleSpace_mono F back)))
    filler := index 0
    interior := ⟨low 0,high 0⟩ }
  refine ⟨n,B,?_⟩
  intro d hd
  let H : scales := ⟨scaleSpace F d,Finset.mem_image_of_mem _ hd⟩
  let w : widths := ⟨pick H,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let j := order.symm w
  refine ⟨index j,low j,high j,?_⟩
  change scaleSpace F (width (index j)) = scaleSpace F d
  rw [root,show order j = w from order.apply_symm_apply _]; exact image H

end GeneralizedEuler.Section4.PaddedBox
