module

public import Section4.PolyhedralGenerators
public import Mathlib.Order.PiLex
import all Section4.ConeBoundary

/-! Triangulation using the original generators. In each coefficient
fiber take the lexicographically least nonnegative representation.
The allowed positive supports depend only on the kernel of the
generator matrix. They give disjoint relatively open simplicial cones. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F E : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup E] [Module F E] {n : ℕ}
local notation "Coeff" => Fin n → F
variable (A : (Fin n → F) →ₗ[F] E)

def IndependentSupport (s : Finset (Fin n)) : Prop :=
  ∀ w : Coeff, (∀ i ∉ s, w i=0) → A w=0 → w=0

def AdmissibleSupport (s : Finset (Fin n)) : Prop :=
  ¬ ∃ w : Coeff, A w=0 ∧ (∀ i ∉ s, 0≤w i) ∧ toLex w < toLex (0 : Coeff)

private theorem negative_direction (w : Coeff) (h : w≠0) :
    toLex w < toLex (0 : Coeff) ∨ toLex (-w) < toLex (0 : Coeff) := by
  have ne : toLex w ≠ toLex (0 : Coeff) := fun e => h (congrArg ofLex e)
  rcases lt_or_gt_of_ne ne with l|⟨i,prev,lt⟩
  · exact Or.inl l
  · exact Or.inr ⟨i,fun j hj => by change -w j=0; have z : 0 = w j := prev j hj; rw [← z,neg_zero],neg_lt_zero.mpr lt⟩

private theorem improving_direction {s : Finset (Fin n)} (bad : ¬IndependentSupport A s) :
    ∃ w : Coeff, A w=0 ∧ (∀ i ∉ s, w i=0) ∧ toLex w < toLex (0 : Coeff) := by
  classical
  unfold IndependentSupport at bad
  push Not at bad
  obtain ⟨w,off,ker,ne⟩ := bad
  obtain neg|neg := negative_direction w ne
  · exact ⟨w,ker,off,neg⟩
  · exact ⟨-w,by simp [ker],fun i h => by simp [off i h],neg⟩

theorem admissible_independent {s : Finset (Fin n)} (h : AdmissibleSupport A s) : IndependentSupport A s := by
  by_contra bad
  obtain ⟨w,ker,off,neg⟩ := improving_direction A bad
  exact h ⟨w,ker,fun i hi => (off i hi).ge,neg⟩

private theorem lex_move (x w : Coeff) {t : F} (ht : 0<t) (neg : toLex w < toLex (0 : Coeff)) :
    toLex (x+t • w) < toLex x := by
  obtain ⟨i,prev,lt⟩ := neg
  refine ⟨i,fun j h => ?_,?_⟩
  · change x j + t*w j = x j
    have z : w j=0 := prev j h
    simp [z]
  · change x i + t*w i < x i
    exact lt_of_sub_pos (by have := mul_neg_of_pos_of_neg ht (show w i<0 from lt); linarith)

private theorem step (x w : Coeff) (positive : ∀ i, 0≤x i) (ker : A w=0)
    (off : ∀ i ∉ live x, 0≤w i) (neg : toLex w < toLex (0 : Coeff)) :
    ∃ t : F, (∀ i, 0≤(x+t • w) i) ∧ A (x+t • w)=A x ∧
      toLex (x+t • w) < toLex x ∧ ∃ i, 0<x i ∧ (x+t • w) i=0 := by
  obtain ⟨t,ht,pos,lost⟩ := first_boundary x w positive
    (fun i hi => off i (by simp [live,hi])) (by obtain ⟨i,_,h⟩ := neg; exact ⟨i,h⟩)
  exact ⟨t,pos,by simp [ker],lex_move x w ht neg,lost⟩

private theorem reduce_to_independent (x : Coeff) (pos : ∀ i, 0≤x i) :
    ∃ y : Coeff, (∀ i, 0≤y i) ∧ A y=A x ∧ toLex y ≤ toLex x ∧ IndependentSupport A (live y) := by
  classical
  generalize measure : (live x).card = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k lower =>
    by_cases basic : IndependentSupport A (live x)
    · exact ⟨x,pos,rfl,le_rfl,basic⟩
    · obtain ⟨w,ker,off,neg⟩ := improving_direction A basic
      obtain ⟨t,pos',same,less,lost⟩ := step A x w pos ker (fun i h => (off i h).ge) neg
      have drop := live_card_drop _ _ pos (fun i hi => by
        have z := off i (by simp [live,hi]); change x i + t*w i=0; simp [hi,z]) lost
      obtain ⟨y,py,ay,le,ind⟩ := lower _ (drop.trans_eq measure) _ pos' rfl
      exact ⟨y,py,ay.trans same,le.trans less.le,ind⟩

omit [IsStrictOrderedRing F] in
private theorem off_live (x : Coeff) (pos : ∀ i, 0≤x i) (i) (h : i ∉ live x) : x i=0 :=
  (pos i).antisymm' (le_of_not_gt (fun lt => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩)))

omit [IsStrictOrderedRing F] in
private theorem basic_unique {x y : Coeff} (px : ∀ i, 0≤x i) (py : ∀ i, 0≤y i)
    (ind : IndependentSupport A (live x)) (s : live x=live y) (eq : A x=A y) : x=y := by
  apply sub_eq_zero.mp
  exact ind _ (fun i h => sub_eq_zero.mpr ((off_live x px i h).trans (off_live y py i (s ▸ h)).symm))
    (by simp [eq])

theorem exists_admissible (x : Coeff) (pos : ∀ i, 0≤x i) :
    ∃ y : Coeff, (∀ i, 0≤y i) ∧ A y=A x ∧ AdmissibleSupport A (live y) := by
  classical
  let solutions := {y : Coeff // (∀ i, 0≤y i) ∧ A y=A x ∧ IndependentSupport A (live y)}
  let _ : Fintype solutions := Fintype.ofInjective (fun y : solutions => live y.val)
    fun y z h => Subtype.ext (basic_unique A y.property.1 z.property.1 y.property.2.2 h (y.property.2.1.trans z.property.2.1.symm))
  obtain ⟨b,pb,eb,_,ib⟩ := reduce_to_independent A x pos
  have ne : (Finset.univ : Finset solutions).Nonempty := ⟨⟨b,pb,eb,ib⟩,Finset.mem_univ _⟩
  obtain ⟨y,_,minimal⟩ := Finset.univ.exists_min_image (fun z : solutions => toLex z.val) ne
  refine ⟨y.val,y.property.1,y.property.2.1,?_⟩
  rintro ⟨w,ker,off,neg⟩
  obtain ⟨t,pt,et,lt,_⟩ := step A _ w y.property.1 ker off neg
  obtain ⟨z,pz,ez,le,iz⟩ := reduce_to_independent A _ pt
  let sol : solutions := ⟨z,pz,ez.trans (et.trans y.property.2.1),iz⟩
  exact (le.trans_lt lt).not_ge (minimal sol (Finset.mem_univ _))

private theorem forbids_smaller (x y : Coeff) (px : ∀ i, 0≤x i) (py : ∀ i, 0≤y i)
    (ad : AdmissibleSupport A (live x)) (eq : A y=A x) : ¬toLex y < toLex x := by
  rintro ⟨i,prev,lt⟩
  apply ad
  exact ⟨y-x,by simp [eq],fun j h => by change 0≤y j-x j; simp [off_live x px j h,py j],
    i,fun j hj => sub_eq_zero.mpr (prev j hj),sub_neg.mpr lt⟩

theorem admissible_unique {x y : Coeff} (px : ∀ i, 0≤x i) (py : ∀ i, 0≤y i)
    (a : AdmissibleSupport A (live x)) (b : AdmissibleSupport A (live y)) (eq : A x=A y) : x=y :=
  congrArg ofLex (le_antisymm (le_of_not_gt (forbids_smaller A x y px py a eq.symm))
    (le_of_not_gt (forbids_smaller A y x py px b eq)))

end GeneralizedEuler.Section4.Polyhedral
