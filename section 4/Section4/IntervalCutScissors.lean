module

public import Section4.BoundedIntervalScissors
import all Section4.BoundedIntervalScissors

/-! Cutting a positive interval at a base point, before groupification.
The point and the right interval are represented by translations of
the zero point and the interval starting at zero. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject
variable {F V : Type*} [Field F] [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V]
  {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)

include lang in
theorem bounded_interval_scissors (a b : V) (oa : a ∈ G) (ha : 0 < a) (hb : 0 < b)
    (da : (G : Set V).Definable J (intervalPiece a)) (db : (G : Set V).Definable J (intervalPiece b))
    (ds : (G : Set V).Definable J (intervalPiece (a+b))) (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V))) :
    pieceClass _ ds = pieceClass _ da + (pieceClass _ dp + pieceClass _ db) := by
  let tr (x : Fin 1 → V) i := x i + a
  let pt := tr '' ({0} : Set (Fin 1 → V))
  let right := tr '' intervalPiece b
  have pm (x : Fin 1 → V) : x ∈ pt ↔ x 0 = a := by
    constructor
    · rintro ⟨y,hy,rfl⟩; rw [Set.mem_singleton_iff.mp hy]; simp [tr]
    · intro h; exact ⟨0,rfl,funext fun i => by simpa [tr,Subsingleton.elim i 0] using h.symm⟩
  have rm (x : Fin 1 → V) : x ∈ right ↔ a < x 0 ∧ x 0 < a+b := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      change 0 < y 0 ∧ y 0 < b at hy
      change a < y 0 + a ∧ y 0 + a < a+b
      exact ⟨lt_add_of_pos_left _ hy.1,(add_lt_add_left hy.2 a).trans_eq (add_comm b a)⟩
    · rintro ⟨lo,hi⟩
      refine ⟨fun i => x i-a,⟨sub_pos.mpr lo,?_⟩,funext fun i => sub_add_cancel _ _⟩
      exact sub_lt_iff_lt_add.mpr (hi.trans_eq (add_comm a b))
  obtain ⟨hpt,eqpt⟩ := translate_piece G lang _ dp a oa
  obtain ⟨hr,eqr⟩ := translate_piece G lang _ db a oa
  have cut : intervalPiece (a+b) = intervalPiece a ∪ (pt ∪ right) := by
    ext x; simp only [Set.mem_union,pm,rm]
    change 0 < x 0 ∧ x 0 < a+b ↔ (0 < x 0 ∧ x 0 < a) ∨ x 0 = a ∨ a < x 0 ∧ x 0 < a+b
    grind
  have sep : Disjoint pt right := Set.disjoint_left.mpr fun x h₁ h₂ =>
    ((rm x).mp h₂).1.ne' ((pm x).mp h₁)
  have sep' : Disjoint (intervalPiece a) (pt ∪ right) := by
    apply Set.disjoint_left.mpr; rintro x h (h'|h')
    · exact h.2.ne ((pm x).mp h')
    · exact h.2.not_gt ((rm x).mp h').1
  calc pieceClass _ ds = pieceClass _ (da.union (hpt.union hr)) := by congr 1
       _ = _ := by rw [pieceClass_cut da (hpt.union hr) sep',pieceClass_cut hpt hr sep,eqpt,eqr]

end GeneralizedEuler.Section4
