module

public import Section4.RVFamilyOperations
import all Section4.RVFamilyOperations
import all Section4.Scissors

/-! Isomorphism classes of tagged definable sets form a semiring. Its
equality retains a definable bijection on the tagged representatives. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.RVFamily
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
variable (A B C : RVFamily M S)

private theorem coordinateIso {I H : Type} [Finite H] (p : H ≃ I) (U : Set (I → Z .rv)) (D : Set (H → Z .rv))
    (hu : isRVSet M S U) (eq : ∀ y, y ∈ D ↔ y ∘ p.symm ∈ U) : RVDefinablyEquivalent M S.carrier U D := by
  rw [show D = {y | y ∘ p.symm ∈ U} from Set.ext eq]
  exact rv_reindex_equivalent M S p U hu

private theorem samePiece {I : Type} [Finite I] (U : Set (I → Z .rv)) (hu : isRVSet M S U) :
    RVDefinablyEquivalent M S.carrier U U := rv_reindex_equivalent M S (Equiv.refl _) U hu

private theorem append_comm : (A.append B).Iso (B.append A) := by
  apply iso_retag _ _ (Equiv.sumComm A.Tag B.Tag)
  rintro (i|j)
  exacts [samePiece _ (A.definable i),samePiece _ (B.definable j)]

private theorem append_assoc : ((A.append B).append C).Iso (A.append (B.append C)) := by
  apply iso_retag _ _ (Equiv.sumAssoc A.Tag B.Tag C.Tag)
  rintro ((i|j)|k)
  exacts [samePiece _ (A.definable i),samePiece _ (B.definable j),samePiece _ (C.definable k)]

private theorem empty_append : ((emptyFamily M S).append A).Iso A := by
  apply iso_retag _ _ (Equiv.emptySum Empty A.Tag)
  rintro (i|j)
  · exact i.elim
  · exact samePiece _ (A.definable j)

private theorem product_comm : (A.product B).Iso (B.product A) := by
  apply iso_retag _ _ (Equiv.prodComm A.Tag B.Tag)
  rintro ⟨i,j⟩
  apply coordinateIso (Equiv.sumComm (B.Coord j) (A.Coord i)) _ _ ((A.product B).definable _)
  intro y; exact and_comm

private theorem product_assoc : ((A.product B).product C).Iso (A.product (B.product C)) := by
  apply iso_retag _ _ (Equiv.prodAssoc A.Tag B.Tag C.Tag)
  rintro ⟨⟨i,j⟩,k⟩
  apply coordinateIso (Equiv.sumAssoc (A.Coord i) (B.Coord j) (C.Coord k)).symm _ _ (((A.product B).product C).definable _)
  intro y; exact and_assoc.symm

private theorem empty_product : ((emptyFamily M S).product A).Iso (emptyFamily M S) := by
  apply iso_retag _ _ (Equiv.emptyProd A.Tag)
  rintro ⟨i,_⟩; exact i.elim

private theorem unit_product : ((unitFamily M S).product A).Iso A := by
  apply iso_retag _ _ (Equiv.punitProd A.Tag)
  rintro ⟨_,j⟩
  apply coordinateIso (Equiv.emptySum Empty (A.Coord j)).symm _ _ (((unitFamily M S).product A).definable _)
  intro y; exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩

private theorem product_append : (A.product (B.append C)).Iso ((A.product B).append (A.product C)) := by
  apply iso_retag _ _ (Equiv.prodSumDistrib A.Tag B.Tag C.Tag)
  rintro ⟨i,j|k⟩
  exacts [samePiece _ ((A.product B).definable (i,j)),samePiece _ ((A.product C).definable (i,k))]

@[expose] def isoSetoid (M : SortedStructure L F Z) (S : SortedSubstructure M) : Setoid (RVFamily M S) where
  r := Iso
  iseqv := ⟨iso_refl,fun h => iso_symm _ _ h,fun h h' => iso_trans _ _ _ h h'⟩

abbrev Classes (M : SortedStructure L F Z) (S : SortedSubstructure M) := Quotient (isoSetoid M S)

@[expose] def cls (A : RVFamily M S) : Classes M S := Quotient.mk _ A

theorem cls_eq_iff : cls A = cls B ↔ A.Iso B := Quotient.eq

instance : Zero (Classes M S) := ⟨cls (emptyFamily M S)⟩
instance : One (Classes M S) := ⟨cls (unitFamily M S)⟩
instance : Add (Classes M S) := ⟨Quotient.map₂ (sa := isoSetoid M S) (sb := isoSetoid M S) (sc := isoSetoid M S) append (by intro a b h c d k; exact append_congr a b c d h k)⟩
instance : Mul (Classes M S) := ⟨Quotient.map₂ (sa := isoSetoid M S) (sb := isoSetoid M S) (sc := isoSetoid M S) product (by intro a b h c d k; exact product_congr a b c d h k)⟩

theorem cls_empty : cls (emptyFamily M S) = 0 := rfl
theorem cls_unit : cls (unitFamily M S) = 1 := rfl

theorem cls_append : cls (A.append B) = cls A + cls B := rfl
theorem cls_product : cls (A.product B) = cls A * cls B := rfl

instance : CommSemiring (Classes M S) where
  add_comm := by rintro ⟨a⟩ ⟨b⟩; exact Quotient.sound (append_comm a b)
  add_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact Quotient.sound (append_assoc a b c)
  zero_add := by rintro ⟨a⟩; exact Quotient.sound (empty_append a)
  add_zero := by rintro ⟨a⟩; exact Quotient.sound (iso_trans _ _ _ (append_comm _ _) (empty_append a))
  mul_comm := by rintro ⟨a⟩ ⟨b⟩; exact Quotient.sound (product_comm a b)
  mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact Quotient.sound (product_assoc a b c)
  one_mul := by rintro ⟨a⟩; exact Quotient.sound (unit_product a)
  mul_one := by rintro ⟨a⟩; exact Quotient.sound (iso_trans _ _ _ (product_comm _ _) (unit_product a))
  zero_mul := by rintro ⟨a⟩; exact Quotient.sound (empty_product a)
  mul_zero := by rintro ⟨a⟩; exact Quotient.sound (iso_trans _ _ _ (product_comm _ _) (empty_product a))
  left_distrib := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact Quotient.sound (product_append a b c)
  right_distrib := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact Quotient.sound (iso_trans _ _ _ (product_comm _ _) (iso_trans _ _ _ (product_append c a b)
      (append_congr _ _ _ _ (product_comm _ _) (product_comm _ _))))
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl

end GeneralizedEuler.Section4.RVFamily
