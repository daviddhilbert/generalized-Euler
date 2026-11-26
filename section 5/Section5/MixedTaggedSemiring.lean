module

public import Section5.MixedTaggedOperations
public import Section5.MixedRelabeling

/-! The classes of finite tagged mixed families form a semiring.
Its equality is exactly fixed-base tagged definable isomorphism. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.MixedTaggedFamily

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} (A B C : MixedTaggedFamily M S)

private theorem coordinateIso {U V : TCsort → Type} [∀ s, Finite (V s)]
    (p : ∀ s, V s ≃ U s) {P : Set (SortedAssignment X U)} {Q : Set (SortedAssignment X V)}
    (defP : SortedDefinableOver M S.carrier P) (h : ∀ y, y ∈ Q ↔ (fun s => y s ∘ (p s).symm) ∈ P) :
    MixedDefinablyEquivalent M S P Q :=
  (Set.ext h).symm ▸ mixed_reindex_equivalent p P defP

private theorem append_comm : (A.append B).Iso (B.append A) := by
  apply iso_retag _ _ (Equiv.sumComm A.Tag B.Tag)
  rintro (i|j)
  · exact MixedDefinablyEquivalent.refl (V := A.coordinates i) (A.definable i)
  · exact MixedDefinablyEquivalent.refl (V := B.coordinates j) (B.definable j)

private theorem append_assoc : ((A.append B).append C).Iso (A.append (B.append C)) := by
  apply iso_retag _ _ (Equiv.sumAssoc A.Tag B.Tag C.Tag)
  rintro ((i|j)|k)
  · exact MixedDefinablyEquivalent.refl (V := A.coordinates i) (A.definable i)
  · exact MixedDefinablyEquivalent.refl (V := B.coordinates j) (B.definable j)
  · exact MixedDefinablyEquivalent.refl (V := C.coordinates k) (C.definable k)

private theorem empty_append : ((emptyFamily M S).append A).Iso A := by
  apply iso_retag _ _ (Equiv.emptySum Empty A.Tag)
  rintro (i|j)
  · exact i.elim
  · exact MixedDefinablyEquivalent.refl (V := A.coordinates j) (A.definable j)

private theorem product_comm : (A.product B).Iso (B.product A) := by
  apply iso_retag _ _ (Equiv.prodComm A.Tag B.Tag)
  rintro ⟨i,j⟩
  apply coordinateIso (fun s => Equiv.sumComm (B.coordinates j s) (A.coordinates i s))
    ((A.product B).definable (i,j))
  intro y
  exact and_comm

private theorem product_assoc : ((A.product B).product C).Iso (A.product (B.product C)) := by
  apply iso_retag _ _ (Equiv.prodAssoc A.Tag B.Tag C.Tag)
  rintro ⟨⟨i,j⟩,k⟩
  apply coordinateIso (fun s => (Equiv.sumAssoc (A.coordinates i s) (B.coordinates j s) (C.coordinates k s)).symm)
    (((A.product B).product C).definable ((i,j),k))
  intro y
  exact and_assoc.symm

private theorem empty_product : ((emptyFamily M S).product A).Iso (emptyFamily M S) := by
  apply iso_retag _ _ (Equiv.emptyProd A.Tag)
  rintro ⟨i,_⟩
  exact i.elim

private theorem unit_product : ((unitFamily M S).product A).Iso A := by
  apply iso_retag _ _ (Equiv.punitProd A.Tag)
  rintro ⟨_,j⟩
  apply coordinateIso (fun s => (Equiv.emptySum Empty (A.coordinates j s)).symm)
    (((unitFamily M S).product A).definable ((),j))
  intro y
  exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩

private theorem product_append : (A.product (B.append C)).Iso ((A.product B).append (A.product C)) := by
  apply iso_retag _ _ (Equiv.prodSumDistrib A.Tag B.Tag C.Tag)
  rintro ⟨i,j|k⟩
  · let : Finite ((A.product B).coordinates (i,j) .vf) := (A.product B).finiteCoordinates (i,j) .vf
    let : Finite ((A.product B).coordinates (i,j) .rv) := (A.product B).finiteCoordinates (i,j) .rv
    exact MixedDefinablyEquivalent.refl (V := (A.product B).coordinates (i,j)) ((A.product B).definable (i,j))
  · let : Finite ((A.product C).coordinates (i,k) .vf) := (A.product C).finiteCoordinates (i,k) .vf
    let : Finite ((A.product C).coordinates (i,k) .rv) := (A.product C).finiteCoordinates (i,k) .rv
    exact MixedDefinablyEquivalent.refl (V := (A.product C).coordinates (i,k)) ((A.product C).definable (i,k))

@[expose] def isoSetoid (M : SortedStructure L E X) (S : SortedSubstructure M) : Setoid (MixedTaggedFamily M S) where
  r := Iso
  iseqv := ⟨iso_refl,fun h => iso_symm _ _ h,fun h h' => iso_trans _ _ _ h h'⟩

abbrev Classes (M : SortedStructure L E X) (S : SortedSubstructure M) := Quotient (isoSetoid M S)

@[expose] def cls (A : MixedTaggedFamily M S) : Classes M S := Quotient.mk _ A

theorem cls_eq_iff : cls A = cls B ↔ A.Iso B := Quotient.eq

instance : Zero (Classes M S) := ⟨cls (emptyFamily M S)⟩
instance : One (Classes M S) := ⟨cls (unitFamily M S)⟩
instance : Add (Classes M S) :=
  ⟨Quotient.map₂ (sa := isoSetoid M S) (sb := isoSetoid M S) (sc := isoSetoid M S) append
    (fun a b h c d j => append_congr a b c d h j)⟩
instance : Mul (Classes M S) :=
  ⟨Quotient.map₂ (sa := isoSetoid M S) (sb := isoSetoid M S) (sc := isoSetoid M S) product
    (fun a b h c d j => product_congr a b c d h j)⟩

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

end GeneralizedEuler.Section5.MixedTaggedFamily
