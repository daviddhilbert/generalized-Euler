module

public import Section4.WholeFiberRelation
import all Section4.FiniteScissors
import all Section2.RVDefinableEquivalence

/-! Restriction of a fixed-base definable RV bijection to a target cell
and its inverse image, before passing to scissor classes. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {I H : Type} {D : Set (I → Z .rv)} {E : Set (H → Z .rv)} (e : D ≃ E)

def rvPreimage (B : Set (H → Z .rv)) := {x | ∃ t : D, t.val = x ∧ (e t).val ∈ B}

theorem rvPreimage_mem (B : Set (H → Z .rv)) (t : D) :
    t.val ∈ rvPreimage e B ↔ (e t).val ∈ B := by
  refine ⟨?_,fun h => ⟨t,rfl,h⟩⟩
  rintro ⟨z,hz,h⟩; exact (Subtype.ext hz : z = t) ▸ h

variable (he : SortedDefinableOver M S.carrier (rvGraph (fun x => (e x).val)))
include he in
theorem restricted_rvGraph [Finite H] (B : Set (H → Z .rv)) (hb : isRVSet M S B) (sub : B ⊆ E) :
    isRVSet M S (rvPreimage e B) ∧ RVDefinablyEquivalent M S.carrier (rvPreimage e B) B := by
  let G := {w : I ⊕ H → Z .rv | ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr}
  have hg : isRVSet M S G := he
  let edge := G ∩ {w | w ∘ Sum.inr ∈ B}
  have hedge : isRVSet M S edge := hg.inter (isRVSet_precomp Sum.inr hb)
  have domain : rvPreimage e B = {x | ∃ y : H → Z .rv, Sum.elim x y ∈ edge} := by
    ext x; constructor
    · rintro ⟨t,rfl,h⟩; exact ⟨(e t).val,⟨t,rfl,rfl⟩,h⟩
    · rintro ⟨y,⟨t,h,eq⟩,hy⟩; exact ⟨t,h,eq.symm ▸ hy⟩
  refine ⟨domain ▸ isRVSet_project hedge,?_⟩
  let get (x : rvPreimage e B) : D := ⟨x.val,by obtain ⟨t,h,_⟩ := x.property; exact h ▸ t.property⟩
  let f : rvPreimage e B ≃ B :=
    { toFun := fun x => ⟨(e (get x)).val,(rvPreimage_mem e B (get x)).mp x.property⟩
      invFun := fun y => ⟨(e.symm ⟨y.val,sub y.property⟩).val,
        (rvPreimage_mem e B _).mpr (by rw [e.apply_symm_apply]; exact y.property)⟩
      left_inv := fun x => Subtype.ext (congrArg (fun t : D => t.val) (e.symm_apply_apply (get x)))
      right_inv := fun y => Subtype.ext (congrArg (fun t : E => t.val) (e.apply_symm_apply ⟨y.val,sub y.property⟩)) }
  refine ⟨f,?_⟩
  unfold isRVSet at hedge
  convert hedge using 1
  ext a
  change (∃ t : rvPreimage e B, t.val = a .rv ∘ Sum.inl ∧ (e (get t)).val = a .rv ∘ Sum.inr) ↔ a .rv ∈ edge
  constructor
  · rintro ⟨x,hx,eq⟩; exact ⟨⟨get x,hx,eq⟩,(congrArg (· ∈ B) eq).mp (f x).property⟩
  · rintro ⟨⟨x,hx,eq⟩,hB⟩
    exact ⟨⟨x.val,(rvPreimage_mem e B x).mpr (eq.symm ▸ hB)⟩,hx,eq⟩

theorem rvPreimage_partition {J : Type} (B : J → Set (H → Z .rv))
    (disj : Pairwise (fun i j => Disjoint (B i) (B j))) (cover : (⋃ j, B j) = E) :
    Pairwise (fun i j => Disjoint (rvPreimage e (B i)) (rvPreimage e (B j))) ∧ (⋃ j, rvPreimage e (B j)) = D := by
  constructor
  · intro i j ne; apply Set.disjoint_left.mpr
    rintro _ ⟨x,rfl,hx⟩ h
    exact Set.disjoint_left.mp (disj ne) hx ((rvPreimage_mem e _ x).mp h)
  · ext x; rw [Set.mem_iUnion]; constructor
    · rintro ⟨_,a,rfl,_⟩; exact a.property
    · intro h; let t : D := ⟨x,h⟩
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ((congrArg ((e t).val ∈ ·) cover).mpr (e t).property)
      exact ⟨j,t,rfl,hj⟩

end GeneralizedEuler.Section4
