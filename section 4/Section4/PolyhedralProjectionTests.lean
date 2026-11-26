module

public import Section4.PointedConeSubdivision
public import Section4.LinearSignTransfer
import all Section4.PointedConeSubdivision
import all Section4.SimplicialConeSubdivision
import all Section4.LinearSignTransfer
import all Section4.ProjectedConeRays

/-! Images of faces have finite defining linear tests in parameter
space. All the tests for all source faces can be put in one arrangement. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F E : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup E] [Module F E]

def Controlled (forms : Finset (E →ₗ[F] F)) (D : Set E) :=
  ∀ x y : E, (∀ a ∈ forms, SameSign (a x) (a y)) → (x∈D ↔ y∈D)

def HasTests (D : Set E) := ∃ forms : Finset (E →ₗ[F] F), Controlled forms D

omit [IsStrictOrderedRing F] in
theorem union_tests {I : Type*} [Fintype I] (D : I → Set E) (h : ∀ i, HasTests (F := F) (D i)) :
    HasTests (F := F) (⋃ i, D i) := by
  classical
  choose f law using h
  refine ⟨Finset.univ.biUnion f,fun x y signs => ?_⟩
  simp only [Set.mem_iUnion]
  exact exists_congr fun i => law i x y (fun t ht => signs t (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩))

namespace SimpleCone
variable {B : Type*} [Fintype B] (c : SimpleCone F (B → F))

def tests : Finset ((B → F) →ₗ[F] F) := by
  classical
  exact Finset.univ.image (fun i : Fin c.rays => (LinearMap.proj i).comp c.param.leftInverse) ∪
    Finset.univ.image (fun j : B => (LinearMap.proj j).comp (c.param.comp c.param.leftInverse - LinearMap.id))

omit [IsStrictOrderedRing F] [Fintype B] in
theorem mem_open_iff (x : B → F) : x ∈ c.openPart ↔
    (∀ i, 0<c.param.leftInverse x i) ∧ c.param (c.param.leftInverse x)=x := by
  constructor
  · rintro ⟨z,h,rfl⟩
    rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr c.injective)]; exact ⟨h,rfl⟩
  · rintro ⟨pos,eq⟩; exact ⟨_,pos,eq⟩

omit [IsStrictOrderedRing F] in
theorem controlled_open : Controlled c.tests c.openPart := by
  classical
  intro x y h
  rw [c.mem_open_iff,c.mem_open_iff]
  apply and_congr
  · apply forall_congr'
    intro i
    have sign := h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun i : Fin c.rays => (LinearMap.proj i).comp c.param.leftInverse) (Finset.mem_univ i)))
    exact lt_iff_lt_of_le_iff_le' sign.2 sign.1
  · simp only [funext_iff]
    apply forall_congr'
    intro j
    have sign := h _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun j : B => (LinearMap.proj j).comp (c.param.comp c.param.leftInverse - LinearMap.id)) (Finset.mem_univ j)))
    change SameSign (c.param (c.param.leftInverse x) j - x j) (c.param (c.param.leftInverse y) j - y j) at sign
    rw [← sub_eq_zero,← sub_eq_zero (a := c.param (c.param.leftInverse y) j)]
    exact (le_antisymm_iff.trans (and_congr sign.2 sign.1)).trans le_antisymm_iff.symm

end SimpleCone

variable {I B : Type*} [Fintype I] [Fintype B] (a : I → E →ₗ[F] F)
  (pointed : ∀ w, (∀ i, a i w=0) → w=0) (π : E →ₗ[F] (B → F))

include pointed in
theorem projection_tests : HasTests (F := F) (π '' polyCone a) := by
  obtain ⟨_,c,_,cv⟩ := subdivide_image a pointed π
  rw [← cv]
  exact union_tests _ (fun i => ⟨(c i).tests,(c i).controlled_open⟩)

include pointed in
theorem all_face_tests : ∃ forms : Finset ((B → F) →ₗ[F] F),
    ∀ u, Controlled forms (π '' activeFace a u) := by
  classical
  let rows (s : Finset I) : I ⊕ s → E →ₗ[F] F := Sum.elim a (fun i => -a i.val)
  have inj s (w : E) (h : ∀ i, rows s i w=0) := pointed w (fun i => h (.inl i))
  choose f hf using fun s => projection_tests (rows s) (inj s) π
  refine ⟨Finset.univ.biUnion f,fun u => ?_⟩
  let s := Finset.univ.filter (fun i => a i u=0)
  have eq : activeFace a u = polyCone (rows s) := by
    ext z
    constructor
    · intro h t
      rcases t with i|⟨i,hi⟩
      · exact h.1 i
      · change 0 ≤ -(a i z)
        rw [h.2 i (Finset.mem_filter.mp hi).2,neg_zero]
    · intro h
      refine ⟨fun i => h (.inl i),fun i hi => ?_⟩
      have other := h (.inr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
      exact le_antisymm (neg_nonneg.mp other) (h (.inl i))
  rw [eq]
  exact fun x y law => hf s x y (fun t ht => law t (Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,ht⟩))

end GeneralizedEuler.Section4.Polyhedral
