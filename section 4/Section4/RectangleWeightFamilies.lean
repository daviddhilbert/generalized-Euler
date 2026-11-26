module

public import Section4.RectangleHeightInduction
public import Section4.TaggedLiftRealization
import all Section4.TaggedLiftRealization
import all Section4.RVScissorRealization
import all Section4.RVFamilyOperations
import all Section4.NormalRectangles
import all Section4.RectangleFiberFamilies

/-! Simultaneous presentation of a homogeneous RV family and its tensor by a finite sum of rectangles. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}
variable (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)


local notation "M" => canonicalStructure (L := J) O hO P
local notation "Rect" => NormalRectangle (JG := JG) (G := G) O v hO P S
open RVFamily

def RectangleWeight (k : ℕ) (a : Classes M S) (t : TensorProduct C R W) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (c : I → Rect k),
    a = ∑ i, cls (single (c i).points ((c i).points_definable pull)) ∧
    t = ∑ i, (c i).tensor hv res val

namespace RectangleWeight
local notation "Wt" => RectangleWeight pull hv res val (C := C)

theorem of_rectangle (c : Rect k) :
    Wt k (cls (single c.points (c.points_definable pull))) (c.tensor hv res val) :=
  ⟨Unit,inferInstance,fun _ => c,by simp,by simp⟩

theorem zero : Wt k 0 0 := ⟨Empty,inferInstance,Empty.elim,by simp,by simp⟩

theorem sum {I : Type} [Fintype I] (a : I → Classes M S) (w : I → TensorProduct C R W)
    (h : ∀ i, Wt k (a i) (w i)) : Wt k (∑ i, a i) (∑ i, w i) := by
  classical
  choose T ft c ha hw using h
  let _ i := ft i
  refine ⟨(i : I) × T i,inferInstance,fun x => c x.1 x.2,?_,?_⟩
  · rw [Fintype.sum_sigma]; exact Finset.sum_congr rfl fun i _ => ha i
  · rw [Fintype.sum_sigma]; exact Finset.sum_congr rfl fun i _ => hw i

theorem add {a b x y} (hx : Wt k a x) (hy : Wt k b y) : Wt k (a+b) (x+y) := by
  obtain ⟨I,_,c,rfl,rfl⟩ := hx
  obtain ⟨H,_,d,rfl,rfl⟩ := hy
  exact ⟨I ⊕ H,inferInstance,Sum.elim c d,by rw [Fintype.sum_sum_type]; rfl,by rw [Fintype.sum_sum_type]; rfl⟩

theorem mul {l a b x y} (hx : Wt k a x) (hy : Wt l b y) : Wt (k+l) (a*b) (x*y) := by
  classical
  obtain ⟨I,_,c,rfl,rfl⟩ := hx
  obtain ⟨H,_,d,rfl,rfl⟩ := hy
  choose z iso wt using fun i j => (c i).product_rectangle hv res val (C := C) pull (d j)
  refine ⟨I × H,inferInstance,fun ij => z ij.1 ij.2,?_,?_⟩
  · rw [Fintype.sum_prod_type,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply (cls_eq_iff _ _).mpr
    apply iso_retag _ _ (Equiv.punitProd Unit)
    exact fun _ => iso i j
  · simp only [Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum,wt]
    exact Finset.sum_comm

theorem unique_of_comparison
    (cmp : ∀ {I H : Type} [Fintype I] [Fintype H] (c : I → Rect k) (d : H → Rect k),
      (rvFamily c pull).Iso (rvFamily d pull) →
      (∑ i, (c i).tensor hv res val (C := C)) = ∑ j, (d j).tensor hv res val)
    {a x y} (hx : Wt k a x) (hy : Wt k a y) : x = y := by
  obtain ⟨I,_,c,hc,rfl⟩ := hx
  obtain ⟨H,_,d,hd,rfl⟩ := hy
  apply cmp c d
  apply (cls_eq_iff _ _).mp
  let _ : Fintype (rvFamily c pull).Tag := inferInstanceAs (Fintype I)
  let _ : Fintype (rvFamily d pull).Tag := inferInstanceAs (Fintype H)
  rw [cls_eq_sum,cls_eq_sum]
  exact hc.symm.trans hd

end RectangleWeight
end GeneralizedEuler.Section4
