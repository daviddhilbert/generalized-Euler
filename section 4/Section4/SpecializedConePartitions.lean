module

public import Section4.FiniteSignSpecialization
public import Section4.AdaptedParameterCones
import all Section4.FiniteSignSpecialization
import all Section4.SimplicialConeSubdivision
import all Section4.ValueMatrixExtension
import all Section4.LinearSignTransfer
import all Section4.PolyhedralProjectionTests

/-! Membership in an open simplicial cone, finite partitions by these
cones, and homogeneous linear inequalities commute with specialization. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {I J : Type*} [Fintype I]

def evalRow (a : (I → F) →ₗ[F] F) (x : I → V) : V := by
  classical
  exact linearTest (fun i => a (Pi.single i 1)) x

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem specialize_row (a : (I → F) →ₗ[F] F) (f : V →ₗ[F] F) (x : I → V) :
    f (evalRow a x) = a (fun i => f (x i)) :=
  congrFun (specialize_matrix f (LinearMap.pi (fun _ : Unit => a)) x) ()

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem transfers_row (a : (I → F) →ₗ[F] F) :
    Transfers (fun (f : V →ₗ[F] F) x i => f (x i)) (fun x => 0≤evalRow a x) (fun x => 0≤a x) := by
  intro x
  refine ⟨{evalRow a x},fun f h => ?_⟩
  simpa only [specialize_row] using (h _ (Finset.mem_singleton_self _)).1

namespace SimpleCone
variable (c : SimpleCone F (I → F))

def valuePart : Set (I → V) := extendMatrix c.param '' {z | ∀ i, 0<z i}

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem mem_valuePart (x : I → V) : x ∈ c.valuePart ↔
    (∀ i, 0<extendMatrix c.param.leftInverse x i) ∧
      extendMatrix c.param (extendMatrix c.param.leftInverse x)=x := by
  constructor
  · rintro ⟨z,pos,rfl⟩
    rw [extendMatrix_leftInverse _ c.injective]; exact ⟨pos,rfl⟩
  · rintro ⟨pos,rec⟩; exact ⟨_,pos,rec⟩

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem transfers_open :
    Transfers (fun (f : V →ₗ[F] F) x i => f (x i)) (fun x => x ∈ c.valuePart) (fun x => x ∈ c.openPart) := by
  classical
  intro x
  let z := extendMatrix c.param.leftInverse x
  let r i := extendMatrix c.param z i - x i
  refine ⟨Finset.univ.image z ∪ Finset.univ.image r,fun f law => ?_⟩
  dsimp only
  rw [c.mem_valuePart,c.mem_open_iff]
  have hz := specialize_matrix f c.param.leftInverse x
  have hr := specialize_matrix f c.param z
  change (fun i => f (z i)) = _ at hz
  rw [← hz,← hr]
  apply and_congr
  · apply forall_congr'; intro i
    have h := law _ (Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
    exact lt_iff_lt_of_le_iff_le' h.2 h.1
  · simp only [funext_iff]
    apply forall_congr'; intro i
    have h := law _ (Finset.mem_union_right _ (Finset.mem_image_of_mem r (Finset.mem_univ i)))
    change SameSign (extendMatrix c.param z i-x i) (f (extendMatrix c.param z i-x i)) at h
    rw [map_sub] at h
    exact (sub_eq_zero.symm.trans ((le_antisymm_iff.trans (and_congr h.2 h.1)).trans le_antisymm_iff.symm)).trans sub_eq_zero

end SimpleCone

theorem value_cover {n} (c : Fin n → SimpleCone F (I → F)) (cover : ∀ x, ∃ i, x∈(c i).openPart)
    (x : I → V) : ∃ i, x∈(c i).valuePart :=
  Transfers.universal (Transfers.finite (fun p => ∃ i, p i) (fun i => (c i).transfers_open)) cover x

def pack {A : Type*} (x : I → A) (y : J → A) : I ⊕ J → A := Sum.elim x y

def packLinear : ((I → F) × (J → F)) ≃ₗ[F] (I ⊕ J → F) where
  toFun z := pack z.1 z.2
  invFun u := (fun i => u (.inl i),fun j => u (.inr j))
  left_inv _ := rfl
  right_inv u := funext fun i => by cases i <;> rfl
  map_add' _ _ := funext fun i => by cases i <;> rfl
  map_smul' _ _ := funext fun i => by cases i <;> rfl

@[expose] def SimpleCone.packed (d : SimpleCone F ((I → F) × (J → F))) : SimpleCone F (I ⊕ J → F) where
  rays := d.rays
  param := packLinear.toLinearMap.comp d.param
  injective := packLinear.injective.comp d.injective

omit [IsStrictOrderedRing F] [Fintype I] in
theorem SimpleCone.mem_packed (d : SimpleCone F ((I → F) × (J → F))) (x : I → F) (y : J → F) :
    pack x y ∈ d.packed.openPart ↔ (x,y)∈d.openPart := by
  constructor
  · rintro ⟨z,h,eq⟩; exact ⟨z,h,packLinear.injective eq⟩
  · rintro ⟨z,h,eq⟩; exact ⟨z,h,congrArg (packLinear : _ ≃ₗ[F] (I⊕J → F)) eq⟩

end GeneralizedEuler.Section4.Polyhedral
