module

public import Section4.ValueMatrixExtension
import all Section4.ValueMatrixExtension
import all Section4.LinearSignTransfer
import Mathlib.LinearAlgebra.Dimension.Free

/-! A single linear functional specializes finitely many value-space signs
to the exponent field. Using a linear functional keeps all linear maps in
a partition compatible, including the maps recovering cone coefficients. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

theorem specialize_signs (s : Finset V) : ∃ f : V →ₗ[F] F, ∀ v ∈ s, SameSign v (f v) := by
  classical
  let W := Submodule.span F (s : Set V)
  let b := Module.finBasis F W
  let e := (Fintype.equivFin s).symm
  let z (i : Fin (Fintype.card s)) : W := ⟨(e i).val,Submodule.subset_span (e i).property⟩
  let a i j := b.repr (z i) j
  obtain ⟨y,h⟩ := realize_linear_signs _ a (fun j => (b j : V))
  let f := (b.constr F y).comp W.subtype.leftInverse
  refine ⟨f,fun v hv => ?_⟩
  let i := e.symm ⟨v,hv⟩
  have val : (z i : V) = v := congrArg Subtype.val (e.apply_symm_apply ⟨v,hv⟩)
  rw [← val]
  have source : linearTest (a i) (fun j => (b j : V)) = (z i : V) := by
    simpa only [linearTest,a,map_sum,map_smul,Submodule.subtype_apply] using congrArg W.subtype (b.sum_repr (z i))
  have ev : f (z i) = linearTest (a i) y := by
    change (b.constr F y) (W.subtype.leftInverse (W.subtype (z i))) = _
    rw [LinearMap.leftInverse_apply_of_inj W.ker_subtype,Module.Basis.constr_apply_fintype]
    rfl
  simpa only [← source, ← ev] using h i

variable {X Y : Type*} (specialize : (V →ₗ[F] F) → X → Y)

/-- A finite set of tested values determines membership after specialization. -/
def Transfers (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∀ x, ∃ s : Finset V, ∀ f : V →ₗ[F] F, (∀ v ∈ s, SameSign v (f v)) → (P x ↔ Q (specialize f x))

namespace Transfers
variable {specialize} {P P' : X → Prop} {Q Q' : Y → Prop}

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem binary (op : Prop → Prop → Prop) (a : Transfers specialize P Q) (b : Transfers specialize P' Q') :
    Transfers specialize (fun x => op (P x) (P' x)) (fun y => op (Q y) (Q' y)) := by
  classical
  intro x
  obtain ⟨s,hs⟩ := a x
  obtain ⟨t,ht⟩ := b x
  refine ⟨s ∪ t,fun f h => ?_⟩
  dsimp only
  rw [propext (hs f (fun v hv => h v (Finset.mem_union_left _ hv))),
    propext (ht f (fun v hv => h v (Finset.mem_union_right _ hv)))]

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem finite {I : Type*} [Fintype I] {p : I → X → Prop} {q : I → Y → Prop}
    (op : (I → Prop) → Prop) (h : ∀ i, Transfers specialize (p i) (q i)) :
    Transfers specialize (fun x => op (fun i => p i x)) (fun y => op (fun i => q i y)) := by
  classical
  intro x
  choose s hs using fun i => h i x
  refine ⟨Finset.univ.biUnion s,fun f sign => ?_⟩
  have eq : (fun i => p i x) = (fun i => q i (specialize f x)) := funext fun i =>
    propext (hs i f (fun v hv => sign v (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩)))
  exact iff_of_eq (congrArg op eq)

theorem universal (h : Transfers specialize P Q) (law : ∀ y, Q y) (x : X) : P x := by
  obtain ⟨s,hs⟩ := h x
  obtain ⟨f,hf⟩ := specialize_signs (F := F) s
  exact (hs f hf).mpr (law _)

end Transfers

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem specialize_matrix {I J : Type*} [Fintype I] (f : V →ₗ[F] F)
    (A : (I → F) →ₗ[F] (J → F)) (x : I → V) : (fun j => f (extendMatrix A x j)) = A (fun i => f (x i)) := by
  rw [← extendMatrix_field A]
  funext j
  simp [extendMatrix,linearTest,map_sum]

end GeneralizedEuler.Section4.Polyhedral
