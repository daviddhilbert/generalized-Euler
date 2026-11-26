module

public import Section4.RayBlockLayout
public import Section4.ValueConePartition
import all Section4.ValueMatrixExtension
import all Section4.SimplicialConeSubdivision
import all Section4.SpecializedConePartitions
import all Section4.LinearSignTransfer
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Rescale every nonvertical column to unit height over its single
parameter axis. At positive parameters every axis must occur. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {k r : ℕ} (d : SimpleCone F (PairSpace (Fin k) (Fin r) F))

structure AxialRays where
  group : Fin d.rays → Option (Fin r)
  scale : Fin d.rays → F
  positive : ∀ i, 0<scale i
  entry : ∀ i b, (d.ray i).2 b = if group i=some b then scale i else 0

def AxialRays.of_support (support : ∀ i, (∀ b, 0≤(d.ray i).2 b) ∧
    ∀ b j, 0<(d.ray i).2 b → 0<(d.ray i).2 j → b=j) : AxialRays d := by
  classical
  let axis i := if h : ∃ b, 0<(d.ray i).2 b then some h.choose else none
  let scale i := (axis i).elim 1 (fun b => (d.ray i).2 b)
  refine ⟨axis,scale,fun i => ?_,fun i b => ?_⟩
  · by_cases h : ∃ b, 0<(d.ray i).2 b
    · simpa [scale,axis,h] using h.choose_spec
    · simp [scale,axis,h]
  · by_cases h : ∃ b, 0<(d.ray i).2 b
    · by_cases eq : h.choose=b
      · simp [scale,axis,h,eq]
      · have z := le_antisymm (le_of_not_gt (fun hb => eq ((support i).2 _ _ h.choose_spec hb))) ((support i).1 b)
        simp [scale,axis,h,eq,z]
    · have z := le_antisymm (le_of_not_gt (fun hb => h ⟨b,hb⟩)) ((support i).1 b)
      simp [axis,h,z]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem SimpleCone.ray_bound : d.rays ≤ k+r := by
  have h := LinearMap.finrank_le_finrank_of_injective d.injective
  simpa [PairSpace,Module.finrank_prod,Module.finrank_pi] using h

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem single_independent {n : ℕ} (d₁ d₂ : DecidableEq (Fin n)) (i : Fin n) :
    @Pi.single (Fin n) (fun _ => F) _ d₁ i 1 = @Pi.single (Fin n) (fun _ => F) _ d₂ i 1 := by
  obtain rfl := Subsingleton.elim d₁ d₂
  rfl

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem SimpleCone.parameter_sum (u : Fin d.rays → V) (b : Fin r) :
    extendMatrix d.packed.param u (.inr b) = ∑ i, (d.ray i).2 b • u i := by
  classical
  simp [extendMatrix,linearTest,entries,SimpleCone.packed,packLinear,pack,SimpleCone.ray,LinearMap.comp_apply]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun v => (d.param v).2 b • u i) (single_independent _ _ i)

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem SimpleCone.source_sum (u : Fin d.rays → V) (j : Fin k) :
    extendMatrix d.packed.param u (.inl j) = ∑ i, (d.ray i).1 j • u i := by
  classical
  simp [extendMatrix,linearTest,entries,SimpleCone.packed,packLinear,pack,SimpleCone.ray,LinearMap.comp_apply]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun v => (d.param v).1 j • u i) (single_independent _ _ i)

variable {d} (a : AxialRays d)
omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem AxialRays.hit {t : Fin r → V} (positive : ∀ b, 0<t b) {x : Fin k → V}
    (mem : pack x t ∈ d.packed.valuePart) (b) : ∃ i, a.group i=some b := by
  obtain ⟨u,_,eq⟩ := mem
  by_contra! all
  have ev := congrFun eq (.inr b)
  change extendMatrix d.packed.param u (.inr b) = t b at ev
  rw [d.parameter_sum u b] at ev
  have z : t b=0 := by simpa [a.entry,all,pack] using ev.symm
  exact (positive b).ne' z

variable {G : Submodule F V} (c : ConeFiber G k) (e : c.Coeff ≃ Fin d.rays)
  (h : Fin c.groups ≃ Fin r) (vertical : ∀ i, a.group (e (.inl i))=none)
  (block : ∀ b j, a.group (e (.inr ⟨b,j⟩))=some (h b))

def AxialRays.normal (u : Fin d.rays → V) (j : c.Coeff) := a.scale (e j) • u (e j)
def AxialRays.recover (z : c.Coeff → V) (i : Fin d.rays) := (a.scale i)⁻¹ • z (e.symm i)

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem AxialRays.recover_normal (u : Fin d.rays → V) : a.recover c e (a.normal c e u) = u := by
  funext i
  simp [AxialRays.recover,AxialRays.normal,smul_smul,(a.positive _).ne']

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem AxialRays.normal_recover (z : c.Coeff → V) : a.normal c e (a.recover c e z) = z := by
  funext j
  simp [AxialRays.recover,AxialRays.normal,smul_smul,(a.positive _).ne']

include vertical block in
omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem AxialRays.block_sum (u : Fin d.rays → V) (b : Fin c.groups) :
    extendMatrix d.packed.param u (.inr (h b)) = ∑ j, a.normal c e u (.inr ⟨b,j⟩) := by
  classical
  rw [d.parameter_sum,← e.sum_comp (fun i => (d.ray i).2 (h b) • u i),Fintype.sum_sum_type,Fintype.sum_sigma]
  simp [a.entry,vertical,block,AxialRays.normal]

end GeneralizedEuler.Section4.Polyhedral
