module

public import Section4.AxialRayCoordinates
public import Section4.ConeFiberPresentations
import all Section4.AxialRayCoordinates
import all Section4.ConeFiberPresentations
import all Section4.SimplicialValueFibers
import all Section4.BarycentricValueFibers
import all Section4.SpecializedConePartitions
import all Section4.ValueMatrixExtension

/-! The intersection of a retained axial cone with the specified base
parameters is the carrier of a fixed-base fiber chart, in degree k. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {G : Submodule F V} {k r : ℕ}
  (d : SimpleCone F (PairSpace (Fin k) (Fin r) F)) (t : Fin r → G) (positive : ∀ b, 0<(t b : V))

def coneSlice : Set (Fin k → V) := {x | pack x (fun j => (t j : V)) ∈ d.packed.valuePart}

omit [IsOrderedAddMonoid V] in
include positive in
theorem chart_of_nonempty_slice (s : AxialRays d) (nonempty : (coneSlice d t).Nonempty) :
    ∃ chart : FiberChart G k, chart.carrier = coneSlice d t := by
  classical
  obtain ⟨x,hx⟩ := nonempty
  obtain ⟨c,e,h,width,vert,group⟩ := build_ray_layout s.group (s.hit positive hx) d.ray_bound G t positive
  let rows (i : Fin k) (j : c.Coeff) := (d.ray (e j)).1 i * (s.scale (e j))⁻¹
  let f (z : c.Coeff → V) (i : Fin k) := ∑ j, rows i j • z j
  have fst (z : c.Coeff → V) (i : Fin k) :
      extendMatrix d.packed.param (s.recover c e z) (.inl i)=f z i := by
    rw [d.source_sum,← e.sum_comp (fun j => (d.ray j).1 i • s.recover c e z j)]
    simp [f,rows,AxialRays.recover,mul_smul]
  have snd (z : c.Coeff → V) (hz : z∈c.domain) (b : Fin r) :
      extendMatrix d.packed.param (s.recover c e z) (.inr b) = (t b : V) := by
    obtain ⟨b,rfl⟩ := h.surjective b
    rw [s.block_sum c e h vert group,s.normal_recover]
    exact (hz.2 b).2.trans (congrArg Subtype.val (width b))
  have eq (z : c.Coeff → V) (hz : z∈c.domain) :
      extendMatrix d.packed.param (s.recover c e z) = pack (f z) (fun j => (t j : V)) := by
    funext i; cases i with | inl i => exact fst z i | inr b => exact snd z hz b
  have inj : InjOn f c.domain := by
    intro x hx y hy hxy
    have full := (eq x hx).trans ((congrArg (fun v => pack v (fun b => (t b : V))) hxy).trans (eq y hy).symm)
    have raw := extendMatrix_injective d.packed.param d.packed.injective full
    simpa only [s.normal_recover] using congrArg (s.normal c e) raw
  let chart : FiberChart G k := ⟨c,rows,fun _ => 0,by simpa [f] using inj⟩
  have ev : chart.eval=f := by funext z i; simp [chart,FiberChart.eval,f]
  refine ⟨chart,?_⟩
  change chart.eval '' c.domain = _
  rw [ev]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨s.recover c e z,fun i => smul_pos (inv_pos.mpr (s.positive i)) ?_,eq z hz⟩
    rcases q : e.symm i with j|⟨b,j⟩
    · exact hz.1 j
    · exact (hz.2 b).1 j
  · rintro ⟨u,pu,eq'⟩
    let z := s.normal c e u
    have pos (i : c.Coeff) : 0<z i := smul_pos (s.positive _) (pu _)
    refine ⟨z,⟨fun _ => pos _,fun b => ⟨fun j => pos _,?_⟩⟩,?_⟩
    · rw [← s.block_sum c e h vert group,eq',width]
      rfl
    · funext i
      rw [← fst]
      change extendMatrix d.packed.param (s.recover c e (s.normal c e u)) (.inl i) = _
      rw [s.recover_normal,eq']
      rfl

theorem triangulate_mixed {J : Type} [Fintype J] (a : J → PairSpace (Fin k) (Fin m) F →ₗ[F] F)
    (pointed : ∀ w, (∀ i, a i w=0) → w=0) (strict : J → Prop) (p : Fin m → G) :
    HasFiberTriangulation (G := G) {x | valueMixed a strict (x,fun j => (p j : V))} := by
  classical
  obtain ⟨r,t,pos,N,d,support,dj,cover⟩ := value_mixed_partition a pointed strict G p
  let T := {i : Fin N // (coneSlice (d i) t).Nonempty}
  choose chart law using fun i : T => chart_of_nonempty_slice (d i) t pos (AxialRays.of_support _ (support i)) i.property
  let e := (Fintype.equivFin T).symm
  refine ⟨_,fun j => chart (e j),fun i j ne => ?_,?_⟩
  · dsimp only
    rw [law,law]; exact dj (fun eq => ne (e.injective (Subtype.ext eq)))
  · ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    rw [← cover x]
    constructor
    · rintro ⟨j,hj⟩; exact ⟨(e j).val,show x ∈ coneSlice (d (e j).val) t from (law (e j)) ▸ hj⟩
    · rintro ⟨j,hj⟩
      let i : T := ⟨j,x,hj⟩
      exact ⟨e.symm i,by rw [e.apply_symm_apply,law]; exact hj⟩

end GeneralizedEuler.Section4.Polyhedral
