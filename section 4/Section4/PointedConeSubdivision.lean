module

public import Section4.SimplicialConeSubdivision
import all Section4.SimplicialConeSubdivision
import all Section4.PolyhedralGenerators
import all Section4.ConeBoundary
import all Section4.ProjectedConeRays

/-! Triangulating a pointed cone or its linear image. An injective list
of scalar tests supplies pointedness, including in dimension zero. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F E H I : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup E] [Module F E]
  [AddCommGroup H] [Module F H] [Fintype I]

def generatorMap {n : ℕ} (r : Fin n → E) : (Fin n → F) →ₗ[F] E :=
  ∑ i : Fin n, (LinearMap.proj (R := F) i).smulRight (r i)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem generatorMap_apply {n} (r : Fin n → E) (x : Fin n → F) :
    generatorMap r x = ∑ i, x i • r i := by simp [generatorMap,LinearMap.sum_apply]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem generatorMap_single {n} (r : Fin n → E) (i : Fin n) :
    generatorMap (F := F) r (Pi.single i 1) = r i := by
  rw [generatorMap_apply,Finset.sum_eq_single i]
  · simp
  · intro j _ ne; simp [Pi.single_eq_of_ne ne]
  · simp

variable (a : I → E →ₗ[F] F) (pointed : ∀ w, (∀ i, a i w=0) → w=0)

def vertices (i : Fin (Fintype.card (Vertex a))) : Vertex a := (Fintype.equivFin _).symm i

include pointed in
theorem generators_image (π : E →ₗ[F] H) :
    generatorMap (fun j => π (vertices a j).val) '' {x | ∀ j, (0 : F)≤x j} = π '' polyCone a := by
  classical
  ext y
  constructor
  · rintro ⟨x,pos,rfl⟩
    let u := ∑ j, x j • (vertices a j).val
    refine ⟨u,fun i => ?_,?_⟩
    · change 0 ≤ a i (∑ j, _)
      rw [map_sum]
      exact Finset.sum_nonneg fun j _ => by simpa using mul_nonneg (pos j) ((vertices a j).property.1 i)
    · simp [u,generatorMap_apply,map_sum]
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨c,pc,im⟩ := extreme_rays_generate a pointed hu
    refine ⟨c ∘ vertices a,fun j => pc _,?_⟩
    rw [generatorMap_apply,← im,map_sum]
    simpa only [Function.comp_apply,map_smul,vertices] using
      (Equiv.sum_comp (Fintype.equivFin (Vertex a)).symm (fun t => c t • π t.val))

include pointed in
theorem subdivide_image (π : E →ₗ[F] H) :
    ∃ (m : ℕ) (c : Fin m → SimpleCone F H), Pairwise (fun i j => Disjoint (c i).openPart (c j).openPart) ∧
      (⋃ i, (c i).openPart) = π '' polyCone a := by
  obtain ⟨m,c,_,dj,cover⟩ := subdivide_generators (generatorMap (F := F) (fun j => π (vertices a j).val))
  exact ⟨m,c,dj,cover.trans (generators_image a pointed π)⟩

include pointed in
theorem subdivide_pointed :
    ∃ (m : ℕ) (c : Fin m → SimpleCone F E),
      (∀ i j, IsVertex a ((c i).ray j)) ∧
      Pairwise (fun i j => Disjoint (c i).openPart (c j).openPart) ∧ (⋃ i, (c i).openPart) = polyCone a := by
  obtain ⟨m,c,orig,dj,cover⟩ := subdivide_generators (generatorMap (F := F) (fun j => (vertices a j).val))
  refine ⟨m,c,?_,dj,cover.trans ?_⟩
  · intro i j
    obtain ⟨t,eq⟩ := orig i j
    rw [eq,generatorMap_single]; exact (vertices a t).property
  · simpa only [LinearMap.id_apply,image_id'] using generators_image a pointed (LinearMap.id (R := F) (M := E))

end GeneralizedEuler.Section4.Polyhedral
