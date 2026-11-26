module

public import Section4.ParameterConeDirections
import all Section4.ParameterConeDirections
import all Section4.ProjectedConeRays
import all Section4.PolyhedralGenerators
import all Section4.ConeBoundary
import all Section4.PointedConeSubdivision
import all Section4.SimplicialConeSubdivision

/-! Subdivide a parameter space along all chosen tests. Over each of
its simplicial cones the restricted source is pointed and each of its
extreme rays projects vertically or onto a single parameter ray. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {E P : Type*} [AddCommGroup E] [Module F E] [AddCommGroup P] [Module F P]

def oriented {I : Type*} (a : I → E →ₗ[F] F) (b : I → Bool) (i : I) := if b i then a i else -a i

variable {B : Type} [Fintype B]

theorem parameter_cover (forms : Finset ((B → F) →ₗ[F] F)) :
    ∃ (m : ℕ) (c : Fin m → SimpleCone F (B → F)), (∀ i, Compatible (c i) forms) ∧
      ∀ p : B → F, ∃ i, p ∈ (c i).openPart := by
  classical
  let tests : forms ⊕ B → (B → F) →ₗ[F] F := Sum.elim Subtype.val (fun j => LinearMap.proj j)
  let row (b : forms ⊕ B → Bool) := oriented tests b
  have pointed b (w : B → F) (h : ∀ i, row b i w=0) : w=0 := by
    funext j
    have eq := h (.inr j)
    by_cases s : b (.inr j)=true <;> simpa [row,oriented,tests,s] using eq
  choose m cone vertex _ cover using fun b => subdivide_pointed (row b) (pointed b)
  let T := (b : forms ⊕ B → Bool) × Fin (m b)
  let tag := (Fintype.equivFin T).symm
  let c j := cone (tag j).1 (tag j).2
  refine ⟨_,c,fun j a ha => ?_,fun p => ?_⟩
  · let i : forms ⊕ B := .inl ⟨a,ha⟩
    have pos t := (vertex (tag j).1 (tag j).2 t).1 i
    by_cases sign : (tag j).1 i=true
    · left; intro t; simpa [c,row,oriented,sign,tests,i] using pos t
    · right; intro t; simpa [c,row,oriented,sign,tests,i] using pos t
  · let b i := decide (0≤tests i p)
    have mem : p ∈ polyCone (row b) := by intro i; by_cases h : 0≤tests i p <;> simp [row,oriented,b,h,le_of_not_ge] at *
    obtain ⟨j,hj⟩ := mem_iUnion.mp ((cover b).symm ▸ mem)
    exact ⟨tag.symm ⟨b,j⟩,by unfold c; rw [tag.apply_symm_apply]; exact hj⟩

variable {I : Type*} [Fintype I] (a : I → (E × P) →ₗ[F] F) (c : SimpleCone F P)
def fiberRows : I ⊕ Fin c.rays → (E × (Fin c.rays → F)) →ₗ[F] F :=
  Sum.elim (fun i => (a i).comp (overParameter c)) (fun j => (LinearMap.proj j).comp (LinearMap.snd _ _ _))

omit [IsStrictOrderedRing F] [Fintype I] in
theorem fiberRows_cone : polyCone (fiberRows a c) =
    polyCone (fun i => (a i).comp (overParameter c)) ∩ {u | ∀ j, 0 ≤ u.2 j} := by
  ext u
  exact ⟨fun h => ⟨fun i => h (.inl i),fun j => h (.inr j)⟩,
    fun h t => by cases t with | inl i => exact h.1 i | inr j => exact h.2 j⟩

theorem fiber_subdivision
    (pointed : ∀ w, (∀ i, a i w=0) → w=0)
    {forms : Finset (P →ₗ[F] F)} (comp : Compatible c forms)
    (adapted : ∀ u, Controlled forms ((LinearMap.snd F E P) '' activeFace a u)) :
    ∃ (m : ℕ) (d : Fin m → SimpleCone F (E × (Fin c.rays → F))),
      (∀ t j, (d t).ray j ∈ polyCone (fiberRows a c)) ∧
      (∀ t j, (∀ b, 0≤((d t).ray j).2 b) ∧
        ∀ i h, 0<((d t).ray j).2 i → 0<((d t).ray j).2 h → i=h) ∧
      Pairwise (fun i j => Disjoint (d i).openPart (d j).openPart) ∧
      (⋃ t, (d t).openPart) = polyCone (fiberRows a c) := by
  have joint (w : E × (Fin c.rays → F)) (h : ∀ i, fiberRows a c i w=0) : w=0 := by
    have eq := pointed (overParameter c w) (fun i => h (.inl i))
    exact Prod.ext (congrArg (Prod.fst : E × P → E) eq) (funext fun j => h (.inr j))
  obtain ⟨m,d,vertex,dj,cover⟩ := subdivide_pointed (fiberRows a c) joint
  refine ⟨m,d,fun t j => (vertex t j).1,fun t j => ?_,dj,cover⟩
  let u := (d t).ray j
  have v := vertex t j
  have inside : overParameter c u ∈ polyCone a := fun i => v.1 (.inl i)
  have pos : ∀ b, 0≤u.2 b := fun b => v.1 (.inr b)
  have ex := vertex_extreme _ _ v
  rw [fiberRows_cone] at ex
  exact ⟨pos,fun _ _ hi hj => extreme_projection_of_directions _ (LinearMap.snd _ _ _) u inside pos
    (parameter_directions c a comp adapted u inside pos) ex hi hj⟩

end GeneralizedEuler.Section4.Polyhedral
