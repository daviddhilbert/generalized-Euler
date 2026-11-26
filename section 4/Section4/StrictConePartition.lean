module

public import Section4.AdaptedParameterCones
import all Section4.AdaptedParameterCones
import all Section4.ParameterConeDirections
import all Section4.PolyhedralProjectionTests
import all Section4.SimplicialConeSubdivision
import all Section4.ProjectedConeRays
import all Section4.LinearSignTransfer

/-! Retaining relatively open source simplices cut out by a mixture
of strict and weak inequalities. The partition applies over each
compatible parameter simplex, with its coefficients as coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F E P : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup E] [Module F E] [AddCommGroup P] [Module F P]
  {I : Type} [Fintype I]

def MixedCone (a : I → E →ₗ[F] F) (strict : I → Prop) (x : E) : Prop :=
  x ∈ polyCone a ∧ ∀ i, strict i → 0<a i x

theorem SimpleCone.strict_center (d : SimpleCone F E) (a : E →ₗ[F] F)
    (nonneg : ∀ j, 0≤a (d.ray j)) {x : E} (hx : x ∈ d.openPart) :
    0<a x ↔ 0<a (d.param (fun _ => 1)) := by
  classical
  obtain ⟨z,hz,rfl⟩ := hx
  have comp : Compatible d {a} := by
    intro g hg; obtain rfl := Finset.mem_singleton.mp hg; exact Or.inl nonneg
  have signs := compatible_signs d comp z (fun _ => 1) (fun j => (hz j).le) (fun _ => zero_le_one)
    (fun j => iff_of_true (hz j) zero_lt_one) a (Finset.mem_singleton_self _)
  exact lt_iff_lt_of_le_iff_le' signs.2 signs.1

variable (a : I → (E × P) →ₗ[F] F) (pointed : ∀ w, (∀ i, a i w=0) → w=0)
  (strict : I → Prop) (c : SimpleCone F P)

include pointed in
theorem mixed_fiber_partition {forms : Finset (P →ₗ[F] F)} (comp : Compatible c forms)
    (adapted : ∀ u, Controlled forms ((LinearMap.snd F E P) '' activeFace a u)) :
    ∃ (n : ℕ) (d : Fin n → SimpleCone F (E × (Fin c.rays → F))),
      (∀ t j, (∀ b, 0≤((d t).ray j).2 b) ∧
        ∀ i h, 0<((d t).ray j).2 i → 0<((d t).ray j).2 h → i=h) ∧
      Pairwise (fun i j => Disjoint (d i).openPart (d j).openPart) ∧
      ∀ u, (∃ i, u ∈ (d i).openPart) ↔ MixedCone a strict (overParameter c u) ∧ ∀ j, 0≤u.2 j := by
  classical
  obtain ⟨m,d,weak,support,disj,cover⟩ := fiber_subdivision a c pointed comp adapted
  let keep t := ∀ i, strict i → 0<a i (overParameter c ((d t).param (fun _ => 1)))
  let idx := (Fintype.equivFin {t : Fin m // keep t}).symm
  have mem {t} {u} (hu : u ∈ (d t).openPart) : u ∈ polyCone (fiberRows a c) :=
    cover ▸ mem_iUnion.mpr ⟨t,hu⟩
  have center {t} {u} (hu : u ∈ (d t).openPart) (i : I) :
      0<a i (overParameter c u) ↔ 0<a i (overParameter c ((d t).param (fun _ => 1))) :=
    (d t).strict_center ((a i).comp (overParameter c)) (fun j => weak t j (.inl i)) hu
  refine ⟨_,fun i => d (idx i).val,fun i => support _,fun i j ne => disj (fun eq => ne (idx.injective (Subtype.ext eq))),fun u => ?_⟩
  constructor
  · rintro ⟨t,ht⟩
    have h := mem ht
    exact ⟨⟨fun i => h (.inl i),fun i hi => (center ht i).mpr ((idx t).property i hi)⟩,fun j => h (.inr j)⟩
  · rintro ⟨⟨h,pos⟩,pr⟩
    have h' : u ∈ polyCone (fiberRows a c) := by
      intro i; cases i with | inl i => exact h i | inr j => exact pr j
    obtain ⟨t,ht⟩ := mem_iUnion.mp (cover.symm ▸ h')
    let k : {t : Fin m // keep t} := ⟨t,fun i hi => (center ht i).mp (pos i hi)⟩
    exact ⟨idx.symm k,by dsimp only; rw [idx.apply_symm_apply]; exact ht⟩

end GeneralizedEuler.Section4.Polyhedral
