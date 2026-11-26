module

public import Section4.RefinedChartTest
public import Section4.ValueMembershipPartition
import all Section4.PositiveRectangles
import all Section4.ValueStratification

/-! Comparison of two RV decompositions on a common value slice, allowing
the projected value supports to overlap. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {G : Submodule F V}
  {J : Language} [J.Structure V] {n : ℕ}

structure ChartPiece (v : T →ₗ[F] V) (G : Submodule F V) (J : Language) [J.Structure V] (n : ℕ) where
  value : DefinablePiece J G n
  residue : Set (value.frame.dependent → v.ker)

namespace ChartPiece
variable {v} (p : ChartPiece v G J n)

def carrier := (fun w => p.value.frame.assemble v s w.1 w.2) ''
    ({z | v ∘ z ∈ p.value.domain} ×ˢ p.residue)

theorem assemble_mem (z : Fin p.value.rank → T) (hz : v ∘ z ∈ p.value.domain)
    (b : p.value.frame.dependent → v.ker) : p.value.frame.assemble v s z b ∈ p.carrier s ↔ b ∈ p.residue := by
  constructor
  · rintro ⟨⟨w,c⟩,⟨_,hc⟩,eq⟩
    have same := p.value.frame.assemble_injective v s (a₁ := (w,c)) (a₂ := (z,b)) eq
    have bc : c = b := congrArg Prod.snd same
    exact bc ▸ hc
  · intro hb; exact ⟨(z,b),⟨hz,hb⟩,rfl⟩

include hs in
theorem value_mem {x : Fin n → T} (hx : x ∈ p.carrier s) : v ∘ x ∈ p.value.support := by
  obtain ⟨⟨z,b⟩,⟨hz,_⟩,rfl⟩ := hx
  exact ⟨_,hz,(p.value.frame.assemble_value v s hs z b).symm⟩

def onSlice (c : DefinablePiece J G n) : Set (c.frame.dependent → v.ker) :=
  {b | p.value.frame.residuePart (c.frame.padResidue b) ∈ p.residue}

include hs in
theorem slice_membership (c : DefinablePiece J G n) (h : c.support ⊆ p.value.support)
    (z : Fin c.rank → T) (hz : v ∘ z ∈ c.domain) (b : c.frame.dependent → v.ker) :
    c.frame.assemble v s z b ∈ p.carrier s ↔ b ∈ p.onSlice c := by
  obtain ⟨α,hα,hi⟩ := c.independent
  have hit := h (show c.frame.eval α ∈ c.support from ⟨α,hα,rfl⟩)
  obtain ⟨y,hy,eq⟩ := h (show c.frame.eval (v ∘ z) ∈ c.support from ⟨_,hz,rfl⟩)
  have proj : c.frame.eval (v ∘ z) ∘ p.value.frame.free ∈ p.value.domain := by
    rwa [← eq,p.value.frame.project_eval]
  exact p.value.frame.refine_membership v s hs c.frame α hi (Set.image_subset_range _ _ hit)
    (p.carrier s) p.value.domain p.residue (p.assemble_mem s) z proj b

variable {I : Type} (a : I → ChartPiece v G J n) (c : DefinablePiece J G n)
  (active : I → Bool)
  (spec : ∀ i γ, γ ∈ c.support → (γ ∈ (a i).value.support ↔ active i = true))

include hs spec in
theorem slice_union (z : Fin c.rank → T) (hz : v ∘ z ∈ c.domain) :
    (⋃ i : {i // active i = true}, (a i.val).onSlice c) =
      (fun b => c.frame.assemble v s z b) ⁻¹' ⋃ i, (a i).carrier s := by
  ext b; simp only [Set.mem_iUnion,Set.mem_preimage]
  have source : v ∘ c.frame.assemble v s z b ∈ c.support := ⟨_,hz,(c.frame.assemble_value v s hs z b).symm⟩
  have ok (i : {i // active i = true}) : c.support ⊆ (a i.val).value.support :=
    fun γ hγ => (spec i.val γ hγ).mpr i.property
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val,((a i.val).slice_membership s hs c (ok i) z hz b).mpr hi⟩
  · rintro ⟨i,hi⟩
    let j : {i // active i = true} := ⟨i,(spec i _ source).mp ((a i).value_mem s hs hi)⟩
    exact ⟨j,((a i).slice_membership s hs c (ok j) z hz b).mp hi⟩

include hs spec in
theorem slice_disjoint (disj : Pairwise (fun i j => Disjoint ((a i).carrier s) ((a j).carrier s))) :
    Pairwise (fun i j : {i // active i = true} => Disjoint ((a i.val).onSlice c) ((a j.val).onSlice c)) := by
  obtain ⟨α,hα,_⟩ := c.independent
  let z := s ∘ α
  have hz : v ∘ z ∈ c.domain := by
    have eq : v ∘ z = α := funext fun i => DFunLike.congr_fun hs (α i)
    rwa [eq]
  have spec' (i : {i // active i = true}) : c.support ⊆ (a i.val).value.support :=
    fun γ hγ => (spec i.val γ hγ).mpr i.property
  intro i j ne; apply Set.disjoint_left.mpr
  intro b hi hj
  exact Set.disjoint_left.mp (disj (fun eq => ne (Subtype.ext eq)))
    (((a i.val).slice_membership s hs c (spec' i) z hz b).mpr hi)
    (((a j.val).slice_membership s hs c (spec' j) z hz b).mpr hj)

end ChartPiece
end GeneralizedEuler.Section4
