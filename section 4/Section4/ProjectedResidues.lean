module

public import Section4.ProjectedRVChart
public import Section4.ResidueMatrices
import all Section4.ProjectedRVChart
import all Section4.PositiveRectangles
import all Section4.ResidueMatrices

/-! An injective projection of a nonempty graph chart restricts to a monomial
injection on its normalized residue factor. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ProjectionBasis
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {G : Submodule F V}
  {k n r : ℕ} {A : ValueFrame G r n} {p : Fin k → Fin n} (q : ProjectionBasis A p)

def projectionMatrix := q.frame.residueMatrix * (readMatrix (F := F) p * A.padMatrix)

theorem projectResidues_eq (b : A.dependent → v.ker) :
    q.projectResidues v b = actRows q.projectionMatrix b := by
  rw [projectionMatrix,actRows_mul,q.frame.act_residue,actRows_mul,act_read,A.act_pad]
  rfl

include hs in
theorem projectResidues_injOn (D : Set (Fin r → V)) (hD : D.Nonempty) (R : Set (A.dependent → v.ker))
    (inj : Set.InjOn (fun x : Fin n → T => x ∘ p)
      ((fun w => A.assemble v s w.1 w.2) '' ({z | v ∘ z ∈ D} ×ˢ R))) :
    Set.InjOn (q.projectResidues v) R := by
  intro b hb c hc eq
  obtain ⟨α,hα⟩ := hD
  let z := s ∘ α
  have hz : v ∘ z = α := funext fun i => DFunLike.congr_fun hs (α i)
  obtain ⟨w,hw⟩ := (q.projectFree_bijective v s c).2 (q.projectFree v s z b)
  change q.projectFree v s w c = q.projectFree v s z b at hw
  have val : v ∘ w = v ∘ z := q.forward_bijective.1
    (((q.projectFree_value v s hs w c).symm.trans (congrArg (v ∘ ·) hw)).trans (q.projectFree_value v s hs z b))
  have same : A.assemble v s z b ∘ p = A.assemble v s w c ∘ p := by
    rw [q.project_assembled v s hs z b,q.project_assembled v s hs w c,hw,eq]
  have point := inj (show A.assemble v s z b ∈ _ from ⟨(z,b),⟨show v ∘ z ∈ D by rwa [hz],hb⟩,rfl⟩)
    (show A.assemble v s w c ∈ _ from ⟨(w,c),⟨show v ∘ w ∈ D by rwa [val,hz],hc⟩,rfl⟩) same
  exact congrArg Prod.snd (A.assemble_injective v s (a₁ := (z,b)) (a₂ := (w,c)) point)

end GeneralizedEuler.Section4.ProjectionBasis
