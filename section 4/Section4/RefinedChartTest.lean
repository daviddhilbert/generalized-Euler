module

public import Section4.LostCoordinates
import all Section4.RelativeResidues
import all Section4.PositiveRectangles
import all Section4.CellProducts

/-! Restriction to a finer affine value hull pulls the coarse residue condition
back along the first component of the residue refinement equivalence. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueFrame
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {G : Submodule F V}
  {r k n : ℕ} (A : ValueFrame G r n) (B : ValueFrame G k n)

theorem assembled_units (z : Fin r → T) (b : A.dependent → v.ker) :
    splitUnit v s hs ∘ A.assemble v s z b =
      actRows A.rows (splitUnit v s hs ∘ z) + A.padResidue b := by
  have eq : (fun i => s ((v ∘ z) i) + ((splitUnit v s hs ∘ z) i).val) = z := by
    funext i; change s (v (z i)) + (z i - s (v (z i))) = z i; abel
  have h := A.lift_units v s hs (v ∘ z) (splitUnit v s hs ∘ z) b
  rw [eq] at h
  exact h

theorem normalized_is_residuePart (x : Fin n → T) (hx : v ∘ x = A.eval ((v ∘ x) ∘ A.free)) :
    A.normalize v s hs x hx = A.residuePart (splitUnit v s hs ∘ x) := by
  let b := A.normalize v s hs x hx
  have eq : A.assemble v s (x ∘ A.free) b = x := A.assemble_normalize v s hs x hx
  conv_rhs => rw [← eq,A.assembled_units v s hs,add_comm,A.residuePart_direction,A.residuePart_pad]

theorem refine_normalization (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) (z : Fin k → T) (b : B.dependent → v.ker) :
    A.residuePart (splitUnit v s hs ∘ B.assemble v s z b) = A.residuePart (B.padResidue b) := by
  rw [B.assembled_units v s hs,(A.refinement_equations B α hi h).1,actRows_mul,add_comm,
    A.residuePart_direction]

include hs in
/-- Membership after refinement uses only the fine residue coordinate. In
particular the new free RV representatives may vary throughout their fibers. -/
theorem refine_membership (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) (U : Set (Fin n → T)) (D : Set (Fin r → V))
    (R : Set (A.dependent → v.ker))
    (chart : ∀ z, v ∘ z ∈ D → ∀ b, A.assemble v s z b ∈ U ↔ b ∈ R)
    (z : Fin k → T) (hz : B.eval (v ∘ z) ∘ A.free ∈ D) (b : B.dependent → v.ker) :
    B.assemble v s z b ∈ U ↔ A.residuePart (B.padResidue b) ∈ R := by
  let x := B.assemble v s z b
  have value : v ∘ x = B.eval (v ∘ z) := B.assemble_value v s hs z b
  have hull : v ∘ x = A.eval ((v ∘ x) ∘ A.free) := by
    rw [value]; exact (A.refinement_hull B α hi h _).symm
  have member : v ∘ (x ∘ A.free) ∈ D := by change (v ∘ x) ∘ A.free ∈ D; rwa [value]
  have test := chart (x ∘ A.free) member (A.normalize v s hs x hull)
  rw [A.assemble_normalize,A.normalized_is_residuePart v s hs x hull] at test
  exact test.trans (congrArg (· ∈ R) (A.refine_normalization v s hs B α hi h z b)).to_iff

end GeneralizedEuler.Section4.ValueFrame
