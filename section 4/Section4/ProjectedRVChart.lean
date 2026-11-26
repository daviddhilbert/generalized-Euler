module

public import Section4.ProjectedValuePiece
public import Section4.RefinedChartTest
import all Section4.ProjectedFrame
import all Section4.PositiveRectangles
import all Section4.RelativeResidues
import all Section4.GraphProjection

/-! The projection of an assembled graph rectangle has a free tuple and
a normalized residue tuple. At fixed residue the free tuple runs over the
entire projected value pullback. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ProjectionBasis
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {G : Submodule F V}
  {k n r : ℕ} {A : ValueFrame G r n} {p : Fin k → Fin n} (q : ProjectionBasis A p)

def projectResidues (b : A.dependent → v.ker) := q.frame.residuePart (A.padResidue b ∘ p)
def projectFree (z : Fin r → T) (b : A.dependent → v.ker) := A.assemble v s z b ∘ p ∘ q.free

theorem directions_mul : q.frame.rows * q.minor.val = A.projectedDirections p := by
  change (A.projectedDirections p * q.minor.inv) * q.minor.val = _
  rw [Matrix.mul_assoc,q.minor.inv_val,Matrix.mul_one]

include hs in
theorem projectFree_value (z : Fin r → T) (b : A.dependent → v.ker) :
    v ∘ q.projectFree v s z b = q.forward (v ∘ z) := by
  rw [q.forward_eq]
  exact congrArg (fun x : Fin n → V => x ∘ p ∘ q.free) (A.assemble_value v s hs z b)

theorem projectFree_bijective (b : A.dependent → v.ker) : Function.Bijective (fun z => q.projectFree v s z b) := by
  let c := (s ∘ (fun i => (q.offset i).val)) + (fun i => (A.padResidue b (p (q.free i))).val)
  have eq (z : Fin r → T) : q.projectFree v s z b = actRows q.minor.val z + c := by
    funext i
    change (∑ j, A.rows (p (q.free i)) j • z j) + s _ + _ =
      (∑ j, q.minor.val i j • z j) + (_ + _)
    rw [q.rows i,add_assoc]; rfl
  let rev (y : Fin r → T) := actRows q.minor.inv (y-c)
  have left (z) : rev (q.projectFree v s z b) = z := by
    unfold rev; rw [eq,add_sub_cancel_right,← actRows_mul,q.minor.inv_val,actRows_one]
  refine ⟨Function.LeftInverse.injective left,fun y => ⟨rev y,?_⟩⟩
  change q.projectFree v s (rev y) b = y
  rw [eq]; unfold rev; rw [← actRows_mul,q.minor.val_inv,actRows_one,sub_add_cancel]

include hs in
theorem project_assembled (z : Fin r → T) (b : A.dependent → v.ker) :
    A.assemble v s z b ∘ p = q.frame.assemble v s (q.projectFree v s z b) (q.projectResidues v b) := by
  let x := A.assemble v s z b ∘ p
  have val : v ∘ x = q.frame.eval (q.forward (v ∘ z)) :=
    (congrArg (· ∘ p) (A.assemble_value v s hs z b)).trans (q.project_eval _).symm
  have hull : v ∘ x = q.frame.eval ((v ∘ x) ∘ q.frame.free) := by
    rw [val,q.frame.project_eval]
  have units : splitUnit v s hs ∘ x =
      actRows (A.projectedDirections p) (splitUnit v s hs ∘ z) + (A.padResidue b ∘ p) :=
    congrArg (· ∘ p) (A.assembled_units v s hs z b)
  have norm : q.frame.normalize v s hs x hull = q.projectResidues v b := by
    rw [q.frame.normalized_is_residuePart v s hs x hull,units,← q.directions_mul,actRows_mul,add_comm,
      q.frame.residuePart_direction]; rfl
  have eq := q.frame.assemble_normalize v s hs x hull
  rw [norm] at eq; exact eq.symm

include hs in
theorem projection_rectangle (D : Set (Fin r → V)) (R : Set (A.dependent → v.ker)) :
    (fun x : Fin n → T => x ∘ p) ''
      ((fun w => A.assemble v s w.1 w.2) '' ({z | v ∘ z ∈ D} ×ˢ R)) =
    (fun w => q.frame.assemble v s w.1 w.2) ''
      ({z | v ∘ z ∈ q.forward '' D} ×ˢ (q.projectResidues v '' R)) := by
  ext x; constructor
  · rintro ⟨_,⟨⟨z,b⟩,⟨hz,hb⟩,rfl⟩,rfl⟩
    exact ⟨(q.projectFree v s z b,q.projectResidues v b),⟨⟨v ∘ z,hz,(q.projectFree_value v s hs z b).symm⟩,b,hb,rfl⟩,(q.project_assembled v s hs z b).symm⟩
  · rintro ⟨⟨y,_⟩,⟨⟨γ,hγ,eq⟩,b,hb,rfl⟩,rfl⟩
    obtain ⟨z,rfl⟩ := (q.projectFree_bijective v s b).2 y
    have zeq : γ = v ∘ z := q.forward_bijective.1 (eq.trans (q.projectFree_value v s hs z b))
    exact ⟨_,⟨(z,b),⟨show v ∘ z ∈ D from zeq ▸ hγ,hb⟩,rfl⟩,q.project_assembled v s hs z b⟩

end GeneralizedEuler.Section4.ProjectionBasis
