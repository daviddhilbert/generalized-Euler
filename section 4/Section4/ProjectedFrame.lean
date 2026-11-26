module

public import Section4.ProjectionMinor
import all Section4.ValueFrames
import all Section4.GraphProjection
import all Section4.RelativeResidues

/-! Value frames on the source or target projection of a graph rectangle. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {G : Submodule F V}
  {r k n : ℕ} (A : ValueFrame G r n) (p : Fin k → Fin n)

structure ProjectionBasis (A : ValueFrame G r n) (p : Fin k → Fin n) where
  free : Fin r ↪ Fin k
  minor : (Matrix (Fin r) (Fin r) F)ˣ
  rows : ∀ i, minor.val i = A.rows (p (free i))

namespace ProjectionBasis
variable {A p} (q : ProjectionBasis A p)

def offset := A.shift ∘ p ∘ q.free
def directions : Matrix (Fin k) (Fin r) F := A.projectedDirections p * q.minor.inv

theorem directions_free (i j : Fin r) : q.directions (q.free i) j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  change ∑ l, A.rows (p (q.free i)) l * q.minor.inv l j = _
  rw [← q.rows i]; exact congrFun (congrFun q.minor.val_inv i) j

def frame : ValueFrame G r k where
  free := q.free
  rows := q.directions
  shift := A.shift ∘ p - actRows q.directions q.offset
  freeRow := q.directions_free
  freeShift i := by
    change A.shift (p (q.free i)) - ∑ j, q.directions (q.free i) j • q.offset j = 0
    simp [q.directions_free,Matrix.one_apply,ite_smul,offset,Function.comp_def]

def forward (z : Fin r → V) := actRows q.minor.val z + fun i => (q.offset i).val

theorem forward_eq (z : Fin r → V) : q.forward z = A.eval z ∘ p ∘ q.free := by
  funext i; change (∑ j, q.minor.val i j • z j) + _ = (∑ j, A.rows (p (q.free i)) j • z j) + _
  rw [q.rows i]; rfl

theorem forward_bijective : Function.Bijective q.forward := by
  let rev (z : Fin r → V) := actRows q.minor.inv (z - fun i => (q.offset i).val)
  have back (z) : rev (q.forward z) = z := by
    unfold rev forward; rw [add_sub_cancel_right,← actRows_mul,q.minor.inv_val,actRows_one]
  refine ⟨Function.LeftInverse.injective back,fun z => ⟨rev z,?_⟩⟩
  unfold rev forward; rw [← actRows_mul,q.minor.val_inv,actRows_one,sub_add_cancel]

theorem project_eval (z : Fin r → V) : q.frame.eval (q.forward z) = A.eval z ∘ p := by
  have mul : q.directions * q.minor.val = A.projectedDirections p := by
    unfold directions; rw [Matrix.mul_assoc,q.minor.inv_val,Matrix.mul_one]
  have val := actRows_map G.subtype q.directions q.offset
  change actRows q.directions (actRows q.minor.val z + fun i => (q.offset i).val) +
    (fun i => (A.shift (p i) - actRows q.directions q.offset i : G).val) = _
  rw [show actRows q.directions (actRows q.minor.val z + fun i => (q.offset i).val) =
      actRows q.directions (actRows q.minor.val z) + actRows q.directions (fun i => (q.offset i).val) from
    (rowsLinear q.directions).map_add _ _,← actRows_mul,mul]
  funext i
  change (actRows (A.projectedDirections p) z i + actRows q.directions (G.subtype ∘ q.offset) i) +
    ((A.shift (p i)).val - (actRows q.directions q.offset i).val) = actRows A.rows z (p i) + _
  rw [← congrFun val i]
  change (actRows (A.projectedDirections p) z i + (actRows q.directions q.offset i).val) +
    ((A.shift (p i)).val - (actRows q.directions q.offset i).val) = actRows (A.projectedDirections p) z i + (A.shift (p i)).val
  abel

end ProjectionBasis
end GeneralizedEuler.Section4
