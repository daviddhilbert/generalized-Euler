module

public import Section4.LostCoordinates
public import Mathlib.LinearAlgebra.Matrix.ToLin
import all Section4.PositiveRectangles
import all Section4.RelativeResidues

/-! The two projections of a graph chart retain its full value rank and,
after removing the projected free directions, preserve its residue class. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F T] (v : T →ₗ[F] V) (s : V →ₗ[F] T)
  {G : Submodule F V} {r n k : ℕ} (A : ValueFrame G r n) (p : Fin k → Fin n)

namespace ValueFrame
def projectedDirections : Matrix (Fin k) (Fin r) F := fun i : Fin k => A.rows (p i)

theorem assemble_add (z d : Fin r → T) (b : A.dependent → v.ker) :
    A.assemble v s (z+d) b = A.assemble v s z b + actRows A.rows d := by
  funext i
  change actRows A.rows (z+d) i + _ + _ = (_ + _ + _) + _
  rw [show actRows A.rows (z+d) = actRows A.rows z + actRows A.rows d from (rowsLinear A.rows).map_add z d]
  simp only [Pi.add_apply]; abel

def graphResidue (b : A.dependent → v.ker) :
    (Fin k → v.ker) ⧸ LinearMap.range (rowsLinear (T := v.ker) (A.projectedDirections p)) :=
  (LinearMap.range (rowsLinear (T := v.ker) (A.projectedDirections p))).mkQ (A.extendResidues v b ∘ p)

variable (D : Set (Fin r → V)) (B : Set (A.dependent → v.ker))
  (inj : Set.InjOn (fun x : Fin n → T => x ∘ p)
    ((fun t : (Fin r → T) × (A.dependent → v.ker) => A.assemble v s t.1 t.2) ''
      ({z | v ∘ z ∈ D} ×ˢ B)))
include inj

theorem graph_full_rank (z : Fin r → T) (hz : v ∘ z ∈ D) (b : A.dependent → v.ker) (hb : b ∈ B)
    (d : v.ker) (hd : d ≠ 0) : Function.Injective (A.projectedDirections p).mulVecLin := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  let t (i : Fin r) := w i • d.val
  have ht : v ∘ (z+t) = v ∘ z := by funext i; simp [t]
  have dir : actRows A.rows t ∘ p = 0 := by
    funext i
    change ∑ j, A.rows (p i) j • (w j • d.val) = 0
    simp only [smul_smul,← Finset.sum_smul]
    change ((A.projectedDirections p).mulVecLin w i) • d.val = 0
    rw [hw]; simp
  have matchP : A.assemble v s (z+t) b ∘ p = A.assemble v s z b ∘ p := by
    rw [A.assemble_add]
    change _ + (actRows A.rows t ∘ p) = _; rw [dir,add_zero]; rfl
  have eq := inj (x₁ := A.assemble v s (z+t) b) (x₂ := A.assemble v s z b)
    ⟨(z+t,b),⟨show v ∘ (z+t) ∈ D from ht.symm ▸ hz,hb⟩,rfl⟩ ⟨(z,b),⟨hz,hb⟩,rfl⟩ matchP
  have free := congrArg (fun x : Fin n → T => x ∘ A.free) eq
  change A.assemble v s (z+t) b ∘ A.free = A.assemble v s z b ∘ A.free at free
  rw [A.assemble_free,A.assemble_free] at free
  have zt : t = 0 := add_eq_left.mp free
  have nz : d.val ≠ 0 := fun h => hd (Subtype.ext h)
  exact funext fun i => (smul_eq_zero.mp (congrFun zt i)).resolve_right nz

theorem graph_residue_injective (z : Fin r → T) (hz : v ∘ z ∈ D) :
    Set.InjOn (A.graphResidue v p) B := by
  intro b hb c hc eq
  let W := LinearMap.range (rowsLinear (T := v.ker) (A.projectedDirections p))
  have q : W.mkQ (A.extendResidues v b ∘ p - A.extendResidues v c ∘ p) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr eq
  obtain ⟨d,hd⟩ := (Submodule.Quotient.mk_eq_zero W).mp q
  let t (i) := (d i).val
  have ht : v ∘ (z+t) = v ∘ z := by funext i; simp [t]
  have matchP : A.assemble v s (z+t) c ∘ p = A.assemble v s z b ∘ p := by
    rw [A.assemble_add]; funext i
    have hi := congrArg Subtype.val (congrFun hd i)
    change (actRows (A.projectedDirections p) d i).val =
      (A.extendResidues v b (p i)).val - (A.extendResidues v c (p i)).val at hi
    have hm := congrFun (actRows_map v.ker.subtype (A.projectedDirections p) d) i
    change (actRows (A.projectedDirections p) d i).val = actRows A.rows t (p i) at hm
    change A.lift s z (p i) + _ + actRows A.rows t (p i) = A.lift s z (p i) + _
    rw [← hm,hi]; abel
  have same := inj (x₁ := A.assemble v s (z+t) c) (x₂ := A.assemble v s z b)
    ⟨(z+t,c),⟨show v ∘ (z+t) ∈ D from ht.symm ▸ hz,hc⟩,rfl⟩ ⟨(z,b),⟨hz,hb⟩,rfl⟩ matchP
  have both := A.assemble_injective v s (a₁ := (z+t,c)) (a₂ := (z,b)) same
  exact (congrArg Prod.snd both).symm

end ValueFrame
end GeneralizedEuler.Section4
