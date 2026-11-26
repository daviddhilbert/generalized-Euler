module

public import Section4.LostCoordinates
import all Section4.LostCoordinates
import all Section4.RelativeResidues

/-! Scalar matrices for the normalized residue comparison, including the
complementary coordinates when a value hull drops rank. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped Matrix
variable {F T : Type*} [Field F] [AddCommGroup T] [Module F T]
  {I H : Type*} [Fintype I]

def readMatrix (p : H → I) : Matrix H I F := by
  classical exact fun h i => if i = p h then 1 else 0

theorem act_read (p : H → I) (x : I → T) : actRows (readMatrix (F := F) p) x = x ∘ p := by
  classical funext j; simp [actRows,readMatrix,ite_smul]

theorem act_sub (a b : Matrix H I F) (x : I → T) : actRows (a-b) x = actRows a x - actRows b x := by
  funext j; simp [actRows,sub_smul,Finset.sum_sub_distrib]

namespace ValueFrame
variable {V : Type*} [AddCommGroup V] [Module F V] {G : Submodule F V} {n r k : ℕ}
  (A : ValueFrame G r n) (B : ValueFrame G k n)

def padMatrix : Matrix (Fin n) A.dependent F := by
  classical exact fun i j => if j.val = i then 1 else 0

theorem act_pad (b : A.dependent → T) : actRows A.padMatrix b = A.padResidue b := by
  classical
  funext i
  by_cases hi : i ∉ Set.range A.free
  · let j : A.dependent := ⟨i,hi⟩
    have cond (u : A.dependent) : u.val = i ↔ u = j := ⟨fun e => Subtype.ext e,fun e => congrArg Subtype.val e⟩
    simp [actRows,padMatrix,padResidue,cond,ite_smul,hi,j]
  · have ne (u : A.dependent) : u.val ≠ i := fun h => hi (h ▸ u.property)
    unfold padResidue
    rw [dite_eq_right hi]
    simp [actRows,padMatrix,ne]

def residueMatrix : Matrix A.dependent (Fin n) F :=
  readMatrix (F := F) (Subtype.val : A.dependent → Fin n) * ((1 : Matrix (Fin n) (Fin n) F) - A.rows * readMatrix A.free)

theorem act_residue (x : Fin n → T) : actRows A.residueMatrix x = A.residuePart x := by
  rw [residueMatrix,actRows_mul,act_read,act_sub,actRows_one,actRows_mul,act_read]; rfl

theorem refinement_matrices (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) :
    ∃ (L : Matrix A.dependent B.dependent F) (N : Matrix (Fin (r-k)) B.dependent F)
      (e : (B.dependent → T) ≃ (A.dependent → T) × (Fin (r-k) → T)),
      (∀ b, e b = (actRows L b,actRows N b)) ∧
      ∀ b, (e b).1 = A.residuePart (B.padResidue b) := by
  classical
  let C := A.projectedRows B
  let j : Fin k ↪ Fin r := Fin.castLEEmb (A.refinement_rank B α hi h)
  let rem := Fintype.equivFinOfCardEq (complement_count j)
  let inj := A.refinement_injective B α hi h
  have pinj : Function.Injective (unitColumns (F := F) j).mulVecLin := by
    intro x y eq
    change actRows (unitColumns (F := F) j) x = actRows (unitColumns (F := F) j) y at eq
    simpa only [unitColumns_free] using congrArg (fun t : Fin r → F => t ∘ j) eq
  let U := (ambient_coordinate_change (unitColumns (F := F) j) C pinj inj).choose
  let q := quotientCoordinates (T := T) C inj j
  let e := (A.relativeResidueEquiv B C (A.refinement_equations B α hi h).1).trans
    (Equiv.prodCongr (Equiv.refl _) (q.trans (Equiv.arrowCongr rem (Equiv.refl T))))
  let rest (i : Fin (r-k)) := (rem.symm i).val
  refine ⟨A.residueMatrix * B.padMatrix,
    readMatrix (F := F) rest * (U.inv * (readMatrix (F := F) A.free * B.padMatrix)),e,?_,fun _ => rfl⟩
  intro b
  apply Prod.ext
  · rw [actRows_mul,A.act_residue,B.act_pad]; rfl
  · change (e b).2 = actRows (readMatrix (F := F) rest * (U.inv * (readMatrix (F := F) A.free * B.padMatrix))) b
    rw [actRows_mul,act_read,actRows_mul,actRows_mul,act_read,B.act_pad]; rfl

end ValueFrame
end GeneralizedEuler.Section4
