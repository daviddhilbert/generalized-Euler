module

public import Section4.ChartTransitions

/-! Affine coordinate frames over a fixed value subspace. Elimination of
a pivot remembers which original coordinates survive. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped BigOperators
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (G : Submodule F V)

/-- All intercepts belong to the original value subspace. -/
structure ValueFrame (r n : ℕ) where
  free : Fin r ↪ Fin n
  rows : Matrix (Fin n) (Fin r) F
  shift : Fin n → G
  freeRow : ∀ i j, rows (free i) j = if i = j then 1 else 0
  freeShift : ∀ i, shift (free i) = 0

namespace ValueFrame
variable {G} {r m n : ℕ}

def eval (A : ValueFrame G r n) (z : Fin r → V) : Fin n → V :=
  actRows A.rows z + fun i => (A.shift i).val

theorem project_eval (A : ValueFrame G r n) (z : Fin r → V) : A.eval z ∘ A.free = z := by
  classical
  funext i
  simp [eval,actRows,A.freeRow,A.freeShift,ite_smul]

theorem injective (A : ValueFrame G r n) : Function.Injective A.eval := by
  intro x y h
  simpa [A.project_eval] using congrArg (fun z : Fin n → V => z ∘ A.free) h

def identity (n : ℕ) : ValueFrame G n n where
  free := Function.Embedding.refl _
  rows := 1
  shift := 0
  freeRow _ _ := rfl
  freeShift _ := rfl

@[simp] theorem identity_eval (z : Fin n → V) : (identity (G := G) n).eval z = z := by
  simp [identity,eval,actRows_one]; rfl

def comp (A : ValueFrame G m n) (B : ValueFrame G r m) : ValueFrame G r n where
  free := B.free.trans A.free
  rows := A.rows * B.rows
  shift := actRows A.rows B.shift + A.shift
  freeRow := by
    intro i j; change ∑ k, A.rows (A.free (B.free i)) k * B.rows k j = _
    simp [A.freeRow,B.freeRow,ite_mul]
  freeShift := by
    intro i
    simp [Function.Embedding.trans_apply,actRows,A.freeRow,B.freeShift,A.freeShift,ite_smul]

theorem comp_eval (A : ValueFrame G m n) (B : ValueFrame G r m) (z : Fin r → V) :
    (A.comp B).eval z = A.eval (B.eval z) := by
  funext i
  simp only [comp,eval,actRows_mul,Pi.add_apply,Submodule.coe_add]
  have shift := congrFun (actRows_map G.subtype A.rows B.shift) i
  change (actRows A.rows B.shift i).val = actRows A.rows (fun k => (B.shift k).val) i at shift
  rw [shift]
  simp [actRows,smul_add,Finset.sum_add_distrib,add_assoc]

end ValueFrame

structure ValuePivot (n : ℕ) where
  index : Fin (n+1)
  coefficients : Fin n → F
  offset : G

namespace ValuePivot
variable {G} {n : ℕ}
def frame (p : ValuePivot G n) : ValueFrame G n (n+1) where
  free := p.index.succAboveEmb
  rows := p.index.insertNth p.coefficients (1 : Matrix (Fin n) (Fin n) F)
  shift := p.index.insertNth p.offset 0
  freeRow i j := by
    have e := Fin.insertNth_apply_succAbove (α := fun _ => Fin n → F) p.index p.coefficients
      (1 : Matrix (Fin n) (Fin n) F) i
    exact (congrFun e j).trans Matrix.one_apply
  freeShift i := by simp

theorem mem_range (p : ValuePivot G n) (x : Fin (n+1) → V) :
    x ∈ Set.range p.frame.eval ↔ x p.index =
      (∑ i, p.coefficients i • x (p.index.succAbove i)) + p.offset.val := by
  have pivot (z : Fin n → V) : p.frame.eval z p.index = _ :=
    show p.frame.eval z p.index = (∑ i, p.coefficients i • z i) + p.offset.val by
      have e := Fin.insertNth_apply_same (α := fun _ => Fin n → F) p.index p.coefficients
        (1 : Matrix (Fin n) (Fin n) F)
      simp [ValueFrame.eval,frame,actRows,e]
  constructor
  · rintro ⟨z,rfl⟩
    rw [pivot]
    exact congrArg (fun y : Fin n → V => (∑ i, p.coefficients i • y i) + p.offset.val)
      (p.frame.project_eval z).symm
  · intro h
    refine ⟨p.index.removeNth x,funext (p.index.forall_iff_succAbove.mpr ⟨?_,?_⟩)⟩
    · exact (pivot _).trans h.symm
    · intro j; exact congrFun (p.frame.project_eval _) j

end ValuePivot
end GeneralizedEuler.Section4
