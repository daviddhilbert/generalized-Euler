module

public import Section4.GraphCharts

/-! Independence of normalized residue coordinates under a change of free
coordinates or intercept representatives in 4.20. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F T : Type*} [Field F] [AddCommGroup T] [Module F T]
variable {i j i' j' : Type*} [Fintype i] [Fintype i']
open scoped BigOperators

def normalizeRows (A : Matrix j i F) (u : j → T) (x : i ⊕ j → T) (k : j) : T :=
  x (.inr k) - (actRows A (x ∘ Sum.inl) k + u k)

theorem normalize_chartPoint (A : Matrix j i F) (u b : j → T) (z : i → T) :
    normalizeRows A u (chartPoint A u z b) = b := by
  funext k
  change b k + actRows A z k + u k - (actRows A z k + u k) = b k
  abel

theorem reconstruct_chartPoint (A : Matrix j i F) (u : j → T) (x : i ⊕ j → T) :
    chartPoint A u (x ∘ Sum.inl) (normalizeRows A u x) = x := by
  funext k
  cases k with
  | inl => rfl
  | inr k =>
    change x (.inr k) - (_ + _) + _ + _ = x (.inr k)
    abel

def directionRows (A : Matrix j i F) : Matrix (i ⊕ j) i F :=
  by classical exact fun k => Sum.elim (fun a b => if a = b then 1 else 0) (fun a => A a) k

theorem chartPoint_split (A : Matrix j i F) (u b : j → T) (z : i → T) :
    chartPoint A u z b = chartPoint A u 0 b + actRows (directionRows A) z := by
  classical
  funext k
  cases k with
  | inl k => simp [chartPoint,directionRows,actRows,ite_smul]
  | inr k =>
    simp only [chartPoint,Pi.add_apply,Sum.elim_inr,actRows,Pi.zero_apply,smul_zero,
      Finset.sum_const_zero,add_zero,directionRows]
    abel

/-- The new rows annihilate the old free directions. The transition can
therefore be evaluated at the zero free tuple, outside the cell if necessary. -/
theorem transition_independent (A : Matrix j i F) (A' : Matrix j' i' F)
    (p : i' ⊕ j' → i ⊕ j) (u : j → T) (u' : j' → T)
    (directions : (fun k l => directionRows A (p (.inr k)) l) =
      A' * (show Matrix i' i F from fun k l => directionRows A (p (.inl k)) l))
    (z : i → T) (b : j → T) :
    normalizeRows A' u' (chartPoint A u z b ∘ p) =
    normalizeRows A' u' (chartPoint A u 0 b ∘ p) := by
  rw [chartPoint_split A u b z]
  let x := chartPoint A u 0 b
  let B : Matrix i' i F := fun k l => directionRows A (p (.inl k)) l
  let C : Matrix j' i F := fun k l => directionRows A (p (.inr k)) l
  have eq : actRows C z = actRows A' (actRows B z) := by rw [← actRows_mul]; exact congrArg (actRows · z) directions
  have distribution : actRows A' (fun k => x (p (.inl k)) + actRows B z k) =
      actRows A' (fun k => x (p (.inl k))) + actRows A' (actRows B z) := by
    funext k; simp [actRows,smul_add,Finset.sum_add_distrib]
  funext k
  change x (p (.inr k)) + actRows C z k - (actRows A' (fun l => x (p (.inl l)) + actRows B z l) k + u' k) =
    x (p (.inr k)) - (actRows A' (fun l => x (p (.inl l))) k + u' k)
  rw [distribution,eq,Pi.add_apply]
  abel

/-- A transition that descends on both residue sets is a bijection. Only
one representative of each residue point is used, with no definable choice. -/
def residueTransitionEquiv {X B C : Type*} (y : X → B) (z : X → C)
    (hy : Function.Surjective y) (hz : Function.Surjective z)
    (p : B → C) (q : C → B) (hp : ∀ x, p (y x) = z x) (hq : ∀ x, q (z x) = y x) : B ≃ C where
  toFun := p
  invFun := q
  left_inv b := by obtain ⟨x,rfl⟩ := hy b; rw [hp,hq]
  right_inv c := by obtain ⟨x,rfl⟩ := hz c; rw [hq,hp]

end GeneralizedEuler.Section4
