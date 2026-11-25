module

public import Section2.SortedQE

/-! Quantification over a finite tuple of the same sort. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w a z

abbrev AddSortedBlock (Var : TCsort → Type a) (s : TCsort) (n : ℕ) (t : TCsort) :=
  Var t ⊕ (Fin n × PLift (s = t))

@[expose]
def appendSortedBlock {Var : TCsort → Type a} {X : TCsort → Type z} {s : TCsort} {n : ℕ}
    (v : ∀ t, Var t → X t) (x : Fin n → X s) (t : TCsort) : AddSortedBlock Var s n t → X t
  | .inl i => v t i
  | .inr ⟨j, ⟨h⟩⟩ => h ▸ x j

namespace SortedFormula

variable {L : Language.{u, v}} {E : Type w} {Var : TCsort → Type a}

private def splitBlockLast (s : TCsort) (n : ℕ) (t : TCsort) :
    AddSortedBlock Var s (n + 1) t → AddSortedVar (AddSortedBlock Var s n) s t
  | .inl i => .inl (.inl i)
  | .inr ⟨j, h⟩ => Fin.lastCases (.inr h) (fun i => .inl (.inr ⟨i, h⟩)) j

/-- Universal quantification over a tuple of a single sort. -/
def allBlock (s : TCsort) :
    (n : ℕ) → SortedFormula L E (AddSortedBlock Var s n) → SortedFormula L E Var
  | 0, φ => φ.relabel (fun _ => Sum.elim id (fun j => j.1.elim0))
  | n + 1, φ => allBlock s n (.all s (φ.relabel (splitBlockLast s n)))

theorem realize_allBlock {X : TCsort → Type z} (M : SortedStructure L E X) (s : TCsort)
    {n : ℕ} (φ : SortedFormula L E (AddSortedBlock Var s n)) (v : ∀ t, Var t → X t) :
    (φ.allBlock s n).realize M v ↔ ∀ x : Fin n → X s, φ.realize M (appendSortedBlock v x) := by
  induction n with
  | zero =>
    rw [allBlock, φ.realize_relabel]
    have eq (x : Fin 0 → X s) :
        (fun t => v t ∘ Sum.elim id (fun j : Fin 0 × PLift (s = t) => j.1.elim0)) =
          appendSortedBlock v x := by
      funext t i
      cases i with
      | inl i => rfl
      | inr i => exact i.1.elim0
    exact ⟨fun h x => eq x ▸ h, fun h => (eq Fin.elim0).symm ▸ h Fin.elim0⟩
  | succ n ih =>
    rw [allBlock, ih]
    have eq (x : Fin n → X s) (y : X s) :
        (fun t => extendSortedAssignment (appendSortedBlock v x) y t ∘ splitBlockLast s n t) =
          appendSortedBlock v (Fin.snoc x y) := by
      funext t i
      rcases i with i | ⟨i, h⟩
      · rfl
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rcases h with ⟨h⟩
          subst t
          simp [splitBlockLast, appendSortedBlock, extendSortedAssignment]
        · rcases h with ⟨h⟩
          subst t
          simp [splitBlockLast, appendSortedBlock, extendSortedAssignment]
    simp only [SortedFormula.realize, SortedFormula.realize_relabel, eq]
    constructor
    · intro h x
      simpa only [Fin.snoc_init_self] using h (Fin.init x) (x (Fin.last n))
    · intro h x y
      exact h (Fin.snoc x y)

/-- Existential quantification over a tuple of a single sort. -/
def exBlock (s : TCsort) (n : ℕ) (φ : SortedFormula L E (AddSortedBlock Var s n)) :
    SortedFormula L E Var := (φ.neg.allBlock s n).neg

theorem realize_exBlock {X : TCsort → Type z} (M : SortedStructure L E X) (s : TCsort)
    {n : ℕ} (φ : SortedFormula L E (AddSortedBlock Var s n)) (v : ∀ t, Var t → X t) :
    (φ.exBlock s n).realize M v ↔ ∃ x : Fin n → X s, φ.realize M (appendSortedBlock v x) := by
  classical
  simp only [exBlock, realize_neg, realize_allBlock, not_forall, not_not]

end SortedFormula

end GeneralizedEuler.Section2
