module

public import Section2.SortedQuantifierBlock
public import Section2.SortedDefinability

/-! Fixed-base projection of a finite mixed tuple. This is used when
composing the graphs of successive coordinate preparations. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

abbrev SortedAssignment (X : TCsort → Type z) (V : TCsort → Type) := ∀ s, V s → X s
abbrev SumVariables (V W : TCsort → Type) (s : TCsort) := V s ⊕ W s

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {A : ∀ s, Set (X s)} {V W : TCsort → Type}

theorem definable_project_block (s : TCsort) {n : ℕ}
    {D : Set (SortedAssignment X (AddSortedBlock V s n))}
    (hD : SortedDefinableOver M A D) :
    SortedDefinableOver M A {x | ∃ y : Fin n → X s, appendSortedBlock x y ∈ D} := by
  obtain ⟨φ, hφ⟩ := hD
  let rename (t : TCsort) :
      (A t : Type z) ⊕ AddSortedBlock V s n t →
      AddSortedBlock (fun t => (A t : Type z) ⊕ V t) s n t
    | .inl c => .inl (.inl c)
    | .inr (.inl i) => .inl (.inr i)
    | .inr (.inr j) => .inr j
  refine ⟨(φ.relabel rename).exBlock s n, fun x => ?_⟩
  rw [SortedFormula.realize_exBlock]
  apply exists_congr
  intro y
  rw [SortedFormula.realize_relabel]
  have he (v : SortedAssignment X (AddSortedBlock V s n)) :=
    hφ v
  have ea : (fun t => appendSortedBlock (fun t => Sum.elim Subtype.val (x t)) y t ∘ rename t) =
      (fun t => Sum.elim Subtype.val (appendSortedBlock x y t)) := by
    funext t i
    rcases i with c | (i | j) <;> rfl
  rw [ea]
  exact he _

/-- Eliminate any finite block described by its own VF and RV index
types, leaving all original parameters and other variables in place. -/
theorem definable_project_mixed [Finite (W .vf)] [Finite (W .rv)]
    {D : Set (SortedAssignment X (SumVariables V W))}
    (hD : SortedDefinableOver M A D) :
    SortedDefinableOver M A
      {x | ∃ y : SortedAssignment X W, (fun s => Sum.elim (x s) (y s)) ∈ D} := by
  classical
  let := Fintype.ofFinite (W .vf)
  let := Fintype.ofFinite (W .rv)
  let n := Fintype.card (W .vf)
  let m := Fintype.card (W .rv)
  let e : W .vf ≃ Fin n := Fintype.equivFin (W .vf)
  let f : W .rv ≃ Fin m := Fintype.equivFin (W .rv)
  let VF := AddSortedBlock V .vf n
  let Both := AddSortedBlock VF .rv m
  let rename : ∀ s, SumVariables V W s → Both s
    | .vf => Sum.elim (fun j => .inl (.inl j)) (fun i => .inl (.inr ⟨e i, ⟨rfl⟩⟩))
    | .rv => Sum.elim (fun j => .inl (.inl j)) (fun i => .inr ⟨f i, ⟨rfl⟩⟩)
  have h := definable_project_block .vf (definable_project_block .rv (hD.pullback_relabel rename))
  convert h using 1
  ext x
  let atTuple (y : Fin n → X .vf) (z : Fin m → X .rv) : SortedAssignment X W
    | .vf => y ∘ e
    | .rv => z ∘ f
  have he (y : Fin n → X .vf) (z : Fin m → X .rv) :
      (fun s => appendSortedBlock (appendSortedBlock x y) z s ∘ rename s) =
        (fun s => Sum.elim (x s) (atTuple y z s)) := by
    funext s i
    cases s <;> cases i <;> rfl
  change (∃ y : SortedAssignment X W, (fun s => Sum.elim (x s) (y s)) ∈ D) ↔
    ∃ y : Fin n → X .vf, ∃ z : Fin m → X .rv,
      (fun s => appendSortedBlock (appendSortedBlock x y) z s ∘ rename s) ∈ D
  simp only [he]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y .vf ∘ e.symm, y .rv ∘ f.symm, ?_⟩
    have eq : atTuple (y .vf ∘ e.symm) (y .rv ∘ f.symm) = y := by
      funext s i
      cases s with
      | vf => exact congrArg (y .vf) (e.symm_apply_apply i)
      | rv => exact congrArg (y .rv) (f.symm_apply_apply i)
    rwa [eq]
  · rintro ⟨y,z,h⟩
    exact ⟨atTuple y z, h⟩

end GeneralizedEuler.Section5
