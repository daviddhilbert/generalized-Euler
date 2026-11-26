module

public import Section5.GeneratedParameterSchemes
public import Section5.LiftBoundaryDimension

/-! Naming a tuple in stages generates the same fixed base as
naming all its coordinates together. The identity keeps both sorts
of the original base, including its RV parameters. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe u v z

variable {L : Language} {E : Type*} {X : TCsort → Type z} {M : SortedStructure L E X}

theorem sortedSubstructure_eq_of_carriers {A B : SortedSubstructure M}
    (h : ∀ s, A.carrier s = B.carrier s) : A = B := by
  have eq := funext h
  cases A
  cases B
  cases eq
  rfl

theorem termGenerated_carrier_subset_of_generators {P : TCsort → Type u}
    (V : SortedSubstructure M) (x : ∀ s, P s → X s)
    (h : ∀ s i, x s i ∈ V.carrier s) : ∀ s, (M.termGenerated x).carrier s ⊆ V.carrier s :=
  M.termGenerated_le V (fun s i => ⟨x s i,h s i⟩)

theorem termGenerated_eq_of_generator_relabel {P : TCsort → Type u} {Q : TCsort → Type v}
    (x : ∀ s, P s → X s) (y : ∀ s, Q s → X s)
    (f : ∀ s, P s → Q s) (g : ∀ s, Q s → P s)
    (hf : ∀ s i, x s i = y s (f s i)) (hg : ∀ s j, y s j = x s (g s j)) :
    M.termGenerated x = M.termGenerated y := by
  apply sortedSubstructure_eq_of_carriers
  intro s
  apply Set.Subset.antisymm
  · apply termGenerated_carrier_subset_of_generators _ x _ s
    intro t i
    rw [hf]
    exact (M.termGeneratedAssignment y t (f t i)).property
  · apply termGenerated_carrier_subset_of_generators _ y _ s
    intro t j
    rw [hg]
    exact (M.termGeneratedAssignment x t (g t j)).property

theorem generated_base_append {P Q : TCsort → Type}
    (S : SortedSubstructure M) (p : SortedAssignment X P) (q : SortedAssignment X Q) :
    M.termGenerated (namedTuple (M.termGenerated (namedTuple S p)) q) =
      M.termGenerated (namedTuple S (appendAssignments p q)) := by
  let T := M.termGenerated (namedTuple S p)
  let U := M.termGenerated (namedTuple T q)
  let V := M.termGenerated (namedTuple S (appendAssignments p q))
  have subsetTV : ∀ s, T.carrier s ⊆ V.carrier s := by
    apply termGenerated_carrier_subset_of_generators
    intro s i
    rcases i with c | i
    · exact (M.termGeneratedAssignment (namedTuple S (appendAssignments p q)) s (.inl c)).property
    · exact (M.termGeneratedAssignment (namedTuple S (appendAssignments p q)) s (.inr (.inl i))).property
  apply sortedSubstructure_eq_of_carriers
  intro s
  apply Set.Subset.antisymm
  · apply termGenerated_carrier_subset_of_generators V (namedTuple T q) _ s
    intro t i
    rcases i with c | i
    · exact subsetTV t c.property
    · exact (M.termGeneratedAssignment (namedTuple S (appendAssignments p q)) t (.inr (.inr i))).property
  · apply termGenerated_carrier_subset_of_generators U (namedTuple S (appendAssignments p q)) _ s
    intro t i
    rcases i with c | (i | j)
    · let x := M.termGeneratedAssignment (namedTuple S p) t (.inl c)
      exact (M.termGeneratedAssignment (namedTuple T q) t (.inl x)).property
    · let x := M.termGeneratedAssignment (namedTuple S p) t (.inr i)
      exact (M.termGeneratedAssignment (namedTuple T q) t (.inl x)).property
    · exact (M.termGeneratedAssignment (namedTuple T q) t (.inr j)).property

theorem generated_base_field_head_tail {n : ℕ}
    (S : SortedSubstructure M) (p : fieldAssignment n X) (q : fieldAssignment 1 X) :
    M.termGenerated (namedTuple (M.termGenerated (namedTuple S p)) q) =
      M.termGenerated (namedTuple S (fieldTupleAssignment (Fin.cons (q .vf 0) (p .vf)))) := by
  rw [generated_base_append]
  let w : fieldAssignment (n+1) X := fieldTupleAssignment (Fin.cons (q .vf 0) (p .vf))
  let U := WithBase S.carrier (SumVariables (MixedVariables n Empty) (MixedVariables 1 Empty))
  let V := WithBase S.carrier (MixedVariables (n+1) Empty)
  let f : (s : TCsort) → U s → V s
    | .vf => Sum.elim Sum.inl (Sum.elim (Sum.inr ∘ Fin.succ) (fun _ => .inr 0))
    | .rv => Sum.elim Sum.inl (Sum.elim Empty.elim Empty.elim)
  let g : (s : TCsort) → V s → U s
    | .vf => Sum.elim Sum.inl (Fin.cases (.inr (.inr 0)) (Sum.inr ∘ Sum.inl))
    | .rv => Sum.elim Sum.inl Empty.elim
  apply termGenerated_eq_of_generator_relabel (namedTuple S (appendAssignments p q)) (namedTuple S w) f g
  · intro s i
    cases s
    · rcases i with c | (i | j)
      · rfl
      · rfl
      · change q .vf j = q .vf 0
        rw [Fin.fin_one_eq_zero j]
    · rcases i with c | (i | j)
      · rfl
      · exact i.elim
      · exact j.elim
  · intro s i
    cases s
    · rcases i with c | i
      · rfl
      · refine Fin.cases rfl (fun j => rfl) i
    · rcases i with c | i
      · rfl
      · exact i.elim

theorem generated_base_emptyField (S : SortedSubstructure M) (p : fieldAssignment 0 X) :
    M.termGenerated (namedTuple S p) = S := by
  apply sortedSubstructure_eq_of_carriers
  intro s
  apply Set.Subset.antisymm
  · apply termGenerated_carrier_subset_of_generators _ _ _ s
    intro t i
    rcases i with c | i
    · exact c.property
    · cases t
      · exact i.elim0
      · exact i.elim
  · intro x hx
    exact (M.termGeneratedAssignment (namedTuple S p) s (.inl ⟨x,hx⟩)).property

theorem generated_base_field_perm {n : ℕ} (S : SortedSubstructure M) (p : fieldAssignment n X)
    (order : Equiv.Perm (Fin n)) :
    M.termGenerated (namedTuple S (fieldTupleAssignment (p .vf ∘ order))) = M.termGenerated (namedTuple S p) := by
  let U := WithBase S.carrier (MixedVariables n Empty)
  let f : (s : TCsort) → U s → U s
    | .vf => Sum.map id order
    | .rv => id
  let g : (s : TCsort) → U s → U s
    | .vf => Sum.map id order.symm
    | .rv => id
  apply termGenerated_eq_of_generator_relabel _ _ f g
  · intro s i
    cases s
    · cases i <;> rfl
    · rcases i with c | i
      · rfl
      · exact i.elim
  · intro s i
    cases s
    · rcases i with c | i
      · rfl
      · change p .vf i = p .vf (order (order.symm i))
        rw [order.apply_symm_apply]
    · rcases i with c | i
      · rfl
      · exact i.elim

end GeneralizedEuler.Section5
