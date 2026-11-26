module

public import Section5.DefinableFieldChoice

/-! Use elementarity after adjoining field coordinates to obtain the
term witnesses for the fixed-base selection theorem. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ}

abbrev fieldAssignment (n : ℕ) (X : TCsort → Type z) :=
  SortedAssignment X (MixedVariables n Empty)

abbrev namedFieldAssignment (S : SortedSubstructure M) (x : fieldAssignment n X) :
    ∀ s, WithBase S.carrier (MixedVariables n Empty) s → X s :=
  fun s => Sum.elim Subtype.val (x s)

/-- The elementary extension supplied by adjoining the input VF tuple
realizes a witness for every nonempty definable VF fiber. Its field
elements are term values by the definition of the generated base. -/
theorem field_term_witness_of_elementary
    {R : fieldAssignment n X → fieldAssignment k X → Prop}
    (hR : DefinableRelation M S.carrier R) (x : fieldAssignment n X)
    (hElem : let B := M.termGenerated (namedFieldAssignment S x)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))
    (hy : ∃ y, R x y) :
    ∃ T : FieldTermTuple M S (MixedVariables n Empty) k, R x (realizeFieldTuple T x) := by
  let V := MixedVariables n Empty
  let W := MixedVariables k Empty
  let N := WithBase S.carrier V
  let name := namedFieldAssignment S x
  let B := M.termGenerated name
  let z := M.termGeneratedAssignment name
  obtain ⟨φ,hφ⟩ := hR
  let rename : ∀ s, WithBase S.carrier (SumVariables V W) s → AddSortedBlock N .vf k s
    | .vf => fun
      | .inl c => .inl (.inl c)
      | .inr (.inl i) => .inl (.inr i)
      | .inr (.inr i) => .inr ⟨i,⟨rfl⟩⟩
    | .rv => fun
      | .inl c => .inl (.inl c)
      | .inr (.inl i) => i.elim
      | .inr (.inr i) => i.elim
  let ψ := φ.relabel rename
  let field (y : Fin k → X .vf) : fieldAssignment k X
    | .vf => y
    | .rv => Empty.elim
  have eval (y : Fin k → X .vf) :
      ψ.realize M (appendSortedBlock name y) ↔ R x (field y) := by
    change (φ.relabel rename).realize M _ ↔ _
    rw [φ.realize_relabel]
    have hEq :
        (fun s => appendSortedBlock name y s ∘ rename s) =
          (fun s => Sum.elim Subtype.val (Sum.elim (x s) (field y s))) := by
      funext s i
      cases s with
      | vf => rcases i with c | (i | j) <;> rfl
      | rv => rcases i with c | (i | j); exacts [rfl,i.elim,j.elim]
    rw [hEq]
    have h := (hφ (fun s => Sum.elim (x s) (field y s))).symm
    have h₁ : (fun s => Sum.elim (x s) (field y s) ∘ Sum.inl) = x := rfl
    have h₂ : (fun s => Sum.elim (x s) (field y s) ∘ Sum.inr) = field y := rfl
    change _ ↔ R (fun s => Sum.elim (x s) (field y s) ∘ Sum.inl)
      (fun s => Sum.elim (x s) (field y s) ∘ Sum.inr) at h
    rw [h₁,h₂] at h
    exact h
  obtain ⟨y,hy⟩ := hy
  have hy' : field (y .vf) = y := by
    funext s i
    cases s with
    | vf => rfl
    | rv => exact i.elim
  have hExists : (ψ.exBlock .vf k).realize M name :=
    (SortedFormula.realize_exBlock M .vf ψ name).2
      ⟨y .vf, (eval _).2 (hy' ▸ hy)⟩
  have hB : (ψ.exBlock .vf k).realize B.structureOn z :=
    (hElem (ψ.exBlock .vf k) z).2 hExists
  obtain ⟨w,hw⟩ := (SortedFormula.realize_exBlock B.structureOn .vf ψ z).1 hB
  have hwM := (hElem ψ (appendSortedBlock z w)).1 hw
  have he : (fun s i => (appendSortedBlock z w s i).val) =
      appendSortedBlock name (fun j => (w j).val) := by
    funext s i
    rcases i with i | ⟨i,e⟩
    · rfl
    · rcases e with ⟨eq⟩
      subst s
      rfl
  rw [he] at hwM
  have hR' := (eval _).1 hwM
  have terms (j : Fin k) :
      ∃ t : SortedTerm L E N .vf, t.realize M name = (w j).val := (w j).property
  choose τ hτ using terms
  refine ⟨τ,?_⟩
  have ht : realizeFieldTuple τ x = field (fun j => (w j).val) := by
    funext s j
    cases s with
    | vf => exact hτ j
    | rv => exact j.elim
  exact ht.symm ▸ hR'

/-- The field choice used in lifting and its exceptional-set argument.
The elementary input is required only after adjoining VF parameters. -/
theorem definable_field_choice_of_elementary
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (MixedVariables n Empty))
      (BaseAssignments S.carrier (MixedVariables n Empty)))
    (A : Set (fieldAssignment n X)) (hA : SortedDefinableOver M S.carrier A)
    {R : fieldAssignment n X → fieldAssignment k X → Prop}
    (hR : DefinableRelation M S.carrier R)
    (hElem : ∀ x ∈ A, let B := M.termGenerated (namedFieldAssignment S x)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))
    (hNonempty : ∀ x ∈ A, ∃ y, R x y) :
    ∃ f : A → fieldAssignment k X,
      (∀ x : A, R x.val (f x)) ∧
      DefinableRelation M S.carrier (fun x y => ∃ h : x ∈ A, f ⟨x,h⟩ = y) :=
  definable_field_choice_from_terms sat A hA hR
    (fun x hx => field_term_witness_of_elementary hR x (hElem x hx) (hNonempty x hx))

end GeneralizedEuler.Section5
