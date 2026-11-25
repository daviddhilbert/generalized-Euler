module

public import Mathlib.ModelTheory.Complexity
public import Section2.TaggedLanguage
public import Section2.SortedSyntax

/-! The guarded translation of sorted terms and formulas, with semantic
preservation. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z a b

variable {L : Language.{u, v}} {E : Type w}

abbrev TaggedVar (Var : TCsort → Type a) := (s : TCsort) × Var s

section Translation

variable {X : TCsort → Type z} {A : Type b} [(taggedLanguage L E).Structure A]
  {M : SortedStructure L E X}

@[expose]
def GuardedPresentation.assignment (P : GuardedPresentation M A)
    {Var : TCsort → Type a} (v : ∀ s, Var s → X s) : TaggedVar Var → A :=
  fun a => P.sortEmbedding a.1 (v a.1 a.2)

def SortedTerm.toTagged {Var : TCsort → Type a} :
    {s : TCsort} → SortedTerm L E Var s → (taggedLanguage L E).Term (TaggedVar Var)
  | _, .var x => .var ⟨_, x⟩
  | _, .app f ts => .func ⟨_, rfl, _, f⟩ (fun i => (ts i).toTagged)

theorem SortedTerm.realize_toGuarded (P : GuardedPresentation M A)
    {Var : TCsort → Type a} (v : ∀ s, Var s → X s)
    {s : TCsort} (t : SortedTerm L E Var s) :
    t.toTagged.realize (P.assignment v) = P.sortEmbedding s (t.realize M v) := by
  induction t with
  | var => rfl
  | app f ts ih =>
    rw [SortedTerm.toTagged, Term.realize_func]
    simp only [ih, SortedTerm.realize]
    exact P.map_fun f _

private def splitAddedVar {Var : TCsort → Type a} (s : TCsort) :
    TaggedVar (AddSortedVar Var s) → TaggedVar Var ⊕ Unit
  | ⟨t, .inl x⟩ => .inl ⟨t, x⟩
  | ⟨_, .inr _⟩ => .inr ()

private theorem splitAddedVar_eval (P : GuardedPresentation M A) {Var : TCsort → Type a}
    (v : ∀ t, Var t → X t) {s : TCsort} (x : X s) (u : Unit → A)
    (hu : u () = P.sortEmbedding s x) :
    Sum.elim (P.assignment v) u ∘ splitAddedVar s =
      P.assignment (extendSortedAssignment v x) := by
  funext t
  obtain ⟨t, a⟩ := t
  cases a with
  | inl a => rfl
  | inr h =>
    obtain ⟨h⟩ := h
    subst t
    exact hu

end Translation

/-- The guard for a term of the specified sort. -/
@[expose]
def sortGuardFormula {α : Type a} (s : TCsort) (t : (taggedLanguage L E).Term α) :
    (taggedLanguage L E).Formula α :=
  Relations.formula (L := taggedLanguage L E) (.sortGuard s) (fun _ => t)

theorem sortGuardFormula_realize {X : TCsort → Type z} {A : Type b}
    [(taggedLanguage L E).Structure A] {M : SortedStructure L E X}
    (P : GuardedPresentation M A) {α : Type a} (v : α → A)
    (s : TCsort) (t : (taggedLanguage L E).Term α) :
    (sortGuardFormula s t).Realize v ↔ ∃ x : X s, P.sortEmbedding s x = t.realize v := by
  rw [sortGuardFormula, Formula.realize_rel]
  exact P.guard s (t.realize v)

def SortedFormula.toTagged : {Var : TCsort → Type a} →
    SortedFormula L E Var → (taggedLanguage L E).Formula (TaggedVar Var)
  | _, .falsum => ⊥
  | _, .equal t t' => t.toTagged.equal t'.toTagged
  | _, .rel r ts => Relations.formula (.symbol _ rfl r) (fun i => (ts i).toTagged)
  | _, .imp φ ψ => φ.toTagged.imp ψ.toTagged
  | _, .all s φ => Formula.iAlls Unit
      ((sortGuardFormula s (.var (.inr ()))).imp (φ.toTagged.relabel (splitAddedVar s)))

theorem SortedFormula.realize_toGuarded {X : TCsort → Type z} {A : Type b}
    [(taggedLanguage L E).Structure A] {M : SortedStructure L E X}
    (P : GuardedPresentation M A)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∀ v : ∀ s, Var s → X s,
      φ.toTagged.Realize (P.assignment v) ↔ φ.realize M v := by
  induction φ with
  | falsum =>
    intro v
    exact Formula.realize_bot
  | equal t t' =>
    intro v
    rw [SortedFormula.toTagged, Formula.realize_equal, t.realize_toGuarded P,
      t'.realize_toGuarded P]
    exact (P.sortEmbedding _).injective.eq_iff
  | rel r ts =>
    intro v
    rw [SortedFormula.toTagged, Formula.realize_rel]
    simp only [SortedTerm.realize_toGuarded]
    exact P.map_rel r _
  | imp φ ψ ihφ ihψ =>
    intro v
    rw [SortedFormula.toTagged, Formula.realize_imp, ihφ, ihψ]
    rfl
  | all s φ ih =>
    intro v
    rw [SortedFormula.toTagged, Formula.realize_iAlls]
    change (∀ u : Unit → A, _) ↔ ∀ x : X s,
      φ.realize M (extendSortedAssignment v x)
    constructor
    · intro h x
      specialize h (fun _ => P.sortEmbedding s x)
      rw [Formula.realize_imp, sortGuardFormula_realize P, Formula.realize_relabel] at h
      have hx := h ⟨x, rfl⟩
      rw [splitAddedVar_eval P v x _ rfl] at hx
      exact (ih _).mp hx
    · intro h u
      rw [Formula.realize_imp, sortGuardFormula_realize P, Formula.realize_relabel]
      rintro ⟨x, hx⟩
      rw [splitAddedVar_eval P v x u hx.symm]
      exact (ih _).mpr (h x)

set_option linter.style.haveILetI false in
theorem SortedFormula.realize_toTagged {X : TCsort → Type z}
    (M : SortedStructure L E X) (d : ∀ s, X s)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) (v : ∀ s, Var s → X s) :
    letI := taggedStructure M d
    φ.toTagged.Realize ((taggedPresentation M d).assignment v) ↔ φ.realize M v := by
  letI := taggedStructure M d
  exact φ.realize_toGuarded (taggedPresentation M d) v

theorem SortedFormula.toTagged_isQF {Var : TCsort → Type a}
    {φ : SortedFormula L E Var} (h : φ.IsQF) : φ.toTagged.IsQF := by
  induction h with
  | falsum => exact BoundedFormula.IsQF.falsum
  | equal _ _ => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | rel _ _ => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ hp hq => exact hp.imp hq

end GeneralizedEuler.Section2
