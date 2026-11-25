module

public import Section2.SortedStructure

/-! Terms and formulas whose variables and quantifiers carry VF or RV sorts. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z z' a

variable {L : Language.{u, v}} {E : Type w}

/-- A new variable of sort `s`, adjoined to an existing variable family. -/
abbrev AddSortedVar (Var : TCsort → Type a) (s : TCsort) (t : TCsort) :=
  Var t ⊕ PLift (s = t)

@[expose]
def extendSortedAssignment {Var : TCsort → Type a} {X : TCsort → Type z} {s : TCsort}
    (assign : ∀ t, Var t → X t) (x : X s) (t : TCsort) : AddSortedVar Var s t → X t
  | .inl v => assign t v
  | .inr ⟨h⟩ => h ▸ x

inductive SortedTerm (L : Language.{u, v}) (E : Type w)
    (Var : TCsort → Type a) : TCsort → Type (max u w a)
  | var {s} : Var s → SortedTerm L E Var s
  | app {ss s} : FunctionSymbol L E ss s →
      SortedArgs (SortedTerm L E Var) ss → SortedTerm L E Var s

@[expose]
def SortedTerm.realize {Var : TCsort → Type a} {X : TCsort → Type z}
    (M : SortedStructure L E X) (assign : ∀ s, Var s → X s) :
    {s : TCsort} → SortedTerm L E Var s → X s
  | _, .var v => assign _ v
  | _, .app f ts => M.funMap f (fun i => (ts i).realize M assign)

inductive SortedFormula (L : Language.{u, v}) (E : Type w) :
    (TCsort → Type a) → Type (max u v w (a + 1))
  | falsum {Var} : SortedFormula L E Var
  | equal {Var s} : SortedTerm L E Var s → SortedTerm L E Var s → SortedFormula L E Var
  | rel {Var ss} : RelationSymbol L ss → SortedArgs (SortedTerm L E Var) ss → SortedFormula L E Var
  | imp {Var} : SortedFormula L E Var → SortedFormula L E Var → SortedFormula L E Var
  | all {Var} (s : TCsort) : SortedFormula L E (AddSortedVar Var s) → SortedFormula L E Var

@[expose]
def SortedFormula.realize {X : TCsort → Type z} (M : SortedStructure L E X) :
    {Var : TCsort → Type a} → SortedFormula L E Var → (∀ s, Var s → X s) → Prop
  | _, .falsum, _ => False
  | _, .equal t t', v => t.realize M v = t'.realize M v
  | _, .rel r ts, v => M.relMap r (fun i => (ts i).realize M v)
  | _, .imp φ ψ, v => φ.realize M v → ψ.realize M v
  | _, .all s φ, v => ∀ x : X s, φ.realize M (extendSortedAssignment v x)

inductive SortedFormula.IsQF : {Var : TCsort → Type a} → SortedFormula L E Var → Prop
  | falsum {Var} : IsQF (SortedFormula.falsum (Var := Var))
  | equal {Var s} (x y : SortedTerm L E Var s) : IsQF (.equal x y)
  | rel {Var ss} (r : RelationSymbol L ss) (ts : SortedArgs (SortedTerm L E Var) ss) :
      IsQF (.rel r ts)
  | imp {Var} {φ ψ : SortedFormula L E Var} : IsQF φ → IsQF ψ → IsQF (.imp φ ψ)

structure SortedEmbedding {X : TCsort → Type z} {Y : TCsort → Type z'}
    (M : SortedStructure L E X) (N : SortedStructure L E Y) where
  toEmbedding : ∀ s, X s ↪ Y s
  map_fun : ∀ {ss s} (f : FunctionSymbol L E ss s) (xs : SortedArgs X ss),
    toEmbedding s (M.funMap f xs) = N.funMap f (fun i => toEmbedding _ (xs i))
  map_rel : ∀ {ss} (r : RelationSymbol L ss) (xs : SortedArgs X ss),
    N.relMap r (fun i => toEmbedding _ (xs i)) ↔ M.relMap r xs

variable {X : TCsort → Type z} {Y : TCsort → Type z'}
  {M : SortedStructure L E X} {N : SortedStructure L E Y}

def SortedEmbedding.mapAssignment (ι : SortedEmbedding M N)
    {Var : TCsort → Type a} (assign : ∀ s, Var s → X s) (s : TCsort) : Var s → Y s :=
  ι.toEmbedding s ∘ assign s

theorem SortedEmbedding.realize_term (ι : SortedEmbedding M N) {Var : TCsort → Type a}
    (assign : ∀ s, Var s → X s) {s : TCsort} (t : SortedTerm L E Var s) :
    ι.toEmbedding s (t.realize M assign) = t.realize N (ι.mapAssignment assign) := by
  induction t with
  | var => rfl
  | app f ts ih =>
    simp only [SortedTerm.realize, ι.map_fun, ih]

theorem SortedEmbedding.realize_qf (ι : SortedEmbedding M N) {Var : TCsort → Type a}
    {φ : SortedFormula L E Var} (hφ : φ.IsQF) (assign : ∀ s, Var s → X s) :
    φ.realize N (ι.mapAssignment assign) ↔ φ.realize M assign := by
  induction hφ with
  | falsum => rfl
  | equal x y =>
    simp only [SortedFormula.realize, ← ι.realize_term assign, EmbeddingLike.apply_eq_iff_eq]
  | rel r ts =>
    simp only [SortedFormula.realize, ← ι.realize_term assign, ι.map_rel]
  | imp _ _ hx hy => simp only [SortedFormula.realize, hx, hy]

end GeneralizedEuler.Section2
