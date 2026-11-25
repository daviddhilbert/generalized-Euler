module

public import Section2.SortedStructure

/-! Terms and formulas whose variables and quantifiers carry VF or RV sorts. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z z' a b

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

/-- A sorted isomorphism is an embedding that is onto in each sort. -/
structure SortedIsomorphism {X : TCsort → Type z} {Y : TCsort → Type z'}
    (M : SortedStructure L E X) (N : SortedStructure L E Y) extends SortedEmbedding M N where
  surjective : ∀ s, Function.Surjective (toEmbedding s)

variable {X : TCsort → Type z} {Y : TCsort → Type z'}
  {M : SortedStructure L E X} {N : SortedStructure L E Y}

def SortedEmbedding.mapAssignment (ι : SortedEmbedding M N)
    {Var : TCsort → Type a} (assign : ∀ s, Var s → X s) (s : TCsort) : Var s → Y s :=
  ι.toEmbedding s ∘ assign s

theorem SortedEmbedding.mapAssignment_apply (ι : SortedEmbedding M N)
    {Var : TCsort → Type a} (assign : ∀ s, Var s → X s) (s : TCsort) (i : Var s) :
    ι.mapAssignment assign s i = ι.toEmbedding s (assign s i) := by rfl

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

/-- A sorted isomorphism preserves formulas with quantifiers as well as
the quantifier-free formulas preserved by an embedding. -/
theorem SortedIsomorphism.realize_iff (e : SortedIsomorphism M N) {Var : TCsort → Type a}
    (φ : SortedFormula L E Var) : ∀ x : (∀ s, Var s → X s),
    φ.realize N (e.toSortedEmbedding.mapAssignment x) ↔ φ.realize M x := by
  induction φ with
  | falsum => intro x; exact e.toSortedEmbedding.realize_qf .falsum x
  | equal t u => intro x; exact e.toSortedEmbedding.realize_qf (.equal t u) x
  | rel r ts => intro x; exact e.toSortedEmbedding.realize_qf (.rel r ts) x
  | imp φ ψ ihφ ihψ =>
    intro x
    simp only [SortedFormula.realize, ihφ x, ihψ x]
  | all s ψ ih =>
    intro x
    have mapped (y : X s) :
        e.toSortedEmbedding.mapAssignment (extendSortedAssignment x y) =
          extendSortedAssignment (e.toSortedEmbedding.mapAssignment x) (e.toEmbedding s y) := by
      funext t i
      rcases i with i | ⟨h⟩
      · rfl
      · have ht : s = t := h.down
        subst t
        rfl
    simp only [SortedFormula.realize]
    constructor
    · intro h y
      apply (ih (extendSortedAssignment x y)).mp
      rw [mapped]
      exact h (e.toEmbedding s y)
    · intro h y
      obtain ⟨z, rfl⟩ := e.surjective s y
      rw [← mapped]
      exact (ih (extendSortedAssignment x z)).mpr (h z)

def SortedTerm.relabel {Var : TCsort → Type a} {Var' : TCsort → Type b}
    (r : ∀ s, Var s → Var' s) :
    {s : TCsort} → SortedTerm L E Var s → SortedTerm L E Var' s
  | _, .var x => .var (r _ x)
  | _, .app f ts => .app f (fun i => (ts i).relabel r)

theorem SortedTerm.realize_relabel {Var : TCsort → Type a} {Var' : TCsort → Type b}
    (r : ∀ s, Var s → Var' s) (v : ∀ s, Var' s → X s) {s : TCsort} (t : SortedTerm L E Var s) :
    (t.relabel r).realize M v = t.realize M (fun s => v s ∘ r s) := by
  induction t with
  | var => rfl
  | app f ts ih => simp only [SortedTerm.relabel, SortedTerm.realize, ih]

def SortedFormula.relabel :
    {Var : TCsort → Type a} → {Var' : TCsort → Type b} →
      (∀ s, Var s → Var' s) → SortedFormula L E Var → SortedFormula L E Var'
  | _, _, _, .falsum => .falsum
  | _, _, r, .equal t t' => .equal (t.relabel r) (t'.relabel r)
  | _, _, r, .rel q ts => .rel q (fun i => (ts i).relabel r)
  | _, _, r, .imp φ ψ => .imp (φ.relabel r) (ψ.relabel r)
  | _, _, r, .all s φ => .all s (φ.relabel (fun t => Sum.map (r t) id))

theorem SortedFormula.realize_relabel {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∀ {Var' : TCsort → Type b} (r : ∀ s, Var s → Var' s) (v : ∀ s, Var' s → X s),
      (φ.relabel r).realize M v ↔ φ.realize M (fun s => v s ∘ r s) := by
  induction φ with
  | falsum => intros; rfl
  | equal t t' =>
    intros
    simp only [SortedFormula.relabel, SortedFormula.realize, SortedTerm.realize_relabel]
  | rel q ts =>
    intros
    simp only [SortedFormula.relabel, SortedFormula.realize, SortedTerm.realize_relabel]
  | imp φ ψ hφ hψ =>
    intros
    simp only [SortedFormula.relabel, SortedFormula.realize, hφ, hψ]
  | all s φ ih =>
    intro Var' r v
    simp only [SortedFormula.relabel, SortedFormula.realize]
    apply forall_congr'
    intro x
    rw [ih]
    apply iff_of_eq
    congr 1
    funext t a
    cases a <;> rfl

theorem SortedFormula.IsQF.relabel {Var : TCsort → Type a} {Var' : TCsort → Type b}
    {φ : SortedFormula L E Var} (hφ : φ.IsQF) (r : ∀ s, Var s → Var' s) :
    (φ.relabel r).IsQF := by
  induction hφ with
  | falsum => exact .falsum
  | equal _ _ => exact .equal ..
  | rel _ _ => exact .rel ..
  | imp _ _ hφ hψ => exact .imp hφ hψ

end GeneralizedEuler.Section2
