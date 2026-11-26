module

public import Section5.DefinableBijectionSchemes
public import Section5.DefinableRelations
public import Section2.GeneratedSubstructure

/-! Turn definitions over a generated parameter base into formula
schemes over the original base with the extra tuple as variables. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe a b z

variable {L : Language} {E : Type*}

private def substituteSortedTerms : {U : TCsort → Type a} → {V : TCsort → Type b} →
    (∀ s, U s → SortedTerm L E V s) → SortedFormula L E U → SortedFormula L E V
  | _, _, _, .falsum => .falsum
  | _, _, r, .equal t u => .equal (t.subst r) (u.subst r)
  | _, _, r, .rel q ts => .rel q (fun i => (ts i).subst r)
  | _, _, r, .imp φ ψ => .imp (substituteSortedTerms r φ) (substituteSortedTerms r ψ)
  | _, _, r, .all s φ => .all s (substituteSortedTerms
    (fun t => Sum.elim (fun i => (r t i).relabel (fun _ => Sum.inl)) (fun j => .var (.inr j))) φ)

private theorem realize_substituteSortedTerms {X : TCsort → Type z} (M : SortedStructure L E X)
    {U : TCsort → Type a} (φ : SortedFormula L E U) :
    ∀ {V : TCsort → Type b} (r : ∀ s, U s → SortedTerm L E V s) (v : ∀ s, V s → X s),
      (substituteSortedTerms r φ).realize M v ↔ φ.realize M (fun s i => (r s i).realize M v) := by
  induction φ with
  | falsum => intros; rfl
  | equal x y =>
    intros
    simp only [substituteSortedTerms,SortedFormula.realize,SortedTerm.realize_subst]
  | rel q ts =>
    intros
    simp only [substituteSortedTerms,SortedFormula.realize,SortedTerm.realize_subst]
  | imp φ ψ hφ hψ =>
    intros
    simp only [substituteSortedTerms,SortedFormula.realize,hφ,hψ]
  | all s φ ih =>
    intro V r v
    simp only [substituteSortedTerms,SortedFormula.realize]
    apply forall_congr'
    intro x
    rw [ih]
    apply iff_of_eq
    congr 1
    funext t i
    rcases i with i | ⟨e⟩
    · change ((r t i).relabel (fun _ => Sum.inl)).realize M (extendSortedAssignment v x) =
        (r t i).realize M v
      rw [SortedTerm.realize_relabel]
      rfl
    · cases e
      rfl

variable {X : TCsort → Type z} {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U : TCsort → Type}

abbrev namedTuple (S : SortedSubstructure M) (p : SortedAssignment X P) :
    ∀ s, WithBase S.carrier P s → X s := fun s => Sum.elim Subtype.val (p s)

/-- Every definable fiber over the generated base has a defining
formula over the original base with the extra tuple as variables. -/
theorem definable_fiber_as_scheme (p : SortedAssignment X P) (D : Set (SortedAssignment X U))
    (hd : SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier D) :
    ∃ D' : Set (SortedAssignment X (SumVariables P U)), SortedDefinableOver M S.carrier D' ∧
      ∀ u, appendAssignments p u ∈ D' ↔ u ∈ D := by
  classical
  let T := M.termGenerated (namedTuple S p)
  obtain ⟨φ,hφ⟩ := hd
  have terms (s : TCsort) (c : T.carrier s) :
      ∃ t : SortedTerm L E (WithBase S.carrier P) s, t.realize M (namedTuple S p) = c.val := c.property
  choose term eval using terms
  let inject (s : TCsort) : WithBase S.carrier P s → WithBase S.carrier (SumVariables P U) s :=
    Sum.map id Sum.inl
  let r (s : TCsort) : WithBase T.carrier U s → SortedTerm L E (WithBase S.carrier (SumVariables P U)) s :=
    Sum.elim (fun c => (term s c).relabel inject) (fun u => .var (.inr (.inr u)))
  let ψ := substituteSortedTerms r φ
  refine ⟨{a | ψ.realize M (fun s => Sum.elim Subtype.val (a s))},⟨ψ,fun _ => Iff.rfl⟩,?_⟩
  intro u
  let w : ∀ s, WithBase S.carrier (SumVariables P U) s → X s :=
    fun s => Sum.elim Subtype.val (appendAssignments p u s)
  have he : (fun s i => (r s i).realize M w) = (fun s => Sum.elim Subtype.val (u s)) := by
    funext s i
    rcases i with c | j
    · change ((term s c).relabel inject).realize M w = c.val
      rw [SortedTerm.realize_relabel]
      have same : (fun t => w t ∘ inject t) = namedTuple S p := by
        funext t i
        cases i <;> rfl
      rw [same,eval]
    · rfl
  change ψ.realize M w ↔ u ∈ D
  rw [realize_substituteSortedTerms, he]
  exact (hφ u).symm

theorem definable_scheme_at_fiber (p : SortedAssignment X P)
    (D : Set (SortedAssignment X (SumVariables P U))) (hd : SortedDefinableOver M S.carrier D) :
    SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier {u | appendAssignments p u ∈ D} := by
  let T := M.termGenerated (namedTuple S p)
  let named := M.termGeneratedAssignment (namedTuple S p)
  obtain ⟨φ,hφ⟩ := hd
  let r (s : TCsort) : WithBase S.carrier (SumVariables P U) s → WithBase T.carrier U s
    | .inl c => .inl (named s (.inl c))
    | .inr (.inl i) => .inl (named s (.inr i))
    | .inr (.inr i) => .inr i
  refine ⟨φ.relabel r,fun u => ?_⟩
  rw [φ.realize_relabel]
  have same : (fun s => Sum.elim Subtype.val (u s) ∘ r s) =
      (fun s => Sum.elim Subtype.val (appendAssignments p u s)) := by
    funext s i
    rcases i with c | (i | i) <;> rfl
  rw [same]
  exact hφ _

theorem definable_relation_fiber_as_scheme {V : TCsort → Type} (p : SortedAssignment X P)
    (G : SortedAssignment X U → SortedAssignment X V → Prop)
    (hg : DefinableRelation M (M.termGenerated (namedTuple S p)).carrier G) :
    ∃ H : Set (SortedAssignment X (SumVariables (SumVariables P U) V)),
      SortedDefinableOver M S.carrier H ∧
      ∀ u v, appendAssignments (appendAssignments p u) v ∈ H ↔ G u v := by
  let D : Set (SortedAssignment X (SumVariables U V)) :=
    {w | G (fun s => w s ∘ Sum.inl) (fun s => w s ∘ Sum.inr)}
  obtain ⟨D',hd,he⟩ := definable_fiber_as_scheme p D hg
  let r (s : TCsort) : SumVariables P (SumVariables U V) s → SumVariables (SumVariables P U) V s :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  refine ⟨_,hd.pullback_relabel r,?_⟩
  intro u v
  have eq : (fun s => appendAssignments (appendAssignments p u) v s ∘ r s) =
      appendAssignments p (appendAssignments u v) := by
    funext s i
    rcases i with i | (i | i) <;> rfl
  change (fun s => appendAssignments (appendAssignments p u) v s ∘ r s) ∈ D' ↔ G u v
  rw [eq,he]
  rfl

end GeneralizedEuler.Section5
