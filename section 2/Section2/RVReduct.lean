module

public import Section2.SortedDefinability

/-! Quantifier-free formulas on RV tuples reduce to RV operations over
the RV parameters of the same substructure, as in Remark 2.27. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X}

/-- A family of free variables belonging to the RV sort. -/
abbrev RVVariables (V : Type a) : TCsort → Type a
  | .vf => PEmpty
  | .rv => V

/-- Terms of the RV reduct, written in the sorted syntax. -/
inductive SortedTerm.IsRVOnly {Var : TCsort → Type a} :
    {s : TCsort} → SortedTerm L E Var s → Prop where
  | var (x : Var .rv) : IsRVOnly (.var x)
  | app {ss : List TCsort} (f : FunctionSymbol L E ss .rv)
      (ts : SortedArgs (SortedTerm L E Var) ss) (ht : ∀ i, (ts i).IsRVOnly) :
      IsRVOnly (.app f ts)

/-- Formulas using only the primitives of the RV reduct. -/
inductive SortedFormula.IsRVOnly {Var : TCsort → Type a} :
    SortedFormula L E Var → Prop where
  | falsum : IsRVOnly .falsum
  | equal {t t' : SortedTerm L E Var .rv} :
      t.IsRVOnly → t'.IsRVOnly → IsRVOnly (.equal t t')
  | residueNonzero {ts : SortedArgs (SortedTerm L E Var) [.rv]} :
      (∀ i, (ts i).IsRVOnly) → IsRVOnly (.rel .residueNonzero ts)
  | rvLE {ts : SortedArgs (SortedTerm L E Var) [.rv, .rv]} :
      (∀ i, (ts i).IsRVOnly) → IsRVOnly (.rel .rvLE ts)
  | imp {φ ψ : SortedFormula L E Var} : IsRVOnly φ → IsRVOnly ψ → IsRVOnly (.imp φ ψ)

private theorem realize_vf_term_eq {Var : TCsort → Type a}
    (x y : ∀ s, Var s → X s) (hxy : x .vf = y .vf)
    {s : TCsort} (t : SortedTerm L E Var s) (hs : s = .vf) :
    t.realize M x = t.realize M y := by
  induction t with
  | var a =>
    cases hs
    exact congrFun hxy a
  | app f ts ih =>
    cases f <;> try contradiction
    simp only [SortedTerm.realize]
    congr 1
    funext i
    exact ih i (by simp only [List.get_eq_getElem, List.getElem_replicate])

private theorem SortedTerm.realize_mem {Var : TCsort → Type a}
    (S : SortedSubstructure M) (x : ∀ s, Var s → X s)
    (hx : ∀ s v, x s v ∈ S.carrier s) {s : TCsort} (t : SortedTerm L E Var s) :
    t.realize M x ∈ S.carrier s := by
  induction t with
  | var a => exact hx _ a
  | app f ts ih => exact S.closed f _ ih

section Reduction

variable (S : SortedSubstructure M) {V : Type a}

abbrev FullRVVariables (S : SortedSubstructure M) (V : Type a) :=
  fun s => (S.carrier s : Type z) ⊕ RVVariables V s

abbrev ReductRVVariables (S : SortedSubstructure M) (V : Type a) :=
  RVVariables ((S.carrier .rv : Type z) ⊕ V)

def fullRVAssignment (x : V → X .rv) : ∀ s, FullRVVariables S V s → X s
  | .vf => Sum.elim Subtype.val PEmpty.elim
  | .rv => Sum.elim Subtype.val x

def reductRVAssignment (x : V → X .rv) : ∀ s, ReductRVVariables S V s → X s
  | .vf => PEmpty.elim
  | .rv => Sum.elim Subtype.val x

private def defaultRV : S.carrier .rv :=
  S.structureOn.funMap .rvZero (fun i => i.elim0)

private theorem defaultAssignment_mem :
    ∀ s v, fullRVAssignment S (fun _ : V => (defaultRV S).val) s v ∈ S.carrier s := by
  intro s v
  cases s with
  | vf =>
    rcases v with p | v
    · exact p.property
    · exact PEmpty.elim v
  | rv =>
    rcases v with p | _
    · exact p.property
    · exact (defaultRV S).property

private theorem get_replicate_sort (s : TCsort) {n : ℕ}
    (i : Fin (List.replicate n s).length) : (List.replicate n s).get i = s := by
  simp only [List.get_eq_getElem, List.getElem_replicate]

private theorem normalize_auxiliary_term {s : TCsort} (t : SortedTerm L E (FullRVVariables S V) s)
    (hs : s = .rv) :
    ∃ t' : SortedTerm L E (ReductRVVariables S V) s, t'.IsRVOnly ∧
      ∀ x : V → X .rv, t'.realize M (reductRVAssignment S x) =
        t.realize M (fullRVAssignment S x) := by
  induction t with
  | var v =>
    cases hs
    let v' : ReductRVVariables S V .rv := v
    exact ⟨.var v', .var v', fun _ => rfl⟩
  | app f ts ih =>
    have useRV {ss : List TCsort} (f : FunctionSymbol L E ss .rv)
        (ts : SortedArgs (SortedTerm L E (FullRVVariables S V)) ss)
        (ih : ∀ i, (ss.get i) = .rv →
          ∃ t' : SortedTerm L E (ReductRVVariables S V) (ss.get i),
            t'.IsRVOnly ∧ ∀ x : V → X .rv,
              t'.realize M (reductRVAssignment S x) = (ts i).realize M (fullRVAssignment S x))
        (hr : ∀ i : Fin ss.length, ss.get i = .rv) :
        ∃ t' : SortedTerm L E (ReductRVVariables S V) .rv, t'.IsRVOnly ∧
          ∀ x : V → X .rv, t'.realize M (reductRVAssignment S x) =
            (SortedTerm.app f ts).realize M (fullRVAssignment S x) := by
      choose t' hp hreal using fun i => ih i (hr i)
      exact ⟨.app f t', .app f t' hp, fun x => congrArg (M.funMap f) (funext fun i => hreal i x)⟩
    cases f with
    | vf f => contradiction
    | rv =>
      let x₀ : V → X .rv := fun _ => (defaultRV S).val
      let t := SortedTerm.app (.rv : FunctionSymbol L E [.vf] .rv) ts
      let c : S.carrier .rv :=
        ⟨t.realize M (fullRVAssignment S x₀), t.realize_mem S _ (defaultAssignment_mem S)⟩
      let v' : ReductRVVariables S V .rv := Sum.inl c
      refine ⟨.var v', .var v', fun x => ?_⟩
      change M.funMap .rv (fun i => (ts i).realize M (fullRVAssignment S x₀)) =
        M.funMap .rv (fun i => (ts i).realize M (fullRVAssignment S x))
      congr 1
      funext i
      have hi : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
      subst i
      exact realize_vf_term_eq (fullRVAssignment S x₀) (fullRVAssignment S x) rfl (ts 0) rfl
    | rvZero => exact useRV .rvZero ts ih (fun i => i.elim0)
    | rvOne => exact useRV .rvOne ts ih (fun i => i.elim0)
    | rvMul => exact useRV .rvMul ts ih (get_replicate_sort .rv (n := 2))
    | rvInv => exact useRV .rvInv ts ih (get_replicate_sort .rv (n := 1))
    | power e => exact useRV (.power e) ts ih (get_replicate_sort .rv (n := 1))
    | residue f => exact useRV (.residue f) ts ih (get_replicate_sort .rv)

private theorem constant_to_rv_formula (p : (V → X .rv) → Prop) (c : Prop)
    (hc : ∀ x, p x ↔ c) :
    ∃ ψ : SortedFormula L E (ReductRVVariables S V), ψ.IsRVOnly ∧
      ∀ x, ψ.realize M (reductRVAssignment S x) ↔ p x := by
  classical
  by_cases h : c
  · exact ⟨.imp .falsum .falsum, .imp .falsum .falsum,
      fun x => iff_of_true (fun h => h) ((hc x).mpr h)⟩
  · exact ⟨.falsum, .falsum, fun x => iff_of_false id (h ∘ (hc x).mp)⟩

/-- Quantifier-free predicates on RV tuples use only RV operations and
parameters from the old RV sort. A VF-only atom is constant and each
leading term of a VF expression in the old parameters is already named. -/
theorem normalize_rv_formula {φ : SortedFormula L E (FullRVVariables S V)} (hφ : φ.IsQF) :
    ∃ ψ : SortedFormula L E (ReductRVVariables S V), ψ.IsRVOnly ∧
      ∀ x, ψ.realize M (reductRVAssignment S x) ↔ φ.realize M (fullRVAssignment S x) := by
  let x₀ : V → X .rv := fun _ => (defaultRV S).val
  induction hφ with
  | falsum => exact ⟨.falsum, .falsum, fun _ => Iff.rfl⟩
  | equal t t' =>
    rename_i s
    cases s with
    | vf =>
      apply constant_to_rv_formula S _ ((.equal t t' : SortedFormula L E _).realize M (fullRVAssignment S x₀))
      intro x
      change t.realize M (fullRVAssignment S x) = t'.realize M (fullRVAssignment S x) ↔
        t.realize M (fullRVAssignment S x₀) = t'.realize M (fullRVAssignment S x₀)
      rw [realize_vf_term_eq (fullRVAssignment S x) (fullRVAssignment S x₀) rfl t rfl,
        realize_vf_term_eq (fullRVAssignment S x) (fullRVAssignment S x₀) rfl t' rfl]
    | rv =>
      obtain ⟨v, hv, he⟩ := normalize_auxiliary_term S t rfl
      obtain ⟨v', hv', he'⟩ := normalize_auxiliary_term S t' rfl
      exact ⟨.equal v v', .equal hv hv', fun x => by simp only [SortedFormula.realize, he, he']⟩
  | rel r ts =>
    cases r with
    | vf r =>
      apply constant_to_rv_formula S _ ((.rel (.vf r) ts : SortedFormula L E _).realize M
        (fullRVAssignment S x₀))
      intro x
      simp only [SortedFormula.realize]
      have h : (fun i => (ts i).realize M (fullRVAssignment S x)) =
          (fun i => (ts i).realize M (fullRVAssignment S x₀)) :=
        funext fun i => realize_vf_term_eq (fullRVAssignment S x) (fullRVAssignment S x₀)
          rfl (ts i) (get_replicate_sort .vf i)
      rw [h]
    | residueNonzero =>
      choose ts' ht' he using fun i => normalize_auxiliary_term S (ts i) (get_replicate_sort .rv (n := 1) i)
      exact ⟨.rel .residueNonzero ts', .residueNonzero ht',
        fun x => by simp only [SortedFormula.realize, he]⟩
    | rvLE =>
      choose ts' ht' he using fun i => normalize_auxiliary_term S (ts i) (get_replicate_sort .rv (n := 2) i)
      exact ⟨.rel .rvLE ts', .rvLE ht', fun x => by simp only [SortedFormula.realize, he]⟩
  | imp _ _ ihφ ihψ =>
    obtain ⟨v, hv, hve⟩ := ihφ
    obtain ⟨w, hw, hwe⟩ := ihψ
    exact ⟨.imp v w, .imp hv hw, fun x => by simp only [SortedFormula.realize, hve, hwe]⟩

/-- Definable sets of RV tuples can be defined in the RV reduct over
the same RV parameters when quantifier elimination is available. -/
theorem exists_rv_formula_of_definable
    {D : Set (∀ s, RVVariables V s → X s)}
    (hD : SortedDefinableOver M S.carrier D)
    (hQE : ∀ φ : SortedFormula L E (FullRVVariables S V),
      ∃ q : SortedFormula L E (FullRVVariables S V), q.IsQF ∧
        ∀ v, q.realize M v ↔ φ.realize M v) :
    ∃ ψ : SortedFormula L E (ReductRVVariables S V), ψ.IsRVOnly ∧
      ∀ x : ∀ s, RVVariables V s → X s,
        x ∈ D ↔ ψ.realize M (reductRVAssignment S (x .rv)) := by
  obtain ⟨φ, hφ⟩ := hD
  obtain ⟨q, hq, hqφ⟩ := hQE φ
  obtain ⟨p, hp, hpq⟩ := normalize_rv_formula S hq
  refine ⟨p, hp, fun x => ?_⟩
  have h : (fun s => Sum.elim Subtype.val (x s)) = fullRVAssignment S (x .rv) := by
    funext s v
    cases s with
    | vf =>
      rcases v with a | v
      · rfl
      · exact PEmpty.elim v
    | rv => rfl
  rw [hφ, h, ← hqφ, hpq]

end Reduction

end GeneralizedEuler.Section2
