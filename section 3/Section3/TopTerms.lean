module

public import Section2.RVReduct
public import Section2.LeadingTermOrder

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder

universe u v w z a
variable {L : Language.{u,v}} {E : Type w} {V : TCsort → Type a}
  {X : TCsort → Type z} (M : SortedStructure L E X)

abbrev Assignment (V : TCsort → Type a) (X : TCsort → Type z) := ∀ s, V s → X s
abbrev VFExpr := SortedTerm L E V .vf

/-- Realization of rv(t), using the single map from VF to RV. -/
def lead (v : Assignment V X) (t : VFExpr (L := L) (E := E) (V := V)) : X .rv :=
  M.funMap .rv (fun i => by
    have he : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
    subst i
    exact t.realize M v)

theorem vfExpr_independent_of_rv (v w : Assignment V X) (h : v .vf = w .vf)
    {s : TCsort} (t : SortedTerm L E V s) (hs : s = .vf) :
    t.realize M v = t.realize M w := by
  induction t with
  | var i => cases hs; exact congrFun h i
  | app f ts ih =>
    cases f <;> try contradiction
    simp only [SortedTerm.realize]
    congr 1
    funext i
    exact ih i (by simp only [List.get_eq_getElem, List.getElem_replicate])

/-- A predicate or expression is determined by the original RV variables and
the leading terms of a single finite list independent of their assignment. -/
def HasTopTerms {Y : Sort*} (F : Assignment V X → Y) : Prop :=
  ∃ T : Finset (VFExpr (L := L) (E := E) (V := V)), ∀ v w, v .rv = w .rv →
    (∀ t ∈ T, lead M v t = lead M w t) → F v = F w

private theorem assemble {I : Type*} {Y : Sort*} [Fintype I] {Z : I → Type*}
    (f : ((i : I) → Z i) → Y) (terms : (i : I) → Assignment V X → Z i)
    (h : ∀ i, HasTopTerms M (terms i)) : HasTopTerms M (fun v => f (fun i => terms i v)) := by
  classical
  choose ts hts using h
  refine ⟨Finset.univ.biUnion ts, fun v w hr ht => congrArg f (funext (fun i => ?_))⟩
  exact hts i v w hr (fun t hti => ht t (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hti⟩))

theorem rv_term_hasTopTerms {s : TCsort} (t : SortedTerm L E V s) (hs : s = .rv) :
    HasTopTerms M (fun v => t.realize M v) := by
  classical
  induction t with
  | var i =>
    cases hs
    exact ⟨∅, fun _ _ hr _ => congrFun hr i⟩
  | app f ts ih =>
    cases f with
    | vf => contradiction
    | rv =>
      refine ⟨{ts 0}, fun v w _ ht => ?_⟩
      have he (v : Assignment V X) :
          (SortedTerm.app (.rv : FunctionSymbol L E [.vf] .rv) ts).realize M v =
            lead M v (ts 0) := by
        unfold lead
        change M.funMap .rv (fun i => (ts i).realize M v) = _
        congr 1
        funext i
        have h : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
        subst i
        simp
      exact (he v).trans ((ht _ (Finset.mem_singleton_self _)).trans (he w).symm)
    | _ =>
      apply assemble
      intro i
      exact ih i (by first | exact i.elim0 | solve | simp only [List.get_eq_getElem, List.getElem_replicate] | fin_cases i <;> rfl)

/-- Convention 3.1 after sorted QE. The two hypotheses encode the field
atoms of the ordered functional presentation by zero and sign of differences. -/
theorem qf_hasTopTerms
    (heq : ∀ t u : VFExpr (L := L) (E := E) (V := V),
      HasTopTerms M (fun v => t.realize M v = u.realize M v))
    (hrel : ∀ {n} (r : L.Relations n)
      (ts : SortedArgs (SortedTerm L E V) (List.replicate n .vf)),
      HasTopTerms M (fun v => (SortedFormula.rel (.vf r) ts).realize M v))
    {φ : SortedFormula L E V} (hφ : φ.IsQF) :
    HasTopTerms M (fun v => φ.realize M v) := by
  classical
  induction hφ with
  | falsum => exact ⟨∅, fun _ _ _ _ => rfl⟩
  | equal t u =>
    rename_i s
    cases s with
    | vf => exact heq t u
    | rv =>
      obtain ⟨T, ht⟩ := rv_term_hasTopTerms M t rfl
      obtain ⟨U, hu⟩ := rv_term_hasTopTerms M u rfl
      refine ⟨T ∪ U, fun v w hr hv => ?_⟩
      change (t.realize M v = u.realize M v) = (t.realize M w = u.realize M w)
      exact congrArg₂ Eq (ht v w hr (fun _ h => hv _ (Finset.mem_union_left U h)))
        (hu v w hr (fun _ h => hv _ (Finset.mem_union_right T h)))
  | rel r ts =>
    cases r with
    | vf r => exact hrel r ts
    | residueNonzero =>
      exact assemble M (M.relMap .residueNonzero) (fun i v => (ts i).realize M v)
        (fun i => rv_term_hasTopTerms M (ts i) (by fin_cases i; rfl))
    | rvLE =>
      exact assemble M (M.relMap .rvLE) (fun i v => (ts i).realize M v)
        (fun i => rv_term_hasTopTerms M (ts i) (by fin_cases i <;> rfl))
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨T, ht⟩ := ih₁
    obtain ⟨U, hu⟩ := ih₂
    exact ⟨T ∪ U, fun v w hr hv => congrArg₂ (fun p q : Prop => p → q)
      (ht v w hr (fun _ h => hv _ (Finset.mem_union_left U h)))
      (hu v w hr (fun _ h => hv _ (Finset.mem_union_right T h)))⟩

end GeneralizedEuler.Section3
