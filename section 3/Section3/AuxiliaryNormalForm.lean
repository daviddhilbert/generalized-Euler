module

public import Section3.TopTerms
public import Section2.RVMonomials
public import Section2.ValuedFieldFormulas
import all Section2.SortedStructure

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe u v w a z
variable {L : Language.{u,v}} {E : Type w} {V : TCsort → Type a}
  {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

local notation "M" => canonicalStructure (L := L) O hO P

/-- All field variables, including named field parameters, stay in a
pure L-term. No auxiliary variable can occur in it. -/
theorem pure_term_of_vf {s} (t : SortedTerm L E V s) (hs : s = .vf) :
    ∃ f : L.Term (V .vf), ∀ v : Assignment V (CanonicalSort O),
      hs ▸ t.realize M v = f.realize (v .vf) := by
  induction t with
  | var i => cases hs; exact ⟨.var i,fun _ => rfl⟩
  | app sym ts ih =>
    cases sym <;> try contradiction
    case vf n sym =>
      have sorts (i : Fin (List.replicate n TCsort.vf).length) :
          (List.replicate n TCsort.vf).get i = .vf := by simp
      choose terms hterms using fun i => ih i (sorts i)
      let ts' (i : Fin n) := terms (i.cast (List.length_replicate ..).symm)
      refine ⟨.func sym ts',fun v => ?_⟩
      apply congrArg (Structure.funMap sym)
      funext i
      exact hterms _ v

/-- Free auxiliary variables and placeholders for leading terms. Every
RV-only formula over these variables is finite syntax. -/
abbrev AuxiliaryInputs (L : Language) (V : TCsort → Type*) :=
  RVVariables (V .rv ⊕ L.Term (V .vf))

@[expose] noncomputable def auxiliaryAssignment (v : Assignment V (CanonicalSort O)) :
    Assignment (AuxiliaryInputs L V) (CanonicalSort O)
  | .vf => PEmpty.elim
  | .rv => Sum.elim (v .rv) (fun f => rv O (f.realize (v .vf)))

private theorem auxiliary_term {s} (t : SortedTerm L E V s) (hs : s = .rv) :
    ∃ u : SortedTerm L E (AuxiliaryInputs L V) s, u.IsRVOnly ∧
      ∀ v, u.realize M (auxiliaryAssignment O v) = t.realize M v := by
  induction t with
  | var i =>
    cases hs
    exact ⟨.var (s := .rv) (Sum.inl i),.var _,fun _ => rfl⟩
  | app sym ts ih =>
    have assemble {ss : List TCsort} (f : FunctionSymbol L E ss .rv)
        (ts : SortedArgs (SortedTerm L E V) ss)
        (hyp : ∀ i, ss.get i = .rv → ∃ u : SortedTerm L E (AuxiliaryInputs L V) (ss.get i),
          u.IsRVOnly ∧ ∀ v, u.realize M (auxiliaryAssignment O v) = (ts i).realize M v)
        (sorts : ∀ i, ss.get i = .rv) :
        ∃ u : SortedTerm L E (AuxiliaryInputs L V) .rv, u.IsRVOnly ∧
          ∀ v, u.realize M (auxiliaryAssignment O v) = (SortedTerm.app f ts).realize M v := by
      choose us onlyRV he using fun i => hyp i (sorts i)
      exact ⟨.app f us,.app f us onlyRV,fun v => congrArg ((M).funMap f) (funext fun i => he i v)⟩
    cases sym with
    | vf => contradiction
    | rv =>
      obtain ⟨f,hf⟩ := pure_term_of_vf O hO P (ts 0) rfl
      exact ⟨.var (s := .rv) (Sum.inr f),.var _,fun v => congrArg (rv O) (hf v).symm⟩
    | _ => apply assemble _ ts ih; intro i; first | exact i.elim0 | solve | simp | fin_cases i <;> rfl

/-- Convention 3.1 in the functional presentation of T. Equality and
the only primitive relation of VF are read from rv(f-g). The output
formula itself uses only auxiliary operations and relations. -/
theorem auxiliary_formula_of_qf {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := K) F)
    (honly : ∀ {n} (r : L.Relations n), ∃ e : n = 2, e ▸ r = F.le)
    {φ : SortedFormula L E V} (hφ : φ.IsQF) :
    ∃ θ : SortedFormula L E (AuxiliaryInputs L V), θ.IsRVOnly ∧
      ∀ v, θ.realize M (auxiliaryAssignment O v) ↔ φ.realize M v := by
  let diff (f g : L.Term (V .vf)) := F.sub.subst ![f,g]
  have hd (f g) (v : Assignment V (CanonicalSort O)) :
      (diff f g).realize (v .vf) = f.realize (v .vf) - g.realize (v .vf) := by
    simp [diff,Term.realize_subst,hF.sub]
  let zero : SortedTerm L E (AuxiliaryInputs L V) .rv := .app .rvZero (fun i => i.elim0)
  have zeroOnly : zero.IsRVOnly := .app _ _ (fun i => i.elim0)
  induction hφ with
  | falsum => exact ⟨.falsum,.falsum,fun _ => Iff.rfl⟩
  | equal t u =>
    rename_i s
    cases s with
    | rv =>
      obtain ⟨t',ht,he⟩ := auxiliary_term O hO P t rfl
      obtain ⟨u',hu,hu'⟩ := auxiliary_term O hO P u rfl
      exact ⟨.equal t' u',.equal ht hu,fun v => by simp only [SortedFormula.realize,he,hu']⟩
    | vf =>
      obtain ⟨f,hf⟩ := pure_term_of_vf O hO P t rfl
      obtain ⟨g,hg⟩ := pure_term_of_vf O hO P u rfl
      refine ⟨.equal (.var (s := .rv) (Sum.inr (diff f g))) zero,.equal (.var _) zeroOnly,fun v => ?_⟩
      change rv O ((diff f g).realize (v .vf)) = 0 ↔ _
      rw [rv_eq_zero_iff,hd,sub_eq_zero]
      exact (congrArg₂ Eq (hf v) (hg v)).symm.to_iff
  | rel sym ts =>
    cases sym with
    | vf r =>
      obtain ⟨rfl,rfl⟩ := honly r
      obtain ⟨f,hf⟩ := pure_term_of_vf O hO P (homogeneousArgs ts 0) rfl
      obtain ⟨g,hg⟩ := pure_term_of_vf O hO P (homogeneousArgs ts 1) rfl
      let args : SortedArgs (SortedTerm L E (AuxiliaryInputs L V)) [.rv,.rv] :=
        expandHomogeneousArgs ![SortedTerm.var (s := .rv) (Sum.inr (diff f g)),zero]
      refine ⟨.rel .rvLE args,.rvLE (fun i => ?_),fun v => ?_⟩
      · fin_cases i
        · exact .var _
        · exact zeroOnly
      · let := rvLinearOrder O hO
        change rv O ((diff f g).realize (v .vf)) ≤ 0 ↔ Structure.RelMap F.le _
        rw [hF.le,hd,← not_lt,zero_lt_rv_iff O hO,not_lt,sub_nonpos]
        exact (congrArg₂ LE.le (hf v) (hg v)).symm.to_iff
    | residueNonzero =>
      choose us hu he using fun i => auxiliary_term O hO P (ts i) (by fin_cases i; rfl)
      exact ⟨.rel .residueNonzero us,.residueNonzero hu,fun v =>
        (congrArg ((M).relMap .residueNonzero) (funext fun i => he i v)).to_iff⟩
    | rvLE =>
      choose us hu he using fun i => auxiliary_term O hO P (ts i) (by fin_cases i <;> rfl)
      exact ⟨.rel .rvLE us,.rvLE hu,fun v =>
        (congrArg ((M).relMap .rvLE) (funext fun i => he i v)).to_iff⟩
  | imp _ _ ha hb =>
    obtain ⟨α,hα,ea⟩ := ha
    obtain ⟨β,hβ,eb⟩ := hb
    exact ⟨.imp α β,.imp hα hβ,fun v => imp_congr (ea v) (eb v)⟩

end GeneralizedEuler.Section3
