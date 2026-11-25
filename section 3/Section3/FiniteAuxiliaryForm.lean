module

public import Section3.AuxiliaryNormalForm
import all Section2.SortedSyntax

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language
universe u v w a z

variable {L : Language.{u,v}} {E : Type w} {V : TCsort → Type a}
  {X : TCsort → Type z} (M : SortedStructure L E X)

private def Supported {Y : Sort*} {B : Type*} (f : Assignment (RVVariables B) X → Y) : Prop :=
  ∃ T : Finset B, ∀ v w, (∀ b ∈ T, v .rv b = w .rv b) → f v = f w

private theorem supported_app {B I : Type*} [Fintype I] {Y : Sort*} {Z : I → Type*}
    (f : ((i : I) → Z i) → Y) (args : (i : I) → Assignment (RVVariables B) X → Z i)
    (hs : ∀ i, Supported (args i)) : Supported (fun v => f (fun i => args i v)) := by
  classical
  choose ts ht using hs
  exact ⟨Finset.univ.biUnion ts,fun v w h => congrArg f (funext fun i =>
    ht i v w (fun b hb => h b (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hb⟩)))⟩

private theorem support_term {B : Type*} {s} {t : SortedTerm L E (RVVariables B) s}
    (h : t.IsRVOnly) : Supported (fun v => t.realize M v) := by
  classical
  induction h with
  | var i => exact ⟨{i},fun _ _ h => h i (Finset.mem_singleton_self _)⟩
  | app f ts _ ih => exact supported_app (M.funMap f) (fun i v => (ts i).realize M v) ih

private theorem support_formula {B : Type*} {φ : SortedFormula L E (RVVariables B)}
    (h : φ.IsRVOnly) : Supported (fun v => φ.realize M v) := by
  classical
  induction h with
  | falsum => exact ⟨∅,fun _ _ _ => rfl⟩
  | equal ht hu =>
    obtain ⟨T,ha⟩ := support_term M ht
    obtain ⟨U,hb⟩ := support_term M hu
    exact ⟨T ∪ U,fun v w h => congrArg₂ Eq (ha v w (fun i hi => h i (Finset.mem_union_left U hi)))
      (hb v w (fun i hi => h i (Finset.mem_union_right T hi)))⟩
  | residueNonzero ht =>
    exact supported_app (M.relMap .residueNonzero) _ (fun i => support_term M (ht i))
  | rvLE ht => exact supported_app (M.relMap .rvLE) _ (fun i => support_term M (ht i))
  | imp _ _ ha hb =>
    obtain ⟨T,ha⟩ := ha
    obtain ⟨U,hb⟩ := hb
    exact ⟨T ∪ U,fun v w h => congrArg₂ (fun p q : Prop => p → q)
      (ha v w (fun i hi => h i (Finset.mem_union_left U hi)))
      (hb v w (fun i hi => h i (Finset.mem_union_right T hi)))⟩

private theorem onlyTerm_relabel {W : TCsort → Type*} (r : ∀ s, V s → W s)
    {s} {t : SortedTerm L E V s} (h : t.IsRVOnly) : (t.relabel r).IsRVOnly := by
  induction h with
  | var => exact .var _
  | app f ts _ ih => exact .app f _ ih

private theorem onlyFormula_relabel {W : TCsort → Type*} (r : ∀ s, V s → W s)
    {φ : SortedFormula L E V} (h : φ.IsRVOnly) : (φ.relabel r).IsRVOnly := by
  induction h with
  | falsum => exact .falsum
  | equal ht hu => exact .equal (onlyTerm_relabel r ht) (onlyTerm_relabel r hu)
  | residueNonzero ht => exact .residueNonzero (fun i => onlyTerm_relabel r (ht i))
  | rvLE ht => exact .rvLE (fun i => onlyTerm_relabel r (ht i))
  | imp _ _ ha hb => exact .imp ha hb

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

local notation "C" => canonicalStructure (L := L) O hO P

/-- The displayed formula of Convention 3.1. The auxiliary formula is
indexed by a *finite set of pure field terms*. An arbitrary sorted formula
enters via its quantifier-free equivalent from Section 2. -/
theorem finite_auxiliary_normal_form (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := K) F)
    (honly : ∀ {n} (r : L.Relations n), ∃ e : n = 2, e ▸ r = F.le)
    (φ : SortedFormula L E V)
    (qe : ∃ ψ : SortedFormula L E V, ψ.IsQF ∧ ∀ v, ψ.realize C v ↔ φ.realize C v) :
    ∃ T : Finset (L.Term (V .vf)), ∃ θ : SortedFormula L E (RVVariables (V .rv ⊕ T)),
      θ.IsRVOnly ∧ ∀ v, φ.realize C v ↔ θ.realize C (fun s => match s with
        | .vf => PEmpty.elim
        | .rv => Sum.elim (v .rv) (fun t : T => rv O (t.val.realize (v .vf)))) := by
  classical
  obtain ⟨ψ,hq,he⟩ := qe
  obtain ⟨aux,ho,haux⟩ := auxiliary_formula_of_qf O hO P hF honly hq
  obtain ⟨S,hs⟩ := support_formula C ho
  let fallback : L.Term (V .vf) := F.zero.relabel Empty.elim
  let T := insert fallback (S.image (Sum.elim (fun _ => fallback) id))
  have first : fallback ∈ T := Finset.mem_insert_self _ _
  let pick (t : L.Term (V .vf)) : T := if h : t ∈ T then ⟨t,h⟩ else ⟨fallback,first⟩
  let r (s) : AuxiliaryInputs L V s → RVVariables (V .rv ⊕ T) s := match s with
    | .vf => PEmpty.elim
    | .rv => Sum.map id pick
  refine ⟨T,aux.relabel r,onlyFormula_relabel r ho,fun v => ?_⟩
  rw [SortedFormula.realize_relabel]
  apply ((he v).symm.trans (haux v).symm).trans
  apply Eq.to_iff
  apply hs
  intro i hi
  rcases i with b | t
  · rfl
  · have ht : t ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Sum.inr t,hi,rfl⟩)
    change rv O (t.realize _) = rv O ((pick t).val.realize _)
    simp [pick,ht]

end GeneralizedEuler.Section3
