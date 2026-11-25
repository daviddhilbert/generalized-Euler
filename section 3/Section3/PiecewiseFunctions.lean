module

public import Section3.FiniteAuxiliaryForm
public import Section3.OrderedBranches
import all Section3.DefinablePartitions

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

universe u v w
variable {K : Type u} {L : Language} {E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K] [L.Structure K] (O : ValuationSubring K)
    [L.Structure (Residue O)] (hO : IsOrderConvex O) (powers : E → RV0 O → RV0 O)
    {I J : Type v}

abbrev FunctionGraphVars (I J : Type v) : TCsort → Type v
  | .vf => Option I
  | .rv => J

abbrev graphAssignment (x : I → K) (t : J → RV0 O) (y : K) :
    ∀ s, FunctionGraphVars I J s → CanonicalSort O s
  | .vf => (Option.elim · y x)
  | .rv => t

/-- Lemma 3.3 with auxiliary arguments retained. Sorted quantifier
elimination gives the finite pure terms. Unary o-minimality supplies a
uniformly finite definable critical family for those terms. Its ordered
enumeration gives pure-field branches and the first agreeing branch
partitions the domain. The free field coordinates include any named field
parameters, independently of the auxiliary tuple. -/
theorem piecewise_field_functions_of_qe (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := K) F)
    (only : ∀ {n} (r : L.Relations n), ∃ e : n = 2, e ▸ r = F.le)
    (f : (I → K) → (J → RV0 O) → K) (φ : SortedFormula L E (FunctionGraphVars I J))
    (graph : ∀ x t y, φ.realize (canonicalStructure (L := L) O hO powers) (graphAssignment O x t y) ↔ y = f x t)
    (qe : ∃ ψ : SortedFormula L E (FunctionGraphVars I J), ψ.IsQF ∧
      ∀ v, ψ.realize (canonicalStructure (L := L) O hO powers) v ↔ φ.realize (canonicalStructure (L := L) O hO powers) v)
    {e : K} (he : 0 < e) (heO : O.valuation e < 1)
    (critical : ∀ T : Finset (L.Term (Option I)), ∃ (N : ℕ) (S : (I → K) → Finset K),
      (∅ : Set K).Definable L {v : Option I → K | v none ∈ S (v ∘ some)} ∧ (∀ a, (S a).card ≤ N) ∧
      ∀ a (j : T), criticalSet (fun y => j.val.realize (Option.elim · y a)) ⊆ S a) :
    ∃ (N : ℕ) (g : Fin N → (I → K) → K), (∀ i, (∅ : Set K).DefinableFun L (g i)) ∧
      (∀ a t, ∃! i, f a t = g i a ∧ ∀ j < i, f a t ≠ g j a) ∧
      ∀ a, (range (f a)).Finite := by
  obtain ⟨T,θ,_,hθ⟩ := finite_auxiliary_normal_form O hO powers F hF only φ qe
  let terms (i : T) (x : I → K) (y : K) := i.val.realize (Option.elim · y x)
  have isolate (x : I → K) (t : J → RV0 O) (y : K)
      (same : ∀ i, rv O (terms i x y) = rv O (terms i x (f x t))) : y = f x t := by
    let M := canonicalStructure (L := L) O hO powers
    let v := graphAssignment O x t y
    let v' := graphAssignment O x t (f x t)
    let args (a : K) : ∀ s, RVVariables (J ⊕ T) s → CanonicalSort O s
      | .vf => PEmpty.elim
      | .rv => Sum.elim t (fun j => rv O (terms j x a))
    have eqArgs : args y = args (f x t) := by
      funext s b
      cases s with
      | vf => exact b.elim
      | rv => cases b with
              | inl j => rfl
              | inr j => exact same j
    apply (graph x t y).mp
    apply (hθ v).mpr
    change θ.realize M (args y)
    rw [eqArgs]
    exact (hθ v').mp ((graph x t _).mpr rfl)
  obtain ⟨N,S,dS,bound,cov⟩ := critical T
  have member (a) (t) : f a t ∈ S a := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp (graph_output_mem_critical O hO he heO f terms isolate a t)
    exact cov a j hj
  obtain ⟨g,dg,cover⟩ := ordered_branches_of_finite_family F hF N S dS bound
  refine ⟨N,g,dg,fun a t => ?_,fun a => (S a).finite_toSet.subset (by
    rintro _ ⟨t,rfl⟩; exact member a t)⟩
  apply firstChoice_partition (fun _ : Unit => f a t) (fun i _ => g i a) _ ()
  intro _
  obtain ⟨i,hi⟩ := cover a _ (member a t)
  exact ⟨i,hi.symm⟩

end GeneralizedEuler.Section3
