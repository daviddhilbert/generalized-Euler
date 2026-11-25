module

public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.Topology.Defs.Basic
public import Section2.Residue
public import Section2.PowerBounded

/-! The valued-field reduct and the external quantifier-elimination input
for Theorem 2.11. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v

/-- The extra language of the valuation-ring predicate. -/
inductive RingPredicate : ℕ → Type
  | mem : RingPredicate 1

abbrev ringPredicateLanguage : Language :=
  ⟨fun _ => Empty, RingPredicate⟩

/-- The language denoted by L_convex in §2.3. -/
abbrev convexLanguage (L : Language.{u, v}) := L.sum ringPredicateLanguage

@[instance_reducible]
def valuationRingPredicate {K : Type*} [Field K] (O : ValuationSubring K) :
    ringPredicateLanguage.Structure K where
  funMap f := f.elim
  RelMap r x := match r with
    | .mem => x 0 ∈ O

@[instance_reducible]
def convexStructure {K : Type*} [Field K] (O : ValuationSubring K)
    (L : Language.{u, v}) [L.Structure K] : (convexLanguage L).Structure K :=
  letI := valuationRingPredicate O
  inferInstance

/-- The graph of a parameter-free function, as a formula with one extra
free variable for the output. The same formula can be evaluated in VF and k. -/
def DefinesTotalFunction {L : Language.{u, v}} {K : Type*} [L.Structure K]
    {n : ℕ} (φ : L.Formula (Option (Fin n))) (f : (Fin n → K) → K) : Prop :=
  ∀ a, φ.Realize a ↔ f (a ∘ some) = a none

/-- Ax. 7 with order convexity included in the definition of a T-convex
valuation ring. The topology on the field is its order topology. -/
def IsTConvex {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] (L : Language.{u, v}) [L.Structure K] (O : ValuationSubring K) : Prop :=
  IsOrderConvex O ∧
    ∀ (φ : L.Formula (Option (Fin 1))) (f : (Fin 1 → K) → K),
      DefinesTotalFunction φ f → Continuous (fun x : K => f (fun _ => x)) →
      ∀ x ∈ O, f (fun _ => x) ∈ O

/-- Ax. 8 in the reviewed language, using the same parameter-free graph
formula in both structures. Lemma 2.12's canonical residue model can
supply the residue structure. -/
def MatchesContinuousFunctions {K : Type*} [Field K] [TopologicalSpace K]
    (L : Language.{u, v}) [L.Structure K] (O : ValuationSubring K)
    [L.Structure (Residue O)] [TopologicalSpace (Residue O)] : Prop :=
  ∀ (n : ℕ) (φ : L.Formula (Option (Fin n))) (f : (Fin n → K) → K),
    DefinesTotalFunction φ f → Continuous f →
    ∃ g : (Fin n → Residue O) → Residue O,
      DefinesTotalFunction φ g ∧ Continuous g ∧
      ∀ a : Fin n → O, ∃ h : f (fun i => (a i : K)) ∈ O,
        IsLocalRing.residue O ⟨f (fun i => (a i : K)), h⟩ =
          g (fun i => IsLocalRing.residue O (a i))

/-- Quantifier elimination, stated with Mathlib formulas and semantic
entailment. The free variables of each formula form a finite tuple. -/
def EliminatesQuantifiers {L : Language.{u, v}} (T : L.Theory) : Prop :=
  ∀ (n : ℕ) (φ : L.Formula (Fin n)),
    ∃ ψ : L.Formula (Fin n), ψ.IsQF ∧ T ⊨ᵇ φ.iff ψ

theorem realizes_iff_of_entails {L : Language.{u, v}} {T : L.Theory}
    {K : Type*} [L.Structure K] [K ⊨ T] [Nonempty K]
    {n : ℕ} {φ ψ : L.Formula (Fin n)} (h : T ⊨ᵇ φ.iff ψ) (x : Fin n → K) :
    φ.Realize x ↔ ψ.Realize x :=
  Formula.realize_iff.mp (h.realize_formula K)

/-- An embedding of models of a theory with QE is elementary. -/
def elementaryEmbeddingOfQE {L : Language.{u, v}} {T : L.Theory}
    {K F : Type*} [L.Structure K] [L.Structure F] [K ⊨ T] [F ⊨ T]
    [Nonempty K] [Nonempty F] (hT : EliminatesQuantifiers T) (ι : K ↪[L] F) :
    K ↪ₑ[L] F where
  toFun := ι
  map_formula' := by
    intro n φ x
    obtain ⟨ψ, hψ, h⟩ := hT n φ
    have hEmbedding := hψ.realize_embedding ι (v := x) (xs := default)
    have hEmpty : ι ∘ (default : Fin 0 → K) = (default : Fin 0 → F) :=
      Subsingleton.elim _ _
    rw [hEmpty] at hEmbedding
    exact (realizes_iff_of_entails h (ι ∘ x)).trans
      (hEmbedding.trans (realizes_iff_of_entails h x).symm)

/-- The external input of Theorem 2.11 for the theory of proper T-convex
pairs, from van den Dries–Lewenberg (1995), Theorem 3.10 and Corollary 3.13. -/
structure ConvexTheoryFacts {L : Language.{u, v}} (Tconvex : (convexLanguage L).Theory) : Prop where
  quantifierElimination : EliminatesQuantifiers Tconvex
  complete : Tconvex.IsComplete

end GeneralizedEuler.Section2
