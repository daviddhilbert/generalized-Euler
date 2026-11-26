module

public import Section5.FieldRVFiberRows
public import Section5.RelativeBlowupPathDescent

/-! Constancy of both endpoint families of the chosen paths implies
membership constancy in the original mixed sets, with no choice of
representatives on the RV sort. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder RelativeObjectFamily RelativeRVTest

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {k a : ℕ}

local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

theorem RetainedFieldFamily.unaryCarrier_constant_of_rows
    (A : RetainedFieldFamily M S 1 k) (idx : Fin a ≃ A.tags) (zero : S.carrier .rv)
    (bounds : Finset (Fin k) → ℕ) {H : Type*} (T : UnaryPreparation O H)
    (D : Set (SortedAssignment Z P))
    (contains : ∀ p u, appendAssignments p u ∈ A.fieldFiberTags idx → p ∈ D)
    (agree : ∀ (p p' : SortedAssignment Z P), p ∈ D → T.label (p .vf 0) = T.label (p' .vf 0) →
      Agree (RelativeObjectFamily.tests (A.orderedFieldFiberRows idx zero bounds)) p p') :
    ∀ x y (t : A.tags → RV0 O), T.label x = T.label y →
      (((fun _ => x),t) ∈ A.carrier ↔ ((fun _ => y),t) ∈ A.carrier) := by
  intro x y t labels
  let field (z : K) : SortedAssignment Z P := fieldTupleAssignment (fun _ => z)
  let u : SortedAssignment Z (RVVariables (Fin a)) := rvTupleAssignment (t ∘ idx)
  have coords : (t ∘ idx) ∘ idx.symm = t := by
    funext i
    exact congrArg t (idx.apply_symm_apply i)
  have test (z : K) : appendAssignments (field z) u ∈ A.fieldFiberTags idx ↔ ((fun _ => z),t) ∈ A.carrier := by
    change ((fun _ => z),(t ∘ idx) ∘ idx.symm) ∈ A.carrier ↔ _
    rw [coords]
  have transport (z w : K) (same : T.label z = T.label w) (mem : ((fun _ => z),t) ∈ A.carrier) :
      ((fun _ => w),t) ∈ A.carrier := by
    have hz := (test z).2 mem
    have d := contains (field z) u hz
    exact (test w).1 ((A.fieldFiberTags_agree_of_rows idx zero bounds (agree (field z) (field w) d same) u).1 hz)
  exact ⟨transport x y labels,transport y x labels.symm⟩

end GeneralizedEuler.Section5
