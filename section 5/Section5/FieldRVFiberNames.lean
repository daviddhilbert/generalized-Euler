module

public import Section5.UnaryTerminalSupports

/-! Freezing the entire field tuple of a retained family leaves a
finite-to-one RV family over the generated base. Its carrier has a
fixed-base relative formula in the field parameters and RV tags. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k a : ℕ}

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S n k) (idx : Fin a ≃ A.tags)

local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables n Empty
local notation "U" => RVVariables (Fin a)

@[expose] def fieldFiberTags : Set (SortedAssignment Z (SumVariables P U)) :=
  {r | (r .vf ∘ Sum.inl,r .rv ∘ Sum.inr ∘ idx.symm) ∈ A.carrier}

theorem fieldFiberTags_definable : SortedDefinableOver M S.carrier (A.fieldFiberTags idx) := by
  let rename : (s : TCsort) → MixedVariables n A.tags s → SumVariables P U s
    | .vf => Sum.inl
    | .rv => Sum.inr ∘ idx.symm
  exact A.definable.pullback_relabel rename

@[expose] def atFieldTuple (p : SortedAssignment Z P) :
    RetainedFieldFamily M (M.termGenerated (namedTuple S p)) 0 k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := {x | (p .vf,x.2) ∈ A.carrier}
  definable := by
    let U₀ := MixedVariables 0 A.tags
    let relabel : (s : TCsort) → MixedVariables n A.tags s → SumVariables P U₀ s
      | .vf => Sum.inl
      | .rv => Sum.inr
    exact definable_scheme_at_fiber p _ (A.definable.pullback_relabel relabel)
  finiteFibers _ := A.finiteFibers (p .vf)

theorem mem_fieldFiberTags (p : SortedAssignment Z P) (x : SortedAssignment Z U) :
    appendAssignments p x ∈ A.fieldFiberTags idx ↔ x .rv ∈ (A.atFieldTuple p).terminalLabels idx :=
  Iff.rfl

theorem fieldFiberTags_eq_union_supports
    (p : SortedAssignment Z P) (zero : S.carrier .rv) (x : SortedAssignment Z U) :
    appendAssignments p x ∈ A.fieldFiberTags idx ↔
      ∃ support : Finset (Fin k),
        appendAssignments p x ∈ A.fieldFiberTags idx ∧
          ∀ i, x .rv (idx.symm (A.select i)) ≠ zero.val ↔ i ∈ support := by
  classical
  constructor
  · intro hx
    exact ⟨Finset.univ.filter (fun i => x .rv (idx.symm (A.select i)) ≠ zero.val),hx,fun i => by simp⟩
  · rintro ⟨_,hx,_⟩
    exact hx

end RetainedFieldFamily

end GeneralizedEuler.Section5
