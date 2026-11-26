module

public import Section5.HeadStartZeroPatterns
public import Section5.RelativeRVRows

/-! The old head-start tuple is a retained RV index once its zero
pattern is fixed. The selected nonzero entries determine it. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k t : ℕ}

theorem all_rv_tuples_definable : isRVSet M S (Set.univ : Set (Fin k → X .rv)) :=
  ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩

@[expose] def oldHeadPatternIndex (keep : Fin t → Fin k) (zero : S.carrier .rv)
    (hz : zero.val = M.funMap .rvZero (fun i => i.elim0)) : RelativeRVIndex M S k t where
  labels := headStartStratum id keep zero.val Set.univ
  definable := headStartStratum_definable id keep zero all_rv_tuples_definable
  select := keep
  active _ hp i := hz ▸ headStartStratum_nonzero id keep hp i
  finite := headStartStratum_finite_indices id keep zero.val Set.univ (fun v =>
    (Set.finite_singleton v).subset (fun _ h => h.2))

/-- Enumerate a fixed nonzero pattern of the old selected tuple. -/
noncomputable def oldHeadSupportIndex (support : Finset (Fin k)) (zero : S.carrier .rv)
    (hz : zero.val = M.funMap .rvZero (fun i => i.elim0)) : RelativeRVIndex M S k (Fintype.card {i // i ∈ support}) :=
  oldHeadPatternIndex (Subtype.val ∘ (Fintype.equivFin {i // i ∈ support}).symm) zero hz

end GeneralizedEuler.Section5
