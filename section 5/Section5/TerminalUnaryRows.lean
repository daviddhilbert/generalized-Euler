module

public import Section5.HeadContractionEndpoints
public import Section5.ProjectedRelativeObjects
public import Section5.RelativeObjectFamilies

/-! The terminal tags of a unary contraction have two uniform rows over
the old head start. A zero last leading term yields degree zero in the
fiber and a nonzero last leading term yields degree one. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {a k : ℕ}

namespace RetainedFieldFamily

variable (B : RetainedFieldFamily M S 0 (k+1)) (tags : Fin a ≃ B.tags)

local notation "Z" => CanonicalSort O
local notation "P" => RVVariables (Fin k)
local notation "U" => RVVariables (Fin a)

@[expose] def terminalOldHead : Fin k → Fin a := B.terminalSelect tags ∘ Fin.castSucc

@[expose] def terminalNewLead : Fin a := B.terminalSelect tags (Fin.last k)

@[expose] def terminalBaseTags : Set (SortedAssignment Z (SumVariables P U)) :=
  {p | p .rv ∘ Sum.inr ∈ B.terminalLabels tags ∧ (p .rv ∘ Sum.inr) ∘ B.terminalOldHead tags = p .rv ∘ Sum.inl}

theorem terminalBaseTags_definable : SortedDefinableOver M S.carrier (B.terminalBaseTags tags) := by
  let W := SumVariables P U
  let take (s : TCsort) : U s → W s := Sum.inr
  have d := (B.terminalLabels_definable tags).pullback_relabel take
  have eqs := SortedDefinableOver.iInter (fun i : Fin k => SortedDefinableOver.coordinate_eq
    (M := M) (A := S.carrier) (Var := W) .rv (.inr (B.terminalOldHead tags i)) (.inl i))
  convert d.inter eqs using 1
  ext a
  simp only [terminalBaseTags,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  exact and_congr_right (fun _ => ⟨congrFun,funext⟩)

variable (zero : S.carrier .rv)

@[expose] def terminalZeroTags : Set (SortedAssignment Z (SumVariables P U)) :=
  B.terminalBaseTags tags ∩ {p | p .rv (.inr (B.terminalNewLead tags)) = zero.val}

@[expose] def terminalNonzeroTags : Set (SortedAssignment Z (SumVariables P U)) :=
  B.terminalBaseTags tags ∩ {p | p .rv (.inr (B.terminalNewLead tags)) ≠ zero.val}

theorem terminalZeroTags_definable : SortedDefinableOver M S.carrier (B.terminalZeroTags tags zero) :=
  (B.terminalBaseTags_definable tags).inter (SortedDefinableOver.coordinate_eq_parameter .rv _ zero)

theorem terminalNonzeroTags_definable : SortedDefinableOver M S.carrier (B.terminalNonzeroTags tags zero) :=
  (B.terminalBaseTags_definable tags).inter (SortedDefinableOver.coordinate_eq_parameter .rv _ zero).compl

theorem terminalBaseTags_finite (p : SortedAssignment Z P) (u : RV0 O) :
    {x : SortedAssignment Z U | appendAssignments p x ∈ B.terminalBaseTags tags ∧ x .rv (B.terminalNewLead tags) = u}.Finite := by
  let label : Fin (k+1) → RV0 O := Fin.lastCases u (p .rv)
  have inj : Function.Injective (fun x : SortedAssignment Z U => x .rv) := by
    intro a b e
    funext s i
    cases s
    · exact i.elim
    · exact congrFun e i
  apply ((B.terminalLabels_finite tags label).preimage inj.injOn).subset
  intro x hx
  change (x .rv ∈ B.terminalLabels tags ∧ x .rv ∘ B.terminalOldHead tags = p .rv) ∧
    x .rv (B.terminalNewLead tags) = u at hx
  refine ⟨hx.1.1,funext (Fin.lastCases ?_ (fun i => ?_))⟩
  · simpa only [Function.comp_apply,label,Fin.lastCases_last,terminalNewLead] using hx.2
  · simpa only [Function.comp_apply,label,Fin.lastCases_castSucc,terminalOldHead] using congrFun hx.1.2 i

theorem terminalZeroProjection_valid
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (SumVariables P (RVVariables (Fin 0))))
      (BaseAssignments S.carrier (SumVariables P (RVVariables (Fin 0))))) :
    ∃ bound, ∀ p, (RelativeRVObjectScheme.ofProjection (B.terminalZeroTags_definable tags zero) Fin.elim0 bound).valid zero p := by
  apply relative_projection_scheme_valid _ _ zero (fun _ _ _ j => j.elim0) _ sat
  intro p v
  apply (B.terminalBaseTags_finite tags p zero.val).subset
  intro x hx
  exact hx.1

theorem terminalNonzeroProjection_valid
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (SumVariables P (RVVariables (Fin 1))))
      (BaseAssignments S.carrier (SumVariables P (RVVariables (Fin 1))))) :
    ∃ bound, ∀ p, (RelativeRVObjectScheme.ofProjection (B.terminalNonzeroTags_definable tags zero)
      (fun _ : Fin 1 => B.terminalNewLead tags) bound).valid zero p := by
  apply relative_projection_scheme_valid _ _ zero (fun _ _ h _ => h.2) _ sat
  intro p v
  apply (B.terminalBaseTags_finite tags p (v .rv 0)).subset
  intro x hx
  exact ⟨hx.1.1,(congrFun hx.2 0).symm⟩

@[expose] def terminalUnaryRows (zeroBound nonzeroBound : ℕ) : RelativeObjectFamily M S P (Fin 2) :=
  Fin.cases (RelativeRVObjectScheme.ofProjection (B.terminalZeroTags_definable tags zero) Fin.elim0 zeroBound)
    (fun _ => RelativeRVObjectScheme.ofProjection (B.terminalNonzeroTags_definable tags zero)
      (fun _ : Fin 1 => B.terminalNewLead tags) nonzeroBound)

theorem terminalUnaryRows_valid
    (sat : ∀ d, RealizesFinitelySatisfiableTypes M (WithBase S.carrier (SumVariables P (RVVariables (Fin d))))
      (BaseAssignments S.carrier (SumVariables P (RVVariables (Fin d))))) :
    ∃ bound₀ bound₁, ∀ p, Valid (B.terminalUnaryRows tags zero bound₀ bound₁) zero p := by
  obtain ⟨b₀,h₀⟩ := B.terminalZeroProjection_valid tags zero (sat 0)
  obtain ⟨b₁,h₁⟩ := B.terminalNonzeroProjection_valid tags zero (sat 1)
  refine ⟨b₀,b₁,fun p => ?_⟩
  exact Fin.cases (h₀ p) (fun _ => h₁ p)

end RetainedFieldFamily

end GeneralizedEuler.Section5
