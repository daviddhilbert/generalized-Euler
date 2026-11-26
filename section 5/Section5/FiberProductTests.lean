module

public import Section5.HeadContractionIteration
public import Section5.DefinableBijectionSchemes
public import Section5.MixedFiniteFamilies
public import Section4.Objects

/-! Projection to either field coordinate and the assertion that
a two-coordinate fiber is its product of projections are definable
over the original base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {k : ℕ}

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S 2 k)
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty
local notation "R" => RVVariables A.tags

@[expose] def factorProjection (i : Fin 2) : Set (K × (A.tags → RV0 O)) :=
  {p | ∃ b : Fin 2 → K, (b,p.2) ∈ A.carrier ∧ b i = p.1}

theorem factorProjection_definable (i : Fin 2) :
    SortedDefinableOver M S.carrier
      {a : SortedAssignment Z (SumVariables R U) | (a .vf (.inr 0),a .rv ∘ Sum.inl) ∈ A.factorProjection i} := by
  let W := SumVariables (SumVariables R U) (MixedVariables 2 Empty)
  let take : (s : TCsort) → MixedVariables 2 A.tags s → W s
    | .vf => Sum.inr
    | .rv => Sum.inl ∘ Sum.inl
  have src := A.definable.pullback_relabel take
  have value := SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W)
    .vf (.inr i) (.inl (.inr 0))
  convert definable_project_mixed (src.inter value) using 1
  ext a
  simp only [Set.mem_inter_iff]
  change (∃ b : Fin 2 → K, (b,a .rv ∘ Sum.inl) ∈ A.carrier ∧ b i = a .vf (.inr 0)) ↔
    ∃ b : fieldAssignment 2 Z, (b .vf,a .rv ∘ Sum.inl) ∈ A.carrier ∧ b .vf i = a .vf (.inr 0)
  exact ⟨fun ⟨b,h,e⟩ => ⟨fieldTupleAssignment b,h,e⟩,fun ⟨b,h,e⟩ => ⟨b .vf,h,e⟩⟩

theorem factorProjection_mixed_definable (i : Fin 2) :
    SortedDefinableOver M S.carrier
      {a : SortedAssignment Z (MixedVariables 1 A.tags) | (a .vf 0,a .rv) ∈ A.factorProjection i} := by
  let take : (s : TCsort) → SumVariables R U s → MixedVariables 1 A.tags s
    | .vf => Sum.elim PEmpty.elim id
    | .rv => Sum.elim id Empty.elim
  exact (A.factorProjection_definable i).pullback_relabel take

@[expose] def productFibers : Set (A.tags → RV0 O) :=
  {q | ∀ b : Fin 2 → K, (b 0,q) ∈ A.factorProjection 0 → (b 1,q) ∈ A.factorProjection 1 → (b,q) ∈ A.carrier}

theorem productFibers_definable :
    isRVSet M S A.productFibers := by
  let W := SumVariables R (MixedVariables 2 Empty)
  let take : (s : TCsort) → MixedVariables 2 A.tags s → W s
    | .vf => Sum.inr
    | .rv => Sum.inl
  let one (i : Fin 2) (s : TCsort) : SumVariables R U s → W s :=
    match s with
    | .vf => Sum.elim Sum.inl (fun _ => .inr i)
    | .rv => Sum.elim Sum.inl (Sum.inr ∘ Empty.elim)
  have both := ((A.factorProjection_definable 0).pullback_relabel (one 0)).inter
    ((A.factorProjection_definable 1).pullback_relabel (one 1))
  have src := A.definable.pullback_relabel take
  unfold isRVSet
  convert definable_forall_assignments (both.compl.union src) using 1
  ext q
  change (∀ b : Fin 2 → K, (b 0,q .rv) ∈ A.factorProjection 0 → (b 1,q .rv) ∈ A.factorProjection 1 →
      (b,q .rv) ∈ A.carrier) ↔
    ∀ b : fieldAssignment 2 Z, ¬ ((b .vf 0,q .rv) ∈ A.factorProjection 0 ∧
      (b .vf 1,q .rv) ∈ A.factorProjection 1) ∨ (b .vf,q .rv) ∈ A.carrier
  classical
  constructor
  · intro all b
    by_cases both : (b .vf 0,q .rv) ∈ A.factorProjection 0 ∧ (b .vf 1,q .rv) ∈ A.factorProjection 1
    · exact .inr (all (b .vf) both.1 both.2)
    · exact .inl both
  · intro all b one two
    exact (all (fieldTupleAssignment b)).elim (fun f => (f ⟨one,two⟩).elim) id

theorem carrier_on_productFibers (t : A.tags → RV0 O) (b : Fin 2 → K)
    (h : t ∈ A.productFibers) :
    (b,t) ∈ A.carrier ↔ (b 0,t) ∈ A.factorProjection 0 ∧ (b 1,t) ∈ A.factorProjection 1 :=
  ⟨fun h => ⟨⟨b,h,rfl⟩,⟨b,h,rfl⟩⟩,fun p => h b p.1 p.2⟩

end RetainedFieldFamily

end GeneralizedEuler.Section5
