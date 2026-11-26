module

public import Section5.FieldPartitionLabels
public import Section5.TagRestrictedContractions

/-! An arbitrary definable cut becomes a cut on the RV tags after
recording the indicator of its partition part. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

local notation "Z" => CanonicalSort O

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S n k)
  (D : MixedCarrier (CanonicalSort O) n A.tags)
  (d : SortedDefinableOver M S.carrier D)
  (sub : D ⊆ {a : SortedAssignment (CanonicalSort O) (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier})

@[expose] def cutCarrier : RetainedFieldFamily M S n k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := {p | mixedAssignment p.1 p.2 ∈ D}
  definable := by
    convert d using 1
    ext a
    change mixedAssignment (a .vf) (a .rv) ∈ D ↔ a ∈ D
    rw [mixedAssignment_eta]
  finiteFibers x v := (A.finiteFibers x v).subset (fun _ h => ⟨sub h.1,h.2⟩)

theorem cutCarrier_as_set :
    {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ (A.cutCarrier D d sub).carrier} = D := by
  ext a
  change mixedAssignment (a .vf) (a .rv) ∈ D ↔ a ∈ D
  rw [mixedAssignment_eta]

end RetainedFieldFamily

end GeneralizedEuler.Section5
