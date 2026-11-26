module

public import Section5.MixedFiberFiniteness
public import Section5.PreparedMapOperations

/-! A definable mixed set with finite RV fibers is a retained-field
family with empty head start. Its original defining graph is unchanged. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n : ℕ} {I : Type}

local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables n I

/-- Assemble a mixed assignment from a field tuple and an RV tuple. -/
@[expose] def mixedAssignment (x : Fin n → K) (r : I → RV0 O) : SortedAssignment Z U
  | .vf => x
  | .rv => r

theorem mixedAssignment_eta (a : SortedAssignment Z U) : mixedAssignment (a .vf) (a .rv) = a := by
  funext s i
  cases s <;> rfl

namespace RetainedFieldFamily

variable [Finite I] (D : MixedCarrier (CanonicalSort O) n I)
  (defD : SortedDefinableOver M S.carrier D)
  (finite : ∀ x : Fin n → K, {a : D | a.val .vf = x}.Finite)

@[expose] def ofFiniteMixedCarrier : RetainedFieldFamily M S n 0 where
  tags := I
  finiteTags := inferInstance
  select := Fin.elim0
  carrier := {p | mixedAssignment p.1 p.2 ∈ D}
  definable := by
    convert defD using 1
    ext a
    change mixedAssignment (a .vf) (a .rv) ∈ D ↔ a ∈ D
    rw [mixedAssignment_eta]
  finiteFibers x v := by
    apply ((finite x).image (fun a : D => a.val .rv)).subset
    rintro r ⟨h,_⟩
    exact ⟨⟨mixedAssignment x r,h⟩,rfl,rfl⟩

theorem ofFiniteMixedCarrier_as_set :
    {a : SortedAssignment Z U | mixedTuple a ∈ (ofFiniteMixedCarrier D defD finite).carrier} = D := by
  ext a
  change mixedAssignment (a .vf) (a .rv) ∈ D ↔ a ∈ D
  rw [mixedAssignment_eta]

end RetainedFieldFamily

end GeneralizedEuler.Section5
