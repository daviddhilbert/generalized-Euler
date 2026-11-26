module

public import Section5.MixedFiniteFamilies

/-! A mixed bijection preserving the selected tuple carries a
retained-field family to one with the same head start. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

section Generic

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

local notation "Z" => CanonicalSort O

theorem RetainedFieldFamily.finiteAssignedFiber (A : RetainedFieldFamily M S n k)
    (x : Fin n → K) (v : Fin k → RV0 O) :
    {a : {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier} |
      a.val .vf = x ∧ a.val .rv ∘ A.select = v}.Finite := by
  apply (A.finiteFibers x v).of_injOn (f := fun a => a.val .rv)
  · rintro a ⟨hx,hv⟩
    exact ⟨hx ▸ a.property,hv⟩
  · rintro a ⟨ha,_⟩ b ⟨hb,_⟩ e
    exact Subtype.ext (mixedTuple_injective (Prod.ext (ha.trans hb.symm) e))

end Generic

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n m k : ℕ} {J : Type} [Finite J]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S n k)
  (D : MixedCarrier (CanonicalSort O) m J) (select : Fin k → J)

@[expose] def RetainedFieldFamily.ofRelativeIso
    (hyp : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (default : S.carrier .vf)
    (f : MixedGraphIso 𝓜 S {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier} D)
    (keep : ∀ x, (f.equiv x).val .rv ∘ select = x.val .rv ∘ A.select) :
    RetainedFieldFamily 𝓜 S m k where
  tags := J
  finiteTags := inferInstance
  select := select
  carrier := {p | mixedAssignment p.1 p.2 ∈ D}
  definable := by
    let : Finite A.tags := A.finiteTags
    convert f.target_definable A.definable using 1
    ext a
    change mixedAssignment (a .vf) (a .rv) ∈ D ↔ a ∈ D
    rw [mixedAssignment_eta]
  finiteFibers x v := by
    let : Finite A.tags := A.finiteTags
    have finite := f.target_finiteFieldFibers_over O hO power S hyp he small default
      (fun x => x.val .rv ∘ A.select) (fun y => y.val .rv ∘ select) keep A.finiteAssignedFiber x v
    apply (finite.image (fun a => a.val .rv)).subset
    rintro t ⟨ht,hv⟩
    exact ⟨⟨mixedAssignment x t,ht⟩,⟨rfl,hv⟩,rfl⟩

end GeneralizedEuler.Section5
