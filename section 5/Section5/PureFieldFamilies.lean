module

public import Section5.TranslationHeadContractions
public import Section5.DefinableCellTranslations
public import Section5.UnaryProductContractions

/-! View a pure field set as a retained family with no original RV
tags. This is the family of a two-cell after its label is fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n : ℕ}

local notation "Z" => CanonicalSort O

namespace RetainedFieldFamily

@[expose] def pureFields
    (D : Set (fieldAssignment n Z)) (defD : SortedDefinableOver M S.carrier D) : RetainedFieldFamily M S n 0 where
  tags := Empty
  finiteTags := inferInstance
  select := Fin.elim0
  carrier := {p | fieldTupleAssignment p.1 ∈ D}
  definable := by
    convert defD using 1
    ext a
    have e : fieldTupleAssignment (a .vf) = a := fieldAssignment_ext (fun _ => rfl)
    exact (congrArg (· ∈ D) e).to_iff
  finiteFibers _ _ := Set.toFinite _

end RetainedFieldFamily

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def RetainedFieldFamily.fieldPairSet (D : Set (K × K))
    (defD : SortedDefinableOver 𝓜 S₀.carrier (fieldPairAssignment O ⁻¹' D)) : RetainedFieldFamily 𝓜 S₀ 2 0 :=
  pureFields _ defD

theorem RetainedFieldFamily.fieldPairSet_vertical (D : Set (K × K))
    (defD : SortedDefinableOver 𝓜 S₀.carrier (fieldPairAssignment O ⁻¹' D))
    (x : K) (b : Fin 1 → K) (t : Empty → RV0 O) :
    (x,b,t) ∈ (fieldPairSet hO power S₀ D defD).verticalCarrier ↔ (x,b 0) ∈ D :=
  Iff.rfl

theorem RetainedFieldFamily.fieldPairSet_swapped_vertical (D : Set (K × K))
    (defD : SortedDefinableOver 𝓜 S₀.carrier (fieldPairAssignment O ⁻¹' D))
    (x : K) (b : Fin 1 → K) (t : Empty → RV0 O) :
    (x,b,t) ∈ ((fieldPairSet hO power S₀ D defD).permuteVF (Equiv.swap 0 1)).verticalCarrier ↔ (b 0,x) ∈ D := by
  let p : Fin 2 → K := Fin.cons x b
  let e := Equiv.swap (0 : Fin 2) 1
  change (p (e.symm 0),p (e.symm 1)) ∈ D ↔ _
  change (p (e 0),p (e 1)) ∈ D ↔ _
  rw [show e 0 = 1 from Equiv.swap_apply_left _ _,show e 1 = 0 from Equiv.swap_apply_right _ _]
  rfl

end Canonical

end GeneralizedEuler.Section5
