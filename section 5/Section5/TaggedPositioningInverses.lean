module

public import Section5.TaggedTwoCellGeometry
public import Section5.PartialFieldFunctions

/-! On a nonproduct tag the positioning function is injective.
Its inverse is definable on the range and is extended by a named
field value away from that range. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {k : ℕ}

local notation "Z" => CanonicalSort O

theorem TaggedTwoCellGeometry.definable_inverse_on_nonproduct
    {A : RetainedFieldFamily M S 2 k} (C : TaggedTwoCellGeometry A)
    (default : S.carrier .vf) :
    ∃ g : K → (A.tags → RV0 O) → K,
      DefinableRelation M S.carrier (fun
        (a : SortedAssignment Z (MixedVariables 1 A.tags)) (b : fieldAssignment 1 Z) =>
        g (a .vf 0) (a .rv) = b .vf 0) ∧
      ∀ q, q ∉ A.productFibers → ∀ x ∈ A.firstDomain q, g (C.position x q) q = x := by
  let U := MixedVariables 1 A.tags
  let V := MixedVariables 1 Empty
  let W := SumVariables U V
  let Q := RVVariables A.tags
  let R (y : SortedAssignment Z U) (x : fieldAssignment 1 Z) :=
    y .rv ∉ A.productFibers ∧ x .vf 0 ∈ A.firstDomain (y .rv) ∧
      C.position (x .vf 0) (y .rv) = y .vf 0
  let old : (s : TCsort) → Q s → W s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let dom : (s : TCsort) → U s → W s
    | .vf => Sum.inr
    | .rv => Sum.inl
  let swapFields : (s : TCsort) → W s → W s
    | .vf => Sum.swap
    | .rv => id
  have prod := A.productFibers_definable.compl.pullback_relabel old
  have source := (A.factorProjection_mixed_definable 0).pullback_relabel dom
  have position := C.positionDef
  unfold DefinableRelation at position
  have dR : DefinableRelation M S.carrier R :=
    prod.inter (source.inter (position.pullback_relabel swapFields))
  have unique (a : SortedAssignment Z U) (x y : fieldAssignment 1 Z) (hx : R a x) (hy : R a y) :
      x = y := by
    have h := C.position_injective_on_nonproduct (a .rv) hx.1 hx.2.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)
    exact fieldAssignment_ext (fun i => by rw [Fin.eq_zero i]; exact h)
  obtain ⟨value,ev,defValue⟩ := definable_partial_field_function R dR unique default
  let inputs (x : K) (q : A.tags → RV0 O) : SortedAssignment Z U := mixedAssignment (fun _ => x) q
  have eval (a : SortedAssignment Z U) : inputs (a .vf 0) (a .rv) = a := by
    funext s i
    cases s
    · rw [Fin.eq_zero i]
      rfl
    · rfl
  refine ⟨fun x q => value (inputs x q),defValue.congr ?_,?_⟩
  · intro a b
    change _ ↔ value (inputs (a .vf 0) (a .rv)) = b .vf 0
    rw [eval]
  · intro q bad x hx
    let a := inputs (C.position x q) q
    let b : fieldAssignment 1 Z := fieldTupleAssignment (fun _ => x)
    exact ev a b ⟨bad,hx,rfl⟩

end GeneralizedEuler.Section5
