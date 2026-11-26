module

public import Section5.RVLabelFunctions
public import Section5.TaggedTwoCellGeometry
public import Section5.PositioningLeafSchemes

/-! A valid leaf scheme gives one definable RV label for each
point over its parameter part. The label depends on the first
field coordinate and the old RV tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)} {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty

@[expose] def RetainedFieldFamily.positioningDomainScheme
    (A : RetainedFieldFamily 𝓜 S 2 k) :
    Set (SortedAssignment Z (SumVariables (RVVariables A.tags) U)) :=
  {a | a .vf (.inr 0) ∈ A.firstDomain (a .rv ∘ Sum.inl)}

theorem RetainedFieldFamily.positioningDomainScheme_definable
    (A : RetainedFieldFamily 𝓜 S 2 k) :
    SortedDefinableOver 𝓜 S.carrier A.positioningDomainScheme :=
  A.factorProjection_definable 0

namespace TaggedPositioningData

variable {A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 2 k}
  (C : TaggedPositioningData A)

local notation "R" => RVVariables A.tags
local notation "V" => SumVariables R U

@[expose] def graphScheme : Set (SortedAssignment Z (SumVariables V U)) :=
  {a | C.position (a .vf (.inl (.inr 0))) (a .rv ∘ Sum.inl ∘ Sum.inl) = a .vf (.inr 0)}

theorem graphScheme_definable : SortedDefinableOver 𝓜 S.carrier C.graphScheme := by
  let ren : (s : TCsort) → SumVariables (MixedVariables 1 A.tags) U s → SumVariables V U s
    | .vf => Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl) Empty.elim
  have g := C.positionDef
  unfold DefinableRelation at g
  exact g.pullback_relabel ren

theorem leaf_label_function
    (W : PositioningLeafScheme 𝓜 S R) (part : Set (A.tags → RV0 O)) (defPart : isRVSet 𝓜 S part)
    (valid : ∀ q ∈ part, W.valid O hO power S A.positioningDomainScheme C.graphScheme (rvAssignment q)) :
    ∃ label : SortedAssignment Z (MixedVariables 2 A.tags) → Fin W.arity → RV0 O,
      DefinableRelation 𝓜 S.carrier (fun a (r : SortedAssignment Z (RVVariables (Fin W.arity))) =>
        label a = r .rv) ∧
      ∀ (a : SortedAssignment Z (MixedVariables 2 A.tags)) (r : SortedAssignment Z (RVVariables (Fin W.arity))),
        a .rv ∈ part → a .vf 0 ∈ A.firstDomain (a .rv) →
        (label a = r .rv ↔ appendAssignments (appendAssignments (rvAssignment (a .rv)) r)
          (fieldTupleAssignment (fun _ => a .vf 0)) ∈ W.leaves) := by
  let F := MixedVariables 2 A.tags
  let Q := RVVariables (Fin W.arity)
  let W' := SumVariables F Q
  let leaf (a : SortedAssignment Z F) (r : SortedAssignment Z Q) :
      SortedAssignment Z (SumVariables (SumVariables R Q) U) :=
    appendAssignments (appendAssignments (rvAssignment (a .rv)) r) (fieldTupleAssignment (fun _ => a .vf 0))
  let graph (a : SortedAssignment Z F) (r : SortedAssignment Z Q) :=
    a .rv ∈ part ∧ leaf a r ∈ W.leaves
  let old (s : TCsort) : R s → W' s := match s with
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let ren (s : TCsort) : SumVariables (SumVariables R Q) U s → W' s :=
    match s with
    | .vf => Sum.elim (Sum.elim PEmpty.elim PEmpty.elim) (fun _ => .inl 0)
    | .rv => Sum.elim (Sum.elim Sum.inl Sum.inr) Empty.elim
  have d : DefinableRelation 𝓜 S.carrier graph := by
    unfold DefinableRelation
    convert (defPart.pullback_relabel old).inter (W.definable.pullback_relabel ren) using 1
    ext z
    let a : SortedAssignment Z F := fun s => z s ∘ Sum.inl
    let r : SortedAssignment Z Q := fun s => z s ∘ Sum.inr
    have e : leaf a r = (fun s => z s ∘ ren s) := by
      funext s i
      cases s
      · rcases i with (i | i) | i
        · exact i.elim
        · exact i.elim
        · rfl
      · rcases i with (i | i) | i
        · rfl
        · rfl
        · exact i.elim
    change (a .rv ∈ part ∧ leaf a r ∈ W.leaves) ↔
      a .rv ∈ part ∧ (fun s => z s ∘ ren s) ∈ W.leaves
    rw [e]
  have unique (a r s) (hr : graph a r) (hs : graph a s) : r = s :=
    (valid (a .rv) hr.1).2.1 (fieldTupleAssignment (fun _ => a .vf 0)) r s hr.2 hs.2
  obtain ⟨f,ev,df⟩ := definable_total_rv_label O hO power S graph d unique
  refine ⟨f,df,?_⟩
  intro a r ha hx
  constructor
  · intro h
    obtain ⟨s,hs⟩ := ((valid (a .rv) ha).1 (fieldTupleAssignment (fun _ => a .vf 0))).1 hx
    have e : s = r := by
      funext j i
      cases j with
      | vf => exact i.elim
      | rv => exact congrFun ((ev a s ⟨ha,hs⟩).symm.trans h) i
    exact e ▸ hs
  · intro h
    exact ev a r ⟨ha,h⟩

end TaggedPositioningData

end GeneralizedEuler.Section5
