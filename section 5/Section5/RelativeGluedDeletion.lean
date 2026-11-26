module

public import Section5.RelativeRVGluing
public import Section5.RelativeLabelDeletion
public import Section5.GradedBlowupLabels

/-! A local deletion remains finite on the glued object because it
leaves the selected index coordinates available. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h m t k : ℕ}

local notation "P" => RVVariables (Fin h)
local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin (k+1))

private theorem rvHead_ne_tail {a b : ℕ} (i : Fin a) (j : Fin b) : rvHead i ≠ rvTail j := by
  intro e
  have h := finSumFinEquiv.injective e
  cases h

theorem gluedRV_finite_deleted_fiber (j : Fin (k+1)) (sel : Fin t → Fin h)
    {B : Set (Fin h → X .rv)}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (finiteBase : ∀ q : Fin t → X .rv, {p ∈ B | p ∘ sel = q}.Finite)
    (finiteLocal : ∀ p ∈ B, ∀ w : SortedAssignment X (RVVariables (Fin k)),
      {u | appendAssignments (appendAssignments (rvTupleAssignment p) u) w ∈ relativeDeleteLabelGraph j G}.Finite)
    {C : Type*} (tag : C → Fin (h+m) → X .rv) (injTag : Function.Injective tag)
    (label : C → Fin (t+(k+1)) → X .rv)
    (graph : ∀ x, RVObject.labelGraphTuple (tag x) (label x) ∈ gluedRVGraph sel B G) :
    ∀ y : {i : Fin (t+(k+1)) // i ≠ rvTail j} → X .rv,
      ((deleteCoordinate (rvTail j) ∘ label) ⁻¹' {y}).Finite := by
  intro y
  let head (i : Fin t) : X .rv := y ⟨rvHead i,rvHead_ne_tail i j⟩
  let tail (i : Fin k) : X .rv := y ⟨rvTail (j.succAbove i),
    fun e => Fin.succAbove_ne j i (Sum.inr.inj (finSumFinEquiv.injective e))⟩
  let target := concatRV head tail
  have fin := gluedRVGraph_finite_labels sel (G := relativeDeleteLabelGraph j G) finiteBase finiteLocal target
  apply (fin.preimage injTag.injOn).subset
  intro x hx
  have eq : deleteCoordinate (rvTail j) (label x) = y := hx
  obtain ⟨hp,hhead,htail⟩ := graph x
  change label x ∘ rvHead = (tag x ∘ rvHead) ∘ sel at hhead
  have oldHead : label x ∘ rvHead = head := by
    funext i
    exact congrFun eq ⟨rvHead i,rvHead_ne_tail i j⟩
  have oldTail : deleteRVAssignment j (rvTupleAssignment (label x ∘ rvTail)) = rvTupleAssignment tail := by
    funext s i
    cases s
    · exact i.elim
    · exact congrFun eq ⟨rvTail (j.succAbove i),
        fun e => Fin.succAbove_ne j i (Sum.inr.inj (finSumFinEquiv.injective e))⟩
  change (tag x ∘ rvHead ∈ B ∧ target ∘ rvHead = (tag x ∘ rvHead) ∘ sel ∧
    appendAssignments (appendAssignments (rvTupleAssignment (tag x ∘ rvHead))
      (rvTupleAssignment (tag x ∘ rvTail))) (rvTupleAssignment (target ∘ rvTail)) ∈ relativeDeleteLabelGraph j G)
  dsimp only [target]
  rw [concatRV_head,concatRV_tail]
  refine ⟨hp,oldHead.symm.trans hhead,?_⟩
  exact (relativeDeleteLabelGraph_iff j G _ _ _).2 ⟨_,htail,oldTail⟩

theorem gluedRV_finite_deletion (j : Fin (k+1)) (sel : Fin t → Fin h)
    {B : Set (Fin h → X .rv)}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (finiteBase : ∀ q : Fin t → X .rv, {p ∈ B | p ∘ sel = q}.Finite)
    (finiteLocal : ∀ p ∈ B, ∀ w : SortedAssignment X (RVVariables (Fin k)),
      {u | appendAssignments (appendAssignments (rvTupleAssignment p) u) w ∈ relativeDeleteLabelGraph j G}.Finite)
    (W : RVObject M S (t+(k+1))) (arity : W.arity = h+m)
    (graph : ∀ x : W.carrier,
      RVObject.labelGraphTuple (x.val ∘ Fin.cast arity.symm) (W.label x) ∈ gluedRVGraph sel B G) :
    ∀ y : Fin (t+k) → X .rv, {v ∈ Set.range W.label | v ∘ (rvTail j).succAbove = y}.Finite := by
  intro y
  let j₀ : Fin ((t+k)+1) := rvTail (a := t) (b := k+1) j
  let index (i : {i : Fin (t+(k+1)) // i ≠ rvTail j}) : Fin (t+k) :=
    (Fin.exists_succAbove_eq (x := i.val) (y := j₀) i.property).choose
  have tagInj : Function.Injective (fun x : W.carrier => x.val ∘ Fin.cast arity.symm) := by
    intro x x' e
    apply Subtype.ext
    funext i
    have eq := congrFun e (Fin.cast arity i)
    have castEq : Fin.cast arity.symm (Fin.cast arity i) = i := Fin.ext rfl
    simpa only [Function.comp_apply,castEq] using eq
  have f := gluedRV_finite_deleted_fiber j sel finiteBase finiteLocal
    (fun x : W.carrier => x.val ∘ Fin.cast arity.symm) tagInj W.label graph (y ∘ index)
  apply (f.image W.label).subset
  rintro v ⟨⟨x,rfl⟩,eq⟩
  refine ⟨x,?_,rfl⟩
  change deleteCoordinate (rvTail j) (W.label x) = y ∘ index
  funext i
  have indexEq : j₀.succAbove (index i) = i.val := (Fin.exists_succAbove_eq i.property).choose_spec
  exact (congrArg (W.label x) indexEq.symm).trans (congrFun eq (index i))

end GeneralizedEuler.Section5
