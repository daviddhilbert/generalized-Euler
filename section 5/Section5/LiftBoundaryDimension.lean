module

public import Section5.DefinableBoundaryLifting
public import Section3.RVBoundaryTheorem
import all Section3.DefinableBoundary

/-! Relate the fixed-base lift boundary to the projection dimension of Section 3. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {n : ℕ}

@[expose] def fieldTupleAssignment (a : Fin n → X .vf) : fieldAssignment n X
  | .vf => a
  | .rv => Empty.elim

@[expose] def rvTupleAssignment (b : Fin n → X .rv) : labelAssignment n X
  | .vf => PEmpty.elim
  | .rv => b

theorem fieldAssignment_ext {a b : fieldAssignment n X}
    (h : ∀ j, a .vf j = b .vf j) : a = b := by
  funext s i
  cases s with
  | vf => exact h i
  | rv => exact i.elim

theorem fieldAssignment_blockDefinable {A : Set (fieldAssignment n X)}
    (hA : SortedDefinableOver M S.carrier A) :
    BlockDefinable M (fun s (a : S.carrier s) => a.val) .vf (fieldTupleAssignment ⁻¹' A) := by
  unfold BlockDefinable
  obtain ⟨φ,hφ⟩ := hA
  let rename : ∀ s, WithBase S.carrier (MixedVariables n Empty) s →
      AddSortedBlock (fun s => (S.carrier s : Type z)) .vf n s
    | .vf => Sum.map id (fun i => ⟨i,⟨rfl⟩⟩)
    | .rv => Sum.elim Sum.inl Empty.elim
  refine ⟨φ.relabel rename,?_⟩
  intro x
  rw [φ.realize_relabel]
  have he : (fun s => appendSortedBlock (fun s (a : S.carrier s) => a.val) x s ∘ rename s) =
      (fun s => Sum.elim Subtype.val (fieldTupleAssignment x s)) := by
    funext s i
    cases s with
    | vf => cases i <;> rfl
    | rv => rcases i with a | j; exacts [rfl,j.elim]
  rw [he]
  exact (hφ (fieldTupleAssignment x)).symm

/-- The numerical dimension on the RV assignments in the lifting proof. -/
@[expose] def labelProjectionDimension [TopologicalSpace (X .rv)] (B : Set (labelAssignment n X)) :
    WithBot ℕ :=
  projectionDimensionWithBot (rvTupleAssignment ⁻¹' B)

theorem labelProjectionDimension_mono [TopologicalSpace (X .rv)] :
    Monotone (labelProjectionDimension (n := n) (X := X)) := by
  intro A B hAB
  let A' := rvTupleAssignment ⁻¹' A
  let B' := rvTupleAssignment ⁻¹' B
  change projectionDimensionWithBot A' ≤ projectionDimensionWithBot B'
  have hs : A' ⊆ B' := Set.preimage_mono hAB
  rcases A'.eq_empty_or_nonempty with h | h
  · simp [h]
  · rw [projectionDimensionWithBot, projectionDimensionWithBot,
      dimensionWithBot_of_nonempty h, dimensionWithBot_of_nonempty (h.mono hs)]
    exact WithBot.coe_le_coe.mpr (projectionDimension_mono hs)

theorem labelProjectionDimension_le_arity [TopologicalSpace (X .rv)]
    (A : Set (labelAssignment n X)) : labelProjectionDimension A ≤ (n : WithBot ℕ) := by
  let T := rvTupleAssignment ⁻¹' A
  change projectionDimensionWithBot T ≤ _
  rcases T.eq_empty_or_nonempty with h | h
  · simp [h]
  · rw [projectionDimensionWithBot, dimensionWithBot_of_nonempty h]
    apply WithBot.coe_le_coe.mpr
    refine projectionDimension_le_iff.2 (fun m _ hm => ?_)
    exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ m.isLt) hm)

theorem fieldLead_boundary_eq_block (A : Set (fieldAssignment n X)) :
    rvTupleAssignment ⁻¹' rvBoundary (fieldLead M) A =
      rvBoundary (fun a : Fin n → X .vf => M.rvMap ∘ a) (fieldTupleAssignment ⁻¹' A) := by
  have hField (x : fieldAssignment n X) : fieldTupleAssignment (x .vf) = x := by
    funext s i
    cases s with
    | vf => rfl
    | rv => exact i.elim
  have hLabel (x : fieldAssignment n X) (y : Fin n → X .rv) :
      fieldLead M x = rvTupleAssignment y ↔ M.rvMap ∘ x .vf = y := by
    constructor
    · intro he
      exact congrFun he .rv
    · intro he
      funext s i
      cases s with
      | vf => exact i.elim
      | rv => exact congrFun he i
  ext b
  constructor
  · rintro ⟨⟨x,hx,hxb⟩,y,hyb,hy⟩
    exact ⟨⟨x .vf,hField x ▸ hx,(hLabel x b).1 hxb⟩,y .vf,
      (hLabel y b).1 hyb,hField y ▸ hy⟩
  · rintro ⟨⟨x,hx,hxb⟩,y,hyb,hy⟩
    exact ⟨⟨fieldTupleAssignment x,hx,(hLabel (fieldTupleAssignment x) b).2 hxb⟩,fieldTupleAssignment y,
      (hLabel (fieldTupleAssignment y) b).2 hyb,hy⟩

/-- Any instance of the Section 3 boundary estimate over the chosen
parameters gives the bound required by the fixed-base lifting proof. -/
theorem fieldLead_boundary_dimension_lt [TopologicalSpace (X .rv)]
    (boundary : ∀ A : Set (Fin n → X .vf),
      BlockDefinable M (fun s (a : S.carrier s) => a.val) .vf A →
      projectionDimensionWithBot (rvBoundary (fun a => M.rvMap ∘ a) A) < (n : WithBot ℕ))
    (A : Set (fieldAssignment n X)) (hA : SortedDefinableOver M S.carrier A) :
    labelProjectionDimension (rvBoundary (fieldLead M) A) < (n : WithBot ℕ) := by
  unfold labelProjectionDimension
  rw [fieldLead_boundary_eq_block]
  exact boundary _ (fieldAssignment_blockDefinable hA)

end GeneralizedEuler.Section5
