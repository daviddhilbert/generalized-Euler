module

public import Section5.TailFieldSlices

/-! A relatively unary map in the first coordinate restricts to a
definable bijection over each fixed complementary field tuple. It
also preserves the selected RV coordinates when the total map does. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ}

local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables n Empty

namespace RetainedFieldFamily

variable (A B : RetainedFieldFamily M S (n+1) k)

private def addFieldTail {I : Type} (p : SortedAssignment Z P)
    (x : SortedAssignment Z (MixedVariables 1 I)) :
    SortedAssignment Z (MixedVariables (n+1) I)
  | .vf => Fin.cons (x .vf 0) (p .vf)
  | .rv => x .rv

private def dropFieldTail {I : Type} (x : SortedAssignment Z (MixedVariables (n+1) I)) :
    SortedAssignment Z (MixedVariables 1 I)
  | .vf => fun _ => x .vf 0
  | .rv => x .rv

private theorem drop_add_fieldTail {I : Type} (p : SortedAssignment Z P)
    (x : SortedAssignment Z (MixedVariables 1 I)) : dropFieldTail (addFieldTail p x) = x := by
  funext s i
  cases s
  · change x .vf 0 = x .vf i
    rw [Subsingleton.elim i (0 : Fin 1)]
  · rfl

private theorem add_drop_fieldTail {I : Type} (p : SortedAssignment Z P)
    (x : SortedAssignment Z (MixedVariables (n+1) I)) (h : x .vf ∘ Fin.succ = p .vf) :
    addFieldTail p (dropFieldTail x) = x := by
  funext s i
  cases s
  · refine Fin.cases rfl (fun j => ?_) i
    exact (congrFun h j).symm
  · rfl

set_option maxHeartbeats 700000 in
theorem fieldTailSlices_iso
    (f : MixedGraphIso M S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier})
    (tail : ∀ x, (f.equiv x).val .vf ∘ Fin.succ = x.val .vf ∘ Fin.succ)
    (select : ∀ x, (f.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select)
    (p : SortedAssignment Z P) :
    let T := M.termGenerated (namedTuple S p)
    let U := {a : SortedAssignment Z (MixedVariables 1 A.tags) |
      mixedTuple a ∈ (A.fieldTailSlice p).carrier}
    let V := {b : SortedAssignment Z (MixedVariables 1 B.tags) |
      mixedTuple b ∈ (B.fieldTailSlice p).carrier}
    ∃ g : MixedGraphIso M T U V,
      ∀ x, (g.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select := by
  intro T U V
  let extend (x : U) : {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier} :=
    ⟨addFieldTail p x.val,x.property⟩
  have cmp (x : U) : (f.equiv (extend x)).val .vf ∘ Fin.succ = p .vf := tail (extend x)
  let forw (x : U) : V :=
    ⟨dropFieldTail (f.equiv (extend x)).val,by
      have h := (f.equiv (extend x)).property
      rw [← add_drop_fieldTail p _ (cmp x)] at h
      exact h⟩
  have eval (x : U) : addFieldTail p (forw x).val = (f.equiv (extend x)).val :=
    add_drop_fieldTail p _ (cmp x)
  have bij : Function.Bijective forw := by
    constructor
    · intro x y eq
      apply Subtype.ext
      have h : f.equiv (extend x) = f.equiv (extend y) := Subtype.ext (by rw [← eval,← eval,eq])
      have same := congrArg (fun z => dropFieldTail z.val) (f.equiv.injective h)
      change dropFieldTail (addFieldTail p x.val) = dropFieldTail (addFieldTail p y.val) at same
      simpa only [drop_add_fieldTail] using same
    · intro y
      let y' : {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier} :=
        ⟨addFieldTail p y.val,y.property⟩
      let x' := f.equiv.symm y'
      have eq : f.equiv x' = y' := f.equiv.apply_symm_apply _
      have isTail : x'.val .vf ∘ Fin.succ = p .vf := by
        have e := tail x'
        rw [eq] at e
        exact e.symm
      let x : U := ⟨dropFieldTail x'.val,by
        have h := x'.property
        rw [← add_drop_fieldTail p _ isTail] at h
        exact h⟩
      have sx : extend x = x' := Subtype.ext (add_drop_fieldTail p _ isTail)
      refine ⟨x,Subtype.ext ?_⟩
      change dropFieldTail (f.equiv (extend x)).val = y.val
      rw [sx,eq]
      exact drop_add_fieldTail p y.val
  let g : U ≃ V := Equiv.ofBijective forw bij
  let W := SumVariables (MixedVariables 1 A.tags) (MixedVariables 1 B.tags)
  let take : (s : TCsort) → SumVariables (MixedVariables (n+1) A.tags) (MixedVariables (n+1) B.tags) s → SumVariables P W s
    | .vf => Sum.elim (Fin.cases (.inr (.inl 0)) Sum.inl) (Fin.cases (.inr (.inr 0)) Sum.inl)
    | .rv => Sum.inr
  let raw := f.definable.pullback_relabel take
  have named := definable_scheme_at_fiber p _ raw
  have graph : DefinableRelation M T.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 A.tags)) (b : SortedAssignment Z (MixedVariables 1 B.tags)) =>
        ∃ h : a ∈ U, (g ⟨a,h⟩).val = b) := by
    unfold DefinableRelation
    convert named using 1
    ext w
    let a : SortedAssignment Z (MixedVariables 1 A.tags) := fun s => w s ∘ Sum.inl
    let b : SortedAssignment Z (MixedVariables 1 B.tags) := fun s => w s ∘ Sum.inr
    have agree : (fun s => appendAssignments p w s ∘ take s) = appendAssignments (addFieldTail p a) (addFieldTail p b) := by
      funext s i
      cases s
      · rcases i with i | i
        · refine Fin.cases rfl (fun j => rfl) i
        · refine Fin.cases rfl (fun j => rfl) i
      · rcases i with i | i <;> rfl
    let Q := SumVariables (MixedVariables (n+1) A.tags) (MixedVariables (n+1) B.tags)
    let original : Set (SortedAssignment Z Q) :=
      {z | ∃ h : mixedTuple (fun s => z s ∘ Sum.inl) ∈ A.carrier,
        (f.equiv ⟨fun s => z s ∘ Sum.inl,h⟩).val = (fun s => z s ∘ Sum.inr)}
    change (∃ h : a ∈ U, (g ⟨a,h⟩).val = b) ↔ (fun s => appendAssignments p w s ∘ take s) ∈ original
    refine Iff.trans ?_ (congrArg (· ∈ original) agree).to_iff.symm
    change (∃ h : a ∈ U, (g ⟨a,h⟩).val = b) ↔
      ∃ h : mixedTuple (addFieldTail p a) ∈ A.carrier, (f.equiv ⟨addFieldTail p a,h⟩).val = addFieldTail p b
    constructor
    · rintro ⟨h,e⟩
      exact ⟨h,(eval ⟨a,h⟩).symm.trans (congrArg (addFieldTail p) e)⟩
    · rintro ⟨h,e⟩
      exact ⟨h,(congrArg dropFieldTail e).trans (drop_add_fieldTail p b)⟩
  exact ⟨⟨g,graph⟩,fun x => select (extend x)⟩

end RetainedFieldFamily

end GeneralizedEuler.Section5
