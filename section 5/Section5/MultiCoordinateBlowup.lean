module

public import Section5.GradedBlowupLabels

/-! Apply the unary focus translation in one coordinate and keep
all other field coordinates fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {F A : Type*} [DecidableEq F]

private def insertCoordinate {Y : Type*} (j : F) (v : {i : F // i ≠ j} → Y) (y : Y) : F → Y :=
  fun i => if h : i ≠ j then v ⟨i,h⟩ else y

private theorem insertCoordinate_at {Y : Type*} (j : F) (v : {i : F // i ≠ j} → Y) (y : Y) :
    insertCoordinate j v y j = y := by
  simp only [insertCoordinate, ne_eq, not_true_eq_false, dite_false]

private theorem insertCoordinate_other {Y : Type*} (j : F) (v : {i : F // i ≠ j} → Y) (y : Y)
    (i : {i : F // i ≠ j}) : insertCoordinate j v y i.val = v i := by
  change (if h : i.val ≠ j then v ⟨i.val,h⟩ else y) = v i
  exact dite_eq_left i.property

private abbrev TupleFiber (t : F → RV0 O) := {x : F → K // ∀ i, rv O (x i) = t i}

private abbrev RestFiber (j : F) (t : F → RV0 O) :=
  {v : {i : F // i ≠ j} → K // ∀ i, rv O (v i) = t i.val}

private def tupleFiberSplit (j : F) (t : F → RV0 O) :
    TupleFiber O t ≃ RestFiber O j t × {y : K // rv O y = t j} where
  toFun x := (⟨fun i => x.val i.val,fun i => x.property i.val⟩,⟨x.val j,x.property j⟩)
  invFun q := ⟨insertCoordinate j q.1.val q.2.val,by
    intro i
    by_cases hi : i = j
    · subst i
      rw [insertCoordinate_at]
      exact q.2.property
    · rw [show insertCoordinate j q.1.val q.2.val i = q.1.val ⟨i,hi⟩ from
        insertCoordinate_other _ _ _ ⟨i,hi⟩]
      exact q.1.property ⟨i,hi⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = j
    · subst i
      exact insertCoordinate_at _ _ _
    · exact insertCoordinate_other _ _ _ ⟨i,hi⟩
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (funext fun i => insertCoordinate_other _ _ _ i)
    · exact Subtype.ext (insertCoordinate_at _ _ _)

/-- The multipliers include zero. The zero is kept as a tag in this
comparison and can subsequently be split off as its own degree. -/
abbrev BlowupMultiplier := {s : RV0 O // unsignedValue O s < 1}

private def blowupFiberPacking (j : F) (t : F → RV0 O) :
    RestFiber O j t × BlownUpFiber O (t j) ≃
      Σ s : BlowupMultiplier O, TupleFiber O (Function.update t j (s.val * t j)) where
  toFun q := by
    let s : BlowupMultiplier O := ⟨q.2.val.2,q.2.property.1⟩
    refine ⟨s, ⟨insertCoordinate j q.1.val q.2.val.1,?_⟩⟩
    intro i
    by_cases hi : i = j
    · subst i
      rw [insertCoordinate_at,Function.update_self]
      exact q.2.property.2
    · rw [show insertCoordinate j q.1.val q.2.val.1 i = q.1.val ⟨i,hi⟩ from
        insertCoordinate_other _ _ _ ⟨i,hi⟩,Function.update_of_ne hi]
      exact q.1.property ⟨i,hi⟩
  invFun q := ⟨⟨fun i => q.2.val i.val,fun i => by
    have h := q.2.property i.val
    rwa [Function.update_of_ne i.property] at h⟩,
    ⟨(q.2.val j,q.1.val),q.1.property,by
      have h := q.2.property j
      rwa [Function.update_self] at h⟩⟩
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (funext fun i => insertCoordinate_other _ _ _ i)
    · exact Subtype.ext (Prod.ext (insertCoordinate_at _ _ _) rfl)
  right_inv p := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      funext i
      by_cases hi : i = j
      · subst i
        exact insertCoordinate_at _ _ _
      · exact insertCoordinate_other _ _ _ ⟨i,hi⟩

/-- The elementary blowup of a lifted label object is equivalent to
the original lift once foci have been chosen in the selected fibers. -/
def liftBlowupCoordinates (j : F) (f : A → F → RV0 O)
    (focus : A → K) (nonzero : ∀ a, focus a ≠ 0)
    (label : ∀ a, rv O (focus a) = f a j) :
    (Σ a : A, {x : F → K // ∀ i, rv O (x i) = f a i}) ≃
      (Σ a : A, Σ s : BlowupMultiplier O,
        {y : F → K // ∀ i, rv O (y i) = blowupLabel O j f (a,s.val) i}) := by
  apply Equiv.sigmaCongrRight
  intro a
  let chooseUnary : {x : K // rv O x = f a j} ≃ BlownUpFiber O (f a j) := by
    rw [← label a]
    exact liftUnaryBlowup O (focus a) (nonzero a)
  exact (tupleFiberSplit O j (f a)).trans
    ((Equiv.prodCongr (Equiv.refl _) chooseUnary).trans (blowupFiberPacking O j (f a)))

/-- The focus may vary with all unchanged field coordinates. The
equivalence acts on the chosen coordinate over each fixed unchanged tuple. -/
def liftBlowupCoordinatesWithRelativeFocus (j : F) (f : A → F → RV0 O)
    (focus : ∀ a : A, {v : {i : F // i ≠ j} → K // ∀ i, rv O (v i) = f a i.val} → K)
    (nonzero : ∀ a v, focus a v ≠ 0)
    (label : ∀ a v, rv O (focus a v) = f a j) :
    (Σ a : A, {x : F → K // ∀ i, rv O (x i) = f a i}) ≃
      (Σ a : A, Σ s : BlowupMultiplier O,
        {y : F → K // ∀ i, rv O (y i) = blowupLabel O j f (a,s.val) i}) := by
  apply Equiv.sigmaCongrRight
  intro a
  let unary (v : RestFiber O j (f a)) :
      {x : K // rv O x = f a j} ≃ BlownUpFiber O (f a j) := by
    rw [← label a v]
    exact liftUnaryBlowup O (focus a v) (nonzero a v)
  let e : (RestFiber O j (f a) × {x : K // rv O x = f a j}) ≃
      (RestFiber O j (f a) × BlownUpFiber O (f a j)) :=
    { toFun w := (w.1,unary w.1 w.2)
      invFun w := (w.1,(unary w.1).symm w.2)
      left_inv w := Prod.ext rfl ((unary w.1).symm_apply_apply w.2)
      right_inv w := Prod.ext rfl ((unary w.1).apply_symm_apply w.2) }
  exact (tupleFiberSplit O j (f a)).trans (e.trans (blowupFiberPacking O j (f a)))

end GeneralizedEuler.Section5
