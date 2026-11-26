module

public import Section2.DiscCodes

/-! Restoring omitted coordinates in a lift of a bijection (Lemma 5.12). -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

private theorem scaled_rv {a b x : K} (ha : a ≠ 0) (hx : rv O x = rv O a) :
    rv O (b * x / a) = rv O b := by
  rw [map_div₀, map_mul, hx]
  exact (div_eq_iff (G₀ := RV0 O) ((rv_eq_zero_iff O).not.mpr ha)).2 rfl

/-- Coordinatewise multiplication by the ratio of chosen field
representatives sends one full leading-term fiber to the other. -/
def scaleFibers {I : Type*} (a b : I → K) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    {x : I → K // ∀ i, rv O (x i) = rv O (a i)} ≃
      {y : I → K // ∀ i, rv O (y i) = rv O (b i)} where
  toFun x := ⟨fun i => b i * x.val i / a i, fun i => scaled_rv O (ha i) (x.property i)⟩
  invFun y := ⟨fun i => a i * y.val i / b i, fun i => scaled_rv O (hb i) (y.property i)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change a i * (b i * x.val i / a i) / b i = x.val i
    field_simp [ha i, hb i]
  right_inv y := by
    apply Subtype.ext
    funext i
    change b i * (a i * y.val i / b i) / a i = y.val i
    field_simp [ha i, hb i]

theorem scaleFibers_apply {I : Type*} (a b : I → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (x : {x : I → K // ∀ i, rv O (x i) = rv O (a i)}) (i : I) :
    (scaleFibers O a b ha hb x).val i = b i * x.val i / a i := by
  unfold scaleFibers
  rfl

/-- The two families of representatives depend on the *retained field
tuples*. Only the projected lift runs on the first component. -/
def restoreCoordinates {X Y I : Type*} (e : X ≃ Y) (a : X → I → K) (b : Y → I → K)
    (ha : ∀ x i, a x i ≠ 0) (hb : ∀ y i, b y i ≠ 0) :
    (Σ x : X, {z : I → K // ∀ i, rv O (z i) = rv O (a x i)}) ≃
      (Σ y : Y, {w : I → K // ∀ i, rv O (w i) = rv O (b y i)}) :=
  Equiv.sigmaCongr e (fun x => scaleFibers O (a x) (b (e x)) (ha x) (hb (e x)))

end GeneralizedEuler.Section5
