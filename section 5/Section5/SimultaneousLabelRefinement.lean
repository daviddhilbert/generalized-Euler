module

public import Section3.Contraction
public import Mathlib.Logic.Equiv.Set

/-! The label induction for simultaneous unary preparations. At an
individual step, paired focused fibers have matching centered labels,
while all unselected source fibers keep one target label. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section3

variable {X Y : Type*} (f : X ≃ Y)

/-- The hypotheses of one paired step compare the new tests only within
the old source fibers. The inverse comparison uses the final target
labels throughout the induction. -/
theorem simultaneous_label_step
    {P Pnext : X → X → Prop} {Q Qnext Qfinal : Y → Y → Prop}
    {C : X → X → Prop} {D : Y → Y → Prop}
    (keepP : ∀ x x', Pnext x x' ↔ P x x' ∧ C x x')
    (keepQ : ∀ y y', Qnext y y' ↔ Q y y' ∧ D y y')
    (forward : ∀ x x', P x x' → Q (f x) (f x'))
    (backward : ∀ y y', Qfinal y y' → P (f.symm y) (f.symm y'))
    (paired : ∀ x x', P x x' → (C x x' ↔ D (f x) (f x')))
    (refines : ∀ y y', Qfinal y y' → Qnext y y') :
    (∀ x x', Pnext x x' → Qnext (f x) (f x')) ∧
    (∀ y y', Qfinal y y' → Pnext (f.symm y) (f.symm y')) := by
  constructor
  · intro x x' he
    obtain ⟨old,new⟩ := (keepP x x').1 he
    exact (keepQ _ _).2 ⟨forward _ _ old,(paired _ _ old).1 new⟩
  · intro y y' he
    have old := backward y y' he
    have hD := ((keepQ y y').1 (refines y y' he)).2
    apply (keepP _ _).2
    refine ⟨old,(paired _ _ old).2 ?_⟩
    simpa only [Equiv.apply_symm_apply] using hD

/-- Iterate paired steps while keeping the inverse contraction to the
final target labels. The conclusion gives contraction in both directions. -/
theorem simultaneous_label_induction
    (P : ℕ → X → X → Prop) (Q : ℕ → Y → Y → Prop) (n : ℕ)
    (C : ℕ → X → X → Prop) (D : ℕ → Y → Y → Prop)
    (keepP : ∀ i < n, ∀ x x', P (i+1) x x' ↔ P i x x' ∧ C i x x')
    (keepQ : ∀ i < n, ∀ y y', Q (i+1) y y' ↔ Q i y y' ∧ D i y y')
    (initialForward : ∀ x x', P 0 x x' → Q 0 (f x) (f x'))
    (initialBackward : ∀ y y', Q n y y' → P 0 (f.symm y) (f.symm y'))
    (paired : ∀ i < n, ∀ x x', P i x x' → (C i x x' ↔ D i (f x) (f x')))
    (refines : ∀ i < n, ∀ y y', Q n y y' → Q (i+1) y y') :
    (∀ x x', P n x x' → Q n (f x) (f x')) ∧
      (∀ y y', Q n y y' → P n (f.symm y) (f.symm y')) := by
  suffices proof : ∀ i ≤ n, (∀ x x', P i x x' → Q i (f x) (f x')) ∧
      (∀ y y', Q n y y' → P i (f.symm y) (f.symm y')) from proof n le_rfl
  intro i hi
  induction i with
  | zero => exact ⟨initialForward,initialBackward⟩
  | succ i ih =>
    have lt : i < n := hi
    obtain ⟨forw,back⟩ := ih lt.le
    exact simultaneous_label_step f (keepP i lt) (keepQ i lt) forw back (paired i lt) (refines i lt)

/-- An equivalence whose two directions contract to labels gives an
equivalence of the labels that actually occur. -/
theorem equiv_of_mutual_contraction {U V : Type*} (p : X → U) (q : Y → V)
    (forward : Contractible p q f) (backward : Contractible q p f.symm) :
    ∃ e : Set.range p ≃ Set.range q,
      ∀ x, (e ⟨p x,Set.mem_range_self x⟩).val = q (f x) := by
  let chooseP (u : Set.range p) : X := u.property.choose
  let g (u : Set.range p) : Set.range q := ⟨q (f (chooseP u)),Set.mem_range_self _⟩
  have value (x : X) : (g ⟨p x,Set.mem_range_self x⟩).val = q (f x) :=
    forward _ _ (Set.mem_range_self x (f := p)).choose_spec
  have bij : Function.Bijective g := by
    constructor
    · rintro ⟨u,x,rfl⟩ ⟨v,y,rfl⟩ he
      have eq : q (f x) = q (f y) :=
        (value x).symm.trans ((congrArg Subtype.val he).trans (value y))
      apply Subtype.ext
      simpa only [Equiv.symm_apply_apply] using backward _ _ eq
    · rintro ⟨v,y,rfl⟩
      refine ⟨⟨p (f.symm y),Set.mem_range_self _⟩,Subtype.ext ?_⟩
      rw [value,f.apply_symm_apply]
  exact ⟨Equiv.ofBijective g bij,value⟩

end GeneralizedEuler.Section5
