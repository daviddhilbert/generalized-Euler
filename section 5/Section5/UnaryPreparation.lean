module

public import Section3.ImmediateDiscs

/-! Unary special bijections with all intermediate leading terms retained. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- A unary preparation on the full affine line. The actual image includes
the labels that occur, and contains the whole leading-term fiber at each label. -/
structure UnaryPreparation (H : Type*) where
  label : K → H
  offset : H → K
  lead : H → RV0 O
  leading x : rv O (x - offset (label x)) = lead (label x)
  constant_label {x y} : rv O (y - offset (label x)) = lead (label x) → label y = label x

namespace UnaryPreparation

variable {O} {H : Type*} (P : UnaryPreparation O H)

/-- The preimage of a prepared fiber is precisely the translate by its
recorded offset. This includes the singleton above the zero leading term. -/
theorem label_eq_iff {x y : K} :
    P.label y = P.label x ↔ rv O (y - P.offset (P.label x)) = P.lead (P.label x) :=
  ⟨fun h => h ▸ P.leading y, P.constant_label⟩

/-- In the original coordinate, a nonpoint prepared fiber is an open
disc centered at any of its own points. -/
theorem label_fiber_eq_openDisc (x : K) (hx : P.lead (P.label x) ≠ 0) :
    P.label ⁻¹' {P.label x} = openDisc O x (O.valuation (x - P.offset (P.label x))) := by
  have hne : x - P.offset (P.label x) ≠ 0 :=
    fun h => hx ((P.leading x).symm.trans ((rv_eq_zero_iff O).2 h))
  ext y
  change P.label y = P.label x ↔ O.valuation (y - x) < O.valuation (x - P.offset (P.label x))
  rw [P.label_eq_iff, ← P.leading x, rv_eq_rv_iff_valuation O hne,
    sub_sub_sub_cancel_right]

theorem label_fiber_eq_singleton (x : K) (hx : P.lead (P.label x) = 0) :
    P.label ⁻¹' {P.label x} = {x} := by
  have h := sub_eq_zero.mp ((rv_eq_zero_iff O).1 ((P.leading x).trans hx))
  ext y
  change P.label y = P.label x ↔ y = x
  rw [P.label_eq_iff, hx, rv_eq_zero_iff, sub_eq_zero, ← h]

/-- The regularized coordinate, paired with all of its labels. -/
@[expose] def map (x : K) : K × H := (x - P.offset (P.label x), P.label x)

/-- Before restriction the image is a union of whole RV fibers. -/
theorem image_univ :
    Set.range P.map =
      {p | p.2 ∈ Set.range P.label ∧ rv O p.1 = P.lead p.2} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Set.mem_range_self x, P.leading x⟩
  · rcases p with ⟨y, h⟩
    rintro ⟨⟨x, rfl⟩, hy⟩
    have hy' : P.label (y + P.offset (P.label x)) = P.label x :=
      P.constant_label (by simpa using hy)
    exact ⟨y + P.offset (P.label x), by simp [map, hy']⟩

theorem map_injective : Function.Injective P.map := by
  intro x y h
  have ht := congrArg Prod.snd h
  have hc := congrArg Prod.fst h
  change P.label x = P.label y at ht
  change x - P.offset (P.label x) = y - P.offset (P.label y) at hc
  rw [ht] at hc
  exact sub_left_inj.mp hc

/-- Initial regularization uses no translations. -/
@[expose] def regularize : UnaryPreparation O (RV0 O) where
  label := rv O
  offset := fun _ => 0
  lead := id
  leading x := by simp
  constant_label h := by simpa using h

/-- On the nonzero fiber containing the new focus, the offset becomes
the new center. Elsewhere the previous translation is retained. -/
@[expose] def nextOffset (c : K) (h : H) : K := by
  classical
  exact if P.lead h ≠ 0 ∧ rv O (c - P.offset h) = P.lead h then c else P.offset h

/-- Translation by a focus in a full nonzero fiber produces the open
ball about zero with the same radius. -/
private theorem fiber_after_translation {x d c : K}
    (hc : c - d ≠ 0) :
    rv O (x - d) = rv O (c - d) ↔ O.valuation (x - c) < O.valuation (c - d) := by
  rw [rv_eq_rv_iff_valuation O hc, sub_sub_sub_cancel_right]

/-- A centripetal transformation followed by regularization, with the
old labels kept in the first component of the new label. -/
@[expose] def step (c : K) : UnaryPreparation O (H × RV0 O) where
  label x := (P.label x, rv O (x - P.nextOffset c (P.label x)))
  offset h := P.nextOffset c h.1
  lead := Prod.snd
  leading _ := rfl
  constant_label {x y} hy := by
    classical
    change rv O (y - P.nextOffset c (P.label x)) =
      rv O (x - P.nextOffset c (P.label x)) at hy
    have hold : P.label y = P.label x := by
      by_cases h : P.lead (P.label x) ≠ 0 ∧
          rv O (c - P.offset (P.label x)) = P.lead (P.label x)
      · have hc : c - P.offset (P.label x) ≠ 0 := by
          intro hz
          exact h.1 (h.2.symm.trans ((rv_eq_zero_iff O).2 hz))
        have hx : O.valuation (x - c) < O.valuation (c - P.offset (P.label x)) :=
          (fiber_after_translation hc).1 ((P.leading x).trans h.2.symm)
        have hv := congrArg (unsignedValue O) hy
        simp only [nextOffset, ite_eq_left h, unsignedValue_rv] at hv
        apply P.constant_label
        rw [← h.2]
        exact (fiber_after_translation hc).2 (hv ▸ hx)
      · apply P.constant_label
        simpa [nextOffset, h, P.leading x] using hy
    exact Prod.ext hold (by simpa only [hold] using hy)

/-- The new leading-term label and the retained labels determine the
translated leading term about this center. -/
theorem step_decides (c : K) {x y : K} (hxy : (P.step c).label x = (P.step c).label y) :
    rv O (x - c) = rv O (y - c) := by
  classical
  have hold : P.label x = P.label y := congrArg Prod.fst hxy
  have hnew : rv O (x - P.nextOffset c (P.label x)) =
      rv O (y - P.nextOffset c (P.label y)) := congrArg Prod.snd hxy
  rw [← hold] at hnew
  by_cases ht : P.lead (P.label x) = 0
  · have hx := (rv_eq_zero_iff O).mp ((P.leading x).trans ht)
    have hy := (rv_eq_zero_iff O).mp (hold ▸ (P.leading y).trans (hold ▸ ht))
    have hsame : x = y := (sub_eq_zero.mp hx).trans (sub_eq_zero.mp hy).symm
    exact hsame ▸ rfl
  by_cases hc : rv O (c - P.offset (P.label x)) = P.lead (P.label x)
  · simpa [nextOffset, ht, hc] using hnew
  have hx0 : x - P.offset (P.label x) ≠ 0 := by
    intro hz
    exact ht ((P.leading x).symm.trans ((rv_eq_zero_iff O).2 hz))
  let d := P.offset (P.label x)
  have hx : x ∈ openDisc O x (O.valuation (x - d)) :=
    mem_openDisc_center O ((map_ne_zero _).mpr hx0) x
  have hy : y ∈ openDisc O x (O.valuation (x - d)) := by
    change O.valuation (y - x) < O.valuation (x - d)
    rw [← sub_sub_sub_cancel_right y x d]
    apply (rv_eq_rv_iff_valuation O hx0).mp
    have hy' := P.leading y
    rw [← hold] at hy'
    exact hy'.trans (P.leading x).symm
  have hfar : c ∉ openDisc O x (O.valuation (x - d)) := by
    intro h
    apply hc
    rw [← P.leading x]
    apply (rv_eq_rv_iff_valuation O hx0).mpr
    rwa [sub_sub_sub_cancel_right]
  exact rv_translate_constant_off_disc O hx hy hfar

end UnaryPreparation

end GeneralizedEuler.Section5
