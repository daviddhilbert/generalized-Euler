module

public import Section5.LiftBoundary
public import Mathlib.Logic.Equiv.Set

/-! Reassemble a lift after lifting its lower-dimensional exceptional
labels separately. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section3

variable {X Y U V : Type*} (p : X → U) (q : Y → V) (e : U ≃ V) (h : X → Y)
  (g : {y : Y // q y ∉ rvBoundary q (Set.range h)} → X)

/-- The two removed label sets, written on the source. -/
@[expose] def boundaryGood : Set U :=
  {u | e u ∉ rvBoundary q (Set.range h) ∧ u ∉ rvBoundary p (Set.range g)}

theorem boundaryBad_eq :
    (boundaryGood p q e h g)ᶜ =
      e ⁻¹' rvBoundary q (Set.range h) ∪ rvBoundary p (Set.range g) := by
  ext u
  classical
  change ¬ (e u ∉ rvBoundary q (Set.range h) ∧ u ∉ rvBoundary p (Set.range g)) ↔
    e u ∈ rvBoundary q (Set.range h) ∨ u ∈ rvBoundary p (Set.range g)
  simp only [not_and_or, not_not]

/-- Glue an ambient bijection on a subset to an equivalence on the
complement, recording which map the result uses on each piece. -/
theorem equivalence_of_bijOn_and_complement {A : Set X} {B : Set Y}
    (hbij : Set.BijOn h A B) (bad : (Aᶜ : Set X) ≃ (Bᶜ : Set Y)) :
    ∃ lift : X ≃ Y,
      (∀ x ∈ A, lift x = h x) ∧ (∀ x : (Aᶜ : Set X), lift x.val = (bad x).val) := by
  classical
  let goodMap (x : A) : B := ⟨h x.val,hbij.1 x.property⟩
  have goodBij : Function.Bijective goodMap := by
    constructor
    · intro a b he
      exact Subtype.ext (hbij.2.1 a.property b.property (congrArg Subtype.val he))
    · intro y
      obtain ⟨x,hx,he⟩ := hbij.2.2 y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let good := Equiv.ofBijective goodMap goodBij
  let lift := (Equiv.Set.sumCompl A).symm.trans ((Equiv.sumCongr good bad).trans (Equiv.Set.sumCompl B))
  refine ⟨lift,?_,?_⟩
  · intro x hx
    have he := (Equiv.Set.sumCompl A).symm_apply_apply (.inl ⟨x,hx⟩)
    change (Equiv.Set.sumCompl A).symm x = _ at he
    simp only [lift, Equiv.trans_apply, he, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.Set.sumCompl_apply_inl]
    rfl
  · intro x
    have he := (Equiv.Set.sumCompl A).symm_apply_apply (.inr x)
    change (Equiv.Set.sumCompl A).symm x.val = _ at he
    simp only [lift, Equiv.trans_apply, he, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.Set.sumCompl_apply_inr]

/-- Glue the good-region bijection to a lift of the exceptional labels.
The second branch is the one supplied by the dimension induction. -/
theorem lift_of_boundary_and_exceptional
    (hlabel : ∀ x, q (h x) = e (p x)) (hg : ∀ y, h (g y) = y.val)
    (bad : ((p ⁻¹' boundaryGood p q e h g)ᶜ : Set X) ≃
      ((q ⁻¹' (e '' boundaryGood p q e h g))ᶜ : Set Y))
    (hbad : ∀ x, q (bad x).val = e (p x.val)) :
    ∃ lift : X ≃ Y, ∀ x, q (lift x) = e (p x) := by
  obtain ⟨lift,hgood,hbad'⟩ := equivalence_of_bijOn_and_complement h
    (bijOn_lift_off_boundaries p q e h hlabel g hg) bad
  refine ⟨lift,?_⟩
  intro x
  by_cases hx : p x ∈ boundaryGood p q e h g
  · rw [hgood x hx]
    exact hlabel x
  · rw [hbad' ⟨x,hx⟩]
    exact hbad ⟨x,hx⟩

theorem image_label_compl (A : Set U) : e '' Aᶜ = (e '' A)ᶜ := by
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩ ⟨w,hw,he⟩
    exact hu ((e.injective he) ▸ hw)
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    exact fun hu => hv ⟨e.symm v,hu,e.apply_symm_apply v⟩

/-- The union of the two exceptional label sets is below the current
dimension bound. Consequently the lower-dimensional lifting theorem
applies to their entire union before the two regions are glued. -/
theorem full_arity_lift_from_boundary_bound {D : Type*} [LinearOrder D]
    (dimU : Set U → D) (dimV : Set V → D) (d : D)
    (transport : ∀ A : Set V, dimU (e ⁻¹' A) = dimV A)
    (dimUnion : ∀ A B, dimU (A ∪ B) ≤ max (dimU A) (dimU B))
    (hTarget : dimV (rvBoundary q (Set.range h)) < d)
    (hSource : dimU (rvBoundary p (Set.range g)) < d)
    (hlabel : ∀ x, q (h x) = e (p x)) (hg : ∀ y, h (g y) = y.val)
    (lower : ∀ A : Set U, dimU A < d →
      ∃ f : (p ⁻¹' A : Set X) ≃ (q ⁻¹' (e '' A) : Set Y),
        ∀ x, q (f x).val = e (p x.val)) :
    ∃ lift : X ≃ Y, ∀ x, q (lift x) = e (p x) := by
  let A := boundaryGood p q e h g
  have hdim : dimU Aᶜ < d := by
    rw [show Aᶜ = _ from boundaryBad_eq p q e h g]
    apply (dimUnion _ _).trans_lt
    rw [transport]
    exact max_lt hTarget hSource
  have hb :
      ∃ f : (p ⁻¹' Aᶜ : Set X) ≃ (((q ⁻¹' (e '' A))ᶜ) : Set Y),
        ∀ x, q (f x).val = e (p x.val) := by
    have hf := lower Aᶜ hdim
    rw [image_label_compl] at hf
    exact hf
  obtain ⟨eBad,hBad⟩ := hb
  exact lift_of_boundary_and_exceptional p q e h g hlabel hg eBad hBad

end GeneralizedEuler.Section5
