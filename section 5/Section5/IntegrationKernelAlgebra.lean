module

public import Section5.BlowupCongruence
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The algebra of the integration quotient after the geometric
common-blowup criterion has been proved. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

variable {A B : Type*} [CommSemiring A] [CommSemiring B]
  {R T : Type*} [CommRing R] [CommRing T]
  (step : A → A → Prop) (lift : A →+* B)

def integration_semiring_equiv
    (surjective : Function.Surjective lift)
    (diamond : ∀ {a b c}, step a b → step a c → ∃ d, step b d ∧ step c d)
    (addStable : ∀ a b w, step a b → step (a + w) (b + w))
    (mulStable : ∀ a b w, step a b → step (a * w) (b * w))
    (geometric : ∀ a b, CommonBlowup step a b ↔ lift a = lift b) :
    (commonBlowupRingCon step diamond addStable mulStable).Quotient ≃+* B := by
  have equal : commonBlowupRingCon step diamond addStable mulStable = RingCon.ker lift :=
    RingCon.ext (fun a b =>
      (commonBlowupRingCon_iff step diamond addStable mulStable a b).trans (geometric a b))
  rw [equal]
  exact RingCon.quotientKerEquivOfSurjective lift surjective

variable (rvGroup : A →+* R) (vfGroup : B →+* T) (liftGroup : R →+* T)
  (commutes : ∀ a, liftGroup (rvGroup a) = vfGroup (lift a))

include commutes in
theorem groupified_lift_surjective (surjective : Function.Surjective lift)
    (differences : ∀ y : T, ∃ b c : B, y = vfGroup b - vfGroup c) :
    Function.Surjective liftGroup := by
  intro y
  obtain ⟨b,c,rfl⟩ := differences y
  obtain ⟨x,rfl⟩ := surjective b
  obtain ⟨z,rfl⟩ := surjective c
  exact ⟨rvGroup x - rvGroup z,by rw [map_sub,commutes x,commutes z]⟩

include commutes in
/-- Cancellation in the groupified VF ring supplies a common positive
summand. Lift that summand, use the geometric criterion on the two
positive classes, and then cancel it modulo the elementary relation. -/
theorem groupified_lift_kernel_of_common_blowups (surjective : Function.Surjective lift)
    (differences : ∀ r : R, ∃ a b : A, r = rvGroup a - rvGroup b)
    (cancel : ∀ b c, vfGroup b = vfGroup c → ∃ d : B, b+d = c+d)
    (geometric : ∀ a b, lift a = lift b → CommonBlowup step a b)
    (d : R) (killed : liftGroup d = 0)
    (elementary : ∀ a b, step a b → rvGroup b - rvGroup a ∈ Ideal.span {d}) :
    RingHom.ker liftGroup = Ideal.span {d} := by
  let J := Ideal.span ({d} : Set R)
  let q := Ideal.Quotient.mk J
  apply le_antisymm
  · intro r hr
    change liftGroup r = 0 at hr
    obtain ⟨a,b,rfl⟩ := differences r
    rw [map_sub,commutes a,commutes b,sub_eq_zero] at hr
    obtain ⟨c,hc⟩ := cancel (lift a) (lift b) hr
    obtain ⟨z,rfl⟩ := surjective c
    have liftEq : lift (a+z) = lift (b+z) := by
      simpa only [map_add] using hc
    have one (u v : A) (huv : step u v) : q (rvGroup u) = q (rvGroup v) := by
      have hz : q (rvGroup v - rvGroup u) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (elementary u v huv)
      rw [map_sub,sub_eq_zero] at hz
      exact hz.symm
    have eq := commonBlowup_invariant step (q ∘ rvGroup) one (geometric (a+z) (b+z) liftEq)
    change q (rvGroup (a+z)) = q (rvGroup (b+z)) at eq
    rw [map_add,map_add,map_add,map_add] at eq
    have last := add_right_cancel eq
    apply Ideal.Quotient.eq_zero_iff_mem.1
    change q (rvGroup a - rvGroup b) = 0
    rw [map_sub,sub_eq_zero]
    exact last
  · apply Ideal.span_le.2
    rintro _ rfl
    exact killed

end GeneralizedEuler.Section5
