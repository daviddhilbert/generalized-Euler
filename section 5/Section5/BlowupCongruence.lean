module

public import Section5.BlowupIteration
public import Mathlib.RingTheory.Congruence.Defs

/-! A common-blowup relation is a semiring congruence once single
blowups can be transported through adding and multiplying a fixed
object. -/

public section

namespace GeneralizedEuler.Section5

variable {T : Type*} (step : T → T → Prop)

theorem blowupSteps_invariant {R : Type*} (w : T → R) (one : ∀ a b, step a b → w a = w b)
    {a b : T} {n : Nat} (h : BlowupSteps step n a b) : w a = w b := by
  induction n generalizing a with
  | zero =>
    have he : a = b := h
    exact congrArg w he
  | succ n ih =>
    obtain ⟨x,hx,tail⟩ := h
    exact (one a x hx).trans (ih tail)

theorem commonBlowup_invariant {R : Type*} (w : T → R) (one : ∀ a b, step a b → w a = w b)
    {a b : T} (h : CommonBlowup step a b) : w a = w b := by
  obtain ⟨c,m,n,ha,hb⟩ := h
  exact (blowupSteps_invariant step w one ha).trans (blowupSteps_invariant step w one hb).symm

theorem blowupSteps_map (f : T → T) (pres : ∀ a b, step a b → step (f a) (f b))
    {a b : T} {n : Nat} (h : BlowupSteps step n a b) : BlowupSteps step n (f a) (f b) := by
  induction n generalizing a with
  | zero =>
    have he : a = b := h
    exact congrArg f he
  | succ n ih =>
    obtain ⟨x,hx,tail⟩ := h
    exact ⟨f x,pres a x hx,ih tail⟩

theorem commonBlowup_map (f : T → T) (pres : ∀ a b, step a b → step (f a) (f b))
    {a b : T} (h : CommonBlowup step a b) : CommonBlowup step (f a) (f b) := by
  obtain ⟨c,m,n,ha,hb⟩ := h
  exact ⟨f c,m,n,blowupSteps_map step f pres ha,blowupSteps_map step f pres hb⟩

variable [CommSemiring T]

/-- One-step transport through tagged sums and tensor products descends
to the corresponding operations on common-refinement classes. -/
def commonBlowupRingCon
    (diamond : ∀ {a b c}, step a b → step a c → ∃ d, step b d ∧ step c d)
    (addStable : ∀ a b w, step a b → step (a + w) (b + w))
    (mulStable : ∀ a b w, step a b → step (a * w) (b * w)) : RingCon T where
  r := CommonBlowup step
  iseqv := commonBlowup_equivalence step diamond
  add' := by
    intro a b c d h g
    have first : CommonBlowup step (a + c) (b + c) :=
      commonBlowup_map step (fun x => x + c) (fun _ _ => addStable _ _ c) h
    have second : CommonBlowup step (b + c) (b + d) := by
      rw [add_comm b c,add_comm b d]
      exact commonBlowup_map step (fun x => x + b) (fun _ _ => addStable _ _ b) g
    exact (commonBlowup_equivalence step diamond).trans first second
  mul' := by
    intro a b c d h g
    have first : CommonBlowup step (a * c) (b * c) :=
      commonBlowup_map step (fun x => x * c) (fun _ _ => mulStable _ _ c) h
    have second : CommonBlowup step (b * c) (b * d) := by
      rw [mul_comm b c,mul_comm b d]
      exact commonBlowup_map step (fun x => x * b) (fun _ _ => mulStable _ _ b) g
    exact (commonBlowup_equivalence step diamond).trans first second

theorem commonBlowupRingCon_iff
    (diamond : ∀ {a b c}, step a b → step a c → ∃ d, step b d ∧ step c d)
    (addStable : ∀ a b w, step a b → step (a + w) (b + w))
    (mulStable : ∀ a b w, step a b → step (a * w) (b * w)) (a b : T) :
    commonBlowupRingCon step diamond addStable mulStable a b ↔ CommonBlowup step a b :=
  Iff.rfl

end GeneralizedEuler.Section5
