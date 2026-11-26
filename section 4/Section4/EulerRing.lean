module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic

/-! The graded value ring in its two Euler coordinates. The constant terms agree
because there is a single generator in degree zero. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial

abbrev Poly := Polynomial ℤ

@[expose] def valueRing : Subring (Poly × Poly) where
  carrier := {p | p.1.eval 0 = p.2.eval 0}
  one_mem' := rfl
  zero_mem' := rfl
  add_mem' {p q} hp hq := by
    change (p.1 + q.1).eval 0 = (p.2 + q.2).eval 0
    simp only [eval_add]; rw [hp, hq]
  neg_mem' {p} hp := by
    change (-p.1).eval 0 = (-p.2).eval 0
    rw [eval_neg, eval_neg, hp]
  mul_mem' {p q} hp hq := by
    change (p.1 * q.1).eval 0 = (p.2 * q.2).eval 0
    simp only [eval_mul]; rw [hp, hq]

@[expose] def point : valueRing := ⟨(X, X), rfl⟩
@[expose] def ray : valueRing := ⟨(-X, 0), by change (-X : Poly).eval 0 = (0 : Poly).eval 0; simp⟩

theorem ray_square : ray ^ 2 = -(point * ray) := by
  apply Subtype.ext
  exact Prod.ext (by change (-X : Poly)^2 = -(X * -X); ring)
    (by change (0 : Poly)^2 = -(X * 0); simp)

@[expose] def special : valueRing := 1 + 2 * ray + point

theorem special_coordinates : special.val = (1 - X, 1 + X) := by
  apply Prod.ext
  · change (1 + 2 * (-X) + X : Poly) = 1 - X
    ring
  · change (1 + 2 * 0 + X : Poly) = 1 + X
    ring

/-- Evaluate the geometric coordinate at 1 and the bounded coordinate at -1. -/
@[expose] def evaluations : valueRing →+* ℤ × ℤ :=
  (((evalRingHom 1).comp (RingHom.fst Poly Poly)).prod
    ((evalRingHom (-1)).comp (RingHom.snd Poly Poly))).comp valueRing.subtype

theorem evaluations_surjective : Function.Surjective evaluations := by
  rintro ⟨a,b⟩
  refine ⟨⟨(C a * X, -C b * X), ?_⟩, ?_⟩
  · change (C a * X).eval 0 = (-C b * X).eval 0
    simp
  · change ((C a * X).eval 1, (-C b * X).eval (-1)) = _
    simp

theorem ker_evaluations : RingHom.ker evaluations = Ideal.span {special} := by
  apply le_antisymm
  · intro p hp
    change (p.val.1.eval 1, p.val.2.eval (-1)) = (0,0) at hp
    obtain ⟨a, ha⟩ := (dvd_iff_isRoot.mpr (congrArg Prod.fst hp) :
      X - C (1 : ℤ) ∣ p.val.1)
    obtain ⟨b, hb⟩ := (dvd_iff_isRoot.mpr (congrArg Prod.snd hp) :
      X - C (-1 : ℤ) ∣ p.val.2)
    have hconst := p.property
    change p.val.1.eval 0 = p.val.2.eval 0 at hconst
    rw [ha,hb] at hconst
    simp at hconst
    let q : valueRing := ⟨(-a,b), by change (-a).eval 0 = b.eval 0; simpa using hconst⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨q, Subtype.ext ?_⟩
    change p.val = special.val * (-a,b)
    rw [special_coordinates]
    exact Prod.ext (by simp [ha, sub_mul]) (by simp [hb, add_comm])
  · apply Ideal.span_le.mpr
    intro p hp
    obtain rfl : p = special := hp
    change (special.val.1.eval 1, special.val.2.eval (-1)) = (0,0)
    rw [special_coordinates]
    simp

def quotientEulerEquiv : (valueRing ⧸ Ideal.span {special}) ≃+* ℤ × ℤ :=
  (Ideal.quotEquivOfEq ker_evaluations.symm).trans
    (RingHom.quotientKerEquivOfSurjective evaluations_surjective)

/-- The orthogonal idempotents of the quotient force either Euler evaluation. -/
theorem integer_character (f : ℤ × ℤ →+* ℤ) :
    f = RingHom.fst ℤ ℤ ∨ f = RingHom.snd ℤ ℤ := by
  let e : ℤ × ℤ := (1,0)
  let d : ℤ × ℤ := (0,1)
  have hsum : f e + f d = 1 := by rw [← map_add]; exact f.map_one
  have hmul : f e * f d = 0 := by rw [← map_mul]; exact f.map_zero
  have formula (a b : ℤ) : f (a,b) = a * f e + b * f d := by
    have h : (a,b) = (a : ℤ × ℤ) * e + (b : ℤ × ℤ) * d := by ext <;> simp [e,d]
    rw [h, map_add, map_mul, map_mul, map_intCast, map_intCast]
    simp
  rcases mul_eq_zero.mp hmul with he | hd
  · right
    ext1 ⟨a,b⟩
    rw [formula, he, (by omega : f d = 1)]
    simp
  · left
    ext1 ⟨a,b⟩
    rw [formula, hd, (by omega : f e = 1)]
    simp

end GeneralizedEuler.Section4
