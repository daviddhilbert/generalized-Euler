module

public import Section2.PowerBounded
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

public section

namespace GeneralizedEuler.Section3

variable {k : Type*} [Field k]

/-- In the conjugation group of 3.34, a nonidentity positive dilation
cannot fix a point of the ray. A linear part different from one would
give exactly such a fixed point on the source affine line. -/
theorem linear_part_eq_one {h : k → k} (hi : Function.Injective h)
    (hn : ∀ x, h x ≠ 0) {a b d : k} (hc : ∀ x, h (a * x + b) = d * h x) :
    a = 1 := by
  by_contra ha
  let x := b / (1 - a)
  have hx : a * x + b = x := by
    dsimp [x]
    field_simp [sub_ne_zero.mpr (Ne.symm ha)]
    ring
  have hd := hc x
  rw [hx] at hd
  have hd' : d = 1 := mul_right_cancel₀ (hn x) (hd.symm.trans (one_mul _).symm)
  have hid (z : k) : a * z + b = z := hi (by rw [hc, hd', one_mul])
  have hb : b = 0 := by simpa using hid 0
  exact ha (by simpa [hb] using hid 1)

/-- The equal residue graphs chosen at two origins force translation by
their difference to conjugate to a dilation. -/
theorem translation_of_common_profile {h : k → k} (hi : Function.Injective h)
    (hn : ∀ x, h x ≠ 0) {x y v w : k} (hv : v ≠ 0)
    (he : ∀ s, h (x + s * v) / h x = h (y + s * w) / h y) (z : k) :
    h (z + (y - x)) = (h y / h x) * h z := by
  let a := w / v
  let b := y - a * x
  have hcon (u : k) : h (a * u + b) = (h y / h x) * h u := by
    have hp := he ((u - x) / v)
    rw [div_mul_cancel₀ _ hv, add_sub_cancel x u] at hp
    have ha : y + (u - x) / v * w = a * u + b := by
      dsimp [a,b]
      ring
    rw [ha] at hp
    have heq := (div_eq_div_iff (hn x) (hn y)).mp hp
    field_simp [hn x]
    linear_combination -heq
  have ha := linear_part_eq_one hi hn hcon
  simpa [b, ha] using hcon z

/-- Fixing the origin gives the exponential in the proof of Lemma 3.34.
This supplies the multiplicative law and injectivity directly. -/
theorem exponential_of_common_profiles {h : k → k} (hi : Function.Injective h)
    (hn : ∀ x, h x ≠ 0)
    (hprof : ∀ y, ∃ v w : k, v ≠ 0 ∧ ∀ s, h (0 + s * v) / h 0 = h (y + s * w) / h y) :
    let E := fun z => h z / h 0
    Function.Injective E ∧ E 0 = 1 ∧ ∀ x y, E (x + y) = E x * E y := by
  refine ⟨fun _ _ he => hi ((div_left_inj' (hn 0)).mp he), div_self (hn 0), ?_⟩
  intro x y
  obtain ⟨v,w,hv,hp⟩ := hprof y
  have he := translation_of_common_profile hi hn hv hp x
  rw [sub_zero] at he
  change h (x + y) / h 0 = _
  rw [he]
  ring

variable [LinearOrder k] [IsStrictOrderedRing k]

/-- Final contradiction in 3.34. Eventual increase of E(x)/(x*g(x)),
obtained by the derivative calculation, rules out domination by g. -/
theorem exceeds_power_of_ratio_monotone (E g : k → k)
    (hE : ∀ x, 0 < E x) (hg : ∀ x > 0, 0 < g x) {b : k}
    (hmono : MonotoneOn (fun x => E x / (x * g x)) (Set.Ioi b)) :
    ∀ c, ∃ x > c, g x < E x := by
  intro c
  let a := max b 0 + 1
  have hb : b < a := lt_of_le_of_lt (le_max_left b 0) (lt_add_one _)
  have ha : 0 < a := lt_of_le_of_lt (le_max_right b 0) (lt_add_one _)
  let m := E a / (a * g a)
  have hm : 0 < m := div_pos (hE _) (mul_pos ha (hg _ ha))
  obtain ⟨x, hx⟩ := exists_gt (max (max a c) m⁻¹)
  have hax := (le_max_left a c).trans (le_max_left (max a c) m⁻¹) |>.trans_lt hx
  have hcx := (le_max_right a c).trans (le_max_left (max a c) m⁻¹) |>.trans_lt hx
  have hxpos := ha.trans hax
  have h₁ : (1 : k) < m * x := by
    have := (le_max_right (max a c) m⁻¹).trans_lt hx
    simpa [hm.ne'] using mul_lt_mul_of_pos_left this hm
  have hm' : m ≤ E x / (x * g x) := hmono hb (hb.trans hax) hax.le
  have h₂ := (le_div_iff₀ (mul_pos hxpos (hg _ hxpos))).mp hm'
  refine ⟨x,hcx,?_⟩
  calc
    g x = 1 * g x := (one_mul _).symm
    _ < (m * x) * g x := mul_lt_mul_of_pos_right h₁ (hg _ hxpos)
    _ ≤ E x := by rwa [mul_assoc]

end GeneralizedEuler.Section3
