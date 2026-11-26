module

public import Section4.EulerRing

/-! Cell scissors in the ambient degree and the normal form in the graded value ring. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial

variable {V B : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

def aboveGraph (f : B → V) : {p : B × V // f p.1 < p.2} ≃ B × {v : V // 0 < v} where
  toFun p := (p.1.1, ⟨p.1.2 - f p.1.1, sub_pos.mpr p.property⟩)
  invFun q := ⟨(q.1,q.2.val + f q.1), lt_add_of_pos_left _ q.2.property⟩
  left_inv _ := Subtype.ext (Prod.ext rfl (sub_add_cancel _ _))
  right_inv _ := Prod.ext rfl (Subtype.ext (add_sub_cancel_right _ _))

/-- Diagonal and the two strictly ordered sectors of a ray squared. -/
def raySquareCut : {x : V // 0 < x} × {x : V // 0 < x} ≃
    {x : V // 0 < x} ⊕
      ({x : V // 0 < x} × {x : V // 0 < x}) ⊕ ({x : V // 0 < x} × {x : V // 0 < x}) where
  toFun p := if h : p.1.val < p.2.val then .inr (.inl (p.1, ⟨_, sub_pos.mpr h⟩))
    else if h' : p.2.val < p.1.val then .inr (.inr (p.2, ⟨_, sub_pos.mpr h'⟩))
    else .inl p.1
  invFun
    | .inl x => (x,x)
    | .inr (.inl (x,y)) => (x,⟨y.val+x.val,add_pos y.property x.property⟩)
    | .inr (.inr (x,y)) => (⟨y.val+x.val,add_pos y.property x.property⟩,x)
  left_inv p := by
    dsimp only
    split_ifs with h h'
    · exact Prod.ext rfl (Subtype.ext (sub_add_cancel _ _))
    · exact Prod.ext (Subtype.ext (sub_add_cancel _ _)) rfl
    · exact Prod.ext rfl (Subtype.ext (le_antisymm (le_of_not_gt h') (le_of_not_gt h)))
  right_inv q := by
    rcases q with x | (⟨x,y⟩ | ⟨x,y⟩)
    · simp
    · simp [lt_add_of_pos_left x.val y.property]
    · simp [lt_add_of_pos_left x.val y.property, (lt_add_of_pos_left x.val y.property).not_gt]

/-- A bounded open strip, graph, and upper ray partition the lower ray. -/
def stripCut (f g : B → V) (h : ∀ b, f b < g b) :
    {p : B × V // f p.1 < p.2} ≃ {p : B × V // f p.1 < p.2 ∧ p.2 < g p.1} ⊕
      B ⊕ {p : B × V // g p.1 < p.2} where
  toFun p := if h₁ : p.val.2 < g p.val.1 then .inl ⟨p.val,p.property,h₁⟩
    else if h₂ : g p.val.1 < p.val.2 then .inr (.inr ⟨p.val,h₂⟩) else .inr (.inl p.val.1)
  invFun
    | .inl p => ⟨p.val,p.property.1⟩
    | .inr (.inl b) => ⟨(b,g b),h b⟩
    | .inr (.inr p) => ⟨p.val,lt_trans (h _) p.property⟩
  left_inv p := by
    dsimp only
    split_ifs with h₁ h₂
    · rfl
    · rfl
    · exact Subtype.ext (Prod.ext rfl (le_antisymm (le_of_not_gt h₁) (le_of_not_gt h₂)))
  right_inv q := by
    rcases q with p | (b | p)
    · simp [p.property.2]
    · simp
    · simp [p.property.not_gt, p.property]

section Calculation
variable {R : Type*} [CommRing R]

theorem strip_class {lower upper graph strip : R} (cuts : lower = strip + graph + upper)
    (translate : lower = upper) : strip = -graph := by linear_combination translate - cuts

theorem square_class {e h : R} (cuts : h*h = e*h + h*h + h*h) :
    h^2 = -(e*h) := by linear_combination -cuts

theorem ray_power {e h : R} (hh : h^2 = -(e*h)) (n : ℕ) :
    h^(n+1) = (-e)^n * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc h^(n+1+1) = (-e)^n * h^2 := by rw [pow_succ _ (n+1), ih]; ring
         _ = (-e)^(n+1) * h := by rw [hh, pow_succ]; ring

end Calculation

@[expose] def diagonal : Poly →+* valueRing where
  toFun p := ⟨(p,p), rfl⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Every pair with equal constants has a unique expression q(e) + H r(e). -/
theorem normal_form (p : valueRing) :
    ∃! qr : Poly × Poly, p = diagonal qr.1 + ray * diagonal qr.2 := by
  have hz : (p.val.2 - p.val.1).eval 0 = 0 :=
    (eval_sub _ _ (0 : ℤ)).trans (sub_eq_zero.mpr p.property.symm)
  have hd : X ∣ (p.val.2 - p.val.1) := by
    simpa using (dvd_iff_isRoot.mpr hz : X - C (0 : ℤ) ∣ _)
  obtain ⟨r,hr⟩ := hd
  refine ⟨(p.val.2,r), Subtype.ext (Prod.ext ?_ ?_), ?_⟩
  · change p.val.1 = p.val.2 + (-X)*r
    linear_combination -hr
  · change p.val.2 = p.val.2 + 0*r
    ring
  · rintro ⟨q,s⟩ he
    have hq := congrArg (fun a : valueRing => a.val.2) he
    change p.val.2 = q + 0*s at hq
    simp at hq
    subst q
    have hs := congrArg (fun a : valueRing => a.val.1) he
    change p.val.1 = p.val.2 + (-X)*s at hs
    refine Prod.ext rfl (mul_left_cancel₀ (X_ne_zero : (X : Poly) ≠ 0) ?_)
    linear_combination hs + hr

/-- The two integral coordinates in positive ambient degree recover the
coefficients of the point and ray generators. -/
theorem homogeneous_coordinates (k : ℕ) (a b : ℤ) :
    ((diagonal (C a) * point^(k+1) + diagonal (C b) * point^k * ray).val) =
      (C (a-b)*X^(k+1), C a*X^(k+1)) := by
  have hp (n : ℕ) : (point^n).val = (X^n,X^n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Subring.coe_mul, ih, pow_succ]
      rfl
  change (C a,C a) * (point^(k+1)).val + (C b,C b) * (point^k).val * (-X,0) = _
  rw [hp,hp,map_sub,pow_succ]
  apply Prod.ext <;> simp; ring

end GeneralizedEuler.Section4
