module

public import Section4.TupleFibers

/-! In a rectangle of whole-fiber matches the two factor relations are
graphs. The maps on the full RV fibers can depend on the residue input. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4

def matchingGraphEquiv {A B : Type*} (R : A → B → Prop)
    (single : ∀ {x y z}, R x y → R x z → y = z)
    (inj : ∀ {x y z}, R x z → R y z → x = y) :
    {x // ∃ y, R x y} ≃ {y // ∃ x, R x y} where
  toFun x := ⟨x.property.choose, x.val, x.property.choose_spec⟩
  invFun y := ⟨y.property.choose, y.val, y.property.choose_spec⟩
  left_inv x := by
    let h : ∃ t, R t x.property.choose := ⟨x.val,x.property.choose_spec⟩
    exact Subtype.ext (inj h.choose_spec x.property.choose_spec)
  right_inv y := by
    let h : ∃ t, R y.property.choose t := ⟨y.val,y.property.choose_spec⟩
    exact Subtype.ext (single h.choose_spec y.property.choose_spec)

theorem matchingGraphEquiv_iff {A B : Type*} (R : A → B → Prop)
    (single : ∀ {x y z}, R x y → R x z → y = z)
    (inj : ∀ {x y z}, R x z → R y z → x = y)
    (a : {x // ∃ y, R x y}) (b : B) :
    (matchingGraphEquiv R single inj a).val = b ↔ R a.val b :=
  ⟨fun eq => eq ▸ a.property.choose_spec,fun h => single a.property.choose_spec h⟩

/-- Separation of whole-fiber matches gives independent residue and value
maps on the projections of each nonempty matching rectangle. -/
theorem factor_matching_rectangle {A B C D : Type*} (R : A → B → Prop) (V : C → D → Prop)
    (nonemptyR : ∃ a b, R a b) (nonemptyV : ∃ c d, V c d)
    (single : ∀ {a b b' c d d'}, R a b → V c d → R a b' → V c d' → b = b' ∧ d = d')
    (inj : ∀ {a a' b c c' d}, R a b → V c d → R a' b → V c' d → a = a' ∧ c = c') :
    ∃ (p : {a // ∃ b, R a b} ≃ {b // ∃ a, R a b})
      (η : {c // ∃ d, V c d} ≃ {d // ∃ c, V c d}),
      ∀ a c b d, R a.val b.val ∧ V c.val d.val ↔ p a = b ∧ η c = d := by
  obtain ⟨a₀,b₀,hr⟩ := nonemptyR
  obtain ⟨c₀,d₀,hv⟩ := nonemptyV
  have sr : ∀ {x y z}, R x y → R x z → y = z := fun h h' => (single h hv h' hv).1
  have ir : ∀ {x y z}, R x z → R y z → x = y := fun h h' => (inj h hv h' hv).1
  have sv : ∀ {x y z}, V x y → V x z → y = z := fun h h' => (single hr h hr h').2
  have iv : ∀ {x y z}, V x z → V y z → x = y := fun h h' => (inj hr h hr h').2
  refine ⟨matchingGraphEquiv R sr ir,matchingGraphEquiv V sv iv,fun a c b d => ?_⟩
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨Subtype.ext (sr a.property.choose_spec ha),Subtype.ext (sv c.property.choose_spec hc)⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨a.property.choose_spec,c.property.choose_spec⟩

/-- A bijection over matching labels restricts to a bijection on each
individual fiber, retaining the label as an argument. -/
def fiberMapOfMatching {A B X Y : Type*} (a : X → A) (b : Y → B) (p : A ≃ B)
    (f : X ≃ Y) (matchLabel : ∀ x, b (f x) = p (a x)) (u : A) :
    {x // a x = u} ≃ {y // b y = p u} where
  toFun x := ⟨f x.val,(matchLabel _).trans (congrArg p x.property)⟩
  invFun y := ⟨f.symm y.val,p.injective (by rw [← matchLabel,f.apply_symm_apply,y.property])⟩
  left_inv x := Subtype.ext (f.symm_apply_apply _)
  right_inv y := Subtype.ext (f.apply_symm_apply _)

end GeneralizedEuler.Section4
