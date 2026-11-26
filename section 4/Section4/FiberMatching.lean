module

public import Section2.ValueSplitting
public import Section2.SeparatedSets
public import Mathlib.Tactic

/-! The action of the value shears on positive RV. A functional on the
quotient by the base values has exactly the fixed parameters required in 4.20. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V]
variable (v : T →ₗ[F] V) (G : Submodule F V)

@[expose] def shear (L : (V ⧸ G) →ₗ[F] v.ker) : T ≃ₗ[F] T where
  toLinearMap := LinearMap.id + v.ker.subtype.comp (L.comp (G.mkQ.comp v))
  invFun x := x - (L (G.mkQ (v x))).val
  left_inv x := by
    change (x + (L _).val) - (L (G.mkQ (v (x + (L _).val)))).val = x
    simp
  right_inv x := by
    change x - (L _).val + (L (G.mkQ (v (x - (L _).val)))).val = x
    simp

theorem shear_def (L : (V ⧸ G) →ₗ[F] v.ker) (t : T) :
    shear v G L t = t + (L (G.mkQ (v t))).val := rfl

theorem shear_preserves_value (L : (V ⧸ G) →ₗ[F] v.ker) (t : T) :
    v (shear v G L t) = v t := by simp [shear_def]

theorem shear_fixes_base (L : (V ⧸ G) →ₗ[F] v.ker) {t : T} (ht : v t ∈ G) :
    shear v G L t = t := by simp [shear_def, (Submodule.Quotient.mk_eq_zero G).mpr ht]

/-- An independent value tuple supports arbitrary changes of representatives
by a single shear fixing the base. -/
theorem transitive_independent_fiber {ι : Type*} (x y : ι → T)
    (h : LinearIndependent F (G.mkQ ∘ v ∘ x)) (hy : v ∘ x = v ∘ y) :
    ∃ L : (V ⧸ G) →ₗ[F] v.ker, shear v G L ∘ x = y := by
  let u := G.mkQ ∘ v ∘ x
  let diff (i : ι) : v.ker := ⟨y i - x i, by
    change v _ = 0
    rw [map_sub, ← show v (x i) = v (y i) from congrFun hy i, sub_self]⟩
  let f := (Finsupp.linearCombination F diff).comp h.repr
  obtain ⟨L,hL⟩ := f.exists_extend
  refine ⟨L, funext fun i => ?_⟩
  have hi : u i ∈ Submodule.span F (Set.range u) := Submodule.subset_span ⟨i,rfl⟩
  have ht := DFunLike.congr_fun hL (⟨u i,hi⟩ : Submodule.span F (Set.range u))
  change L (u i) = (Finsupp.linearCombination F diff) (h.repr ⟨u i,hi⟩) at ht
  rw [h.repr_eq_single i _ rfl, Finsupp.linearCombination_single, one_smul] at ht
  change x i + (L (u i)).val = y i
  rw [ht]
  exact add_sub_cancel _ _

@[expose] def valueSpan {ι : Type*} (x : ι → T) : Submodule F (V ⧸ G) :=
  Submodule.span F (Set.range (G.mkQ ∘ v ∘ x))

/-- Fixing the output and moving a missing input value contradicts uniqueness
in the inverse graph. This uses the nonzero residue direction explicitly. -/
theorem span_le_of_shear_graph {ι κ : Type*} (R : (ι → T) → (κ → T) → Prop)
    (invariant : ∀ L x y, R x y → R (shear v G L ∘ x) (shear v G L ∘ y))
    (unique : ∀ {x x' y}, R x y → R x' y → x = x')
    (d : v.ker) (hd : d ≠ 0) {x y} (hxy : R x y) :
    valueSpan v G x ≤ valueSpan v G y := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  by_contra hi
  obtain ⟨L,hL,hker⟩ := Submodule.exists_le_ker_of_notMem hi
  let move := L.smulRight d
  have fixes : shear v G move ∘ y = y := by
    funext j
    have hj : L (G.mkQ (v (y j))) = 0 := hker (Submodule.subset_span ⟨j,rfl⟩)
    change y j + ((L (G.mkQ (v (y j)))) • d).val = y j
    rw [hj, zero_smul]; simp
  have hx := invariant move x y hxy
  rw [fixes] at hx
  have he := congrFun (unique hx hxy) i
  change x i + (move (G.mkQ (v (x i)))).val = x i at he
  have hz : move (G.mkQ (v (x i))) = 0 := Subtype.ext (by change _ = (0 : T); simpa only [add_eq_left] using he)
  exact (smul_ne_zero hL hd) hz

theorem span_eq_of_shear_bijection {ι κ : Type*} (R : (ι → T) → (κ → T) → Prop)
    (invariant : ∀ L x y, R x y → R (shear v G L ∘ x) (shear v G L ∘ y))
    (inj : ∀ {x x' y}, R x y → R x' y → x = x')
    (single : ∀ {x y y'}, R x y → R x y' → y = y')
    (d : v.ker) (hd : d ≠ 0) {x y} (hxy : R x y) :
    valueSpan v G x = valueSpan v G y :=
  le_antisymm (span_le_of_shear_graph v G R invariant inj d hd hxy)
    (span_le_of_shear_graph v G (fun y x => R x y) (fun L y x => invariant L x y)
      single d hd hxy)

/-- A nonempty rectangular piece of a bijective relation induces separate
bijections between the projections of each factor. -/
theorem rectangle_single_valued {A B C D : Type*} (P : A → B → Prop) (Q : C → D → Prop)
    (hq : ∃ c d, Q c d)
    (unique : ∀ {a b b' c d d'}, P a b → Q c d → P a b' → Q c d' → (b,d) = (b',d')) :
    ∀ {a b b'}, P a b → P a b' → b = b' := by
  obtain ⟨c,d,h⟩ := hq
  exact fun h₁ h₂ => congrArg Prod.fst (unique h₁ h h₂ h)

end GeneralizedEuler.Section4
