module

public import Section4.TensorComparison

/-! Dependence of a value tuple over the base and matching of whole fibers. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V] (v : T →ₗ[F] V) (W : Submodule F T)

def fullFiber {ι : Type*} (α : ι → V) : Set (ι → T) := {x | v ∘ x = α}

/-- 4.18. A cut in a single value fiber supplies an actual monomial on the
other representatives and one leading term in the original base. -/
theorem dependent_coordinate {n : ℕ} (α : Fin n → V) (U : Set (Fin n → T))
    (invariant : ∀ L x, x ∈ U → shear v (W.map v) L ∘ x ∈ U)
    (x y : Fin n → T) (hx : x ∈ fullFiber v α) (hy : y ∈ fullFiber v α)
    (hin : x ∈ U) (hout : y ∉ U) :
    ∃ i : Fin n, ∃ (c : {j : Fin n // j ≠ i} → F) (u : W),
      ∀ t : {j : Fin n // j ≠ i} → T, (∀ j, v (t j) = α j.val) →
        v (u.val + ∑ j, c j • t j) = α i := by
  classical
  let G := W.map v
  change v ∘ x = α at hx
  change v ∘ y = α at hy
  have dep : ¬ LinearIndependent F (G.mkQ ∘ α) := by
    intro hi
    obtain ⟨L,hL⟩ := transitive_independent_fiber v G x y (hx.symm ▸ hi) (hx.trans hy.symm)
    exact hout (hL ▸ invariant L x hin)
  rw [linearIndependent_iff_notMem_span] at dep
  push Not at dep
  obtain ⟨i,hi⟩ := dep
  let other (j : {j : Fin n // j ≠ i}) := G.mkQ (α j.val)
  have eq : (G.mkQ ∘ α) '' (Set.univ \ {i}) = Set.range other := by
    ext t
    exact ⟨fun ⟨j,hj,he⟩ => ⟨⟨j,hj.2⟩,he⟩,
      fun ⟨j,he⟩ => ⟨j.val,⟨Set.mem_univ _,j.property⟩,he⟩⟩
  rw [eq] at hi
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hi
  have hz : G.mkQ (α i - ∑ j, c j • α j.val) = 0 := by
    rw [map_sub,map_sum]
    simp only [map_smul]
    exact sub_eq_zero.mpr hc.symm
  obtain ⟨u,hu,he⟩ := (Submodule.Quotient.mk_eq_zero G).mp hz
  refine ⟨i,c,⟨u,hu⟩,fun t ht => ?_⟩
  rw [map_add,map_sum,he]
  simp only [map_smul,ht,sub_add_cancel]

/-- At maximal height an equivariant graph matches the entire input and
output fibers. Both containments are needed. -/
theorem whole_fiber_match {n : ℕ} (G : Submodule F V) (R : (Fin n → T) → (Fin n → T) → Prop)
    (invariant : ∀ L x y, R x y → R (shear v G L ∘ x) (shear v G L ∘ y))
    (inj : ∀ {x x' y}, R x y → R x' y → x = x')
    (single : ∀ {x y y'}, R x y → R x y' → y = y')
    (d : v.ker) (hd : d ≠ 0) {x y} (hxy : R x y)
    (hi : LinearIndependent F (G.mkQ ∘ v ∘ x)) :
    {b | ∃ a ∈ fullFiber v (v ∘ x), R a b} = fullFiber v (v ∘ y) := by
  have hs := span_eq_of_shear_bijection v G R invariant inj single d hd hxy
  have hj := (independent_at_max_height v G x y hi hs le_rfl).2
  ext b
  constructor
  · rintro ⟨a,ha,hr⟩
    obtain ⟨L,hL⟩ := transitive_independent_fiber v G x a hi (Eq.symm ha)
    have hi' := invariant L x y hxy
    rw [hL] at hi'
    rw [← single hi' hr]
    exact funext fun k => shear_preserves_value v G L (y k)
  · intro hb
    obtain ⟨L,hL⟩ := transitive_independent_fiber v G y b hj (Eq.symm hb)
    exact ⟨_,funext (fun k => shear_preserves_value v G L (x k)), hL ▸ invariant L x y hxy⟩

end GeneralizedEuler.Section4
