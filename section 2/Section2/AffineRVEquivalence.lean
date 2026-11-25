module

public import Section2.DefinableAffineCharts
public import Section2.PositiveRVMonomials

/-! The positive affine pullback is the retained pullback times a residue
factor for each omitted coordinate. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder RVValueSection

universe u v w z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  {E : Type w} (P : E → RV0 O → RV0 O) {I : Type} {m n : ℕ}
  (coords : Fin m ⊕ Fin n ≃ I)
  (coeff : Fin n → Fin m → E) (u : Fin n → RV0 O) (D : Set (Fin m → RV0 O))

/-- A positive affine value piece, expressed using the unsigned values
of its monomial representatives. -/
@[expose]
def affineRVSource : Set (I → RV0 O) :=
  {x | (∀ i, IsPositiveRV O (x i)) ∧ x ∘ coords ∘ Sum.inl ∈ D ∧
    ∀ i, valueCoordinate (x (coords (.inr i))) =
      valueCoordinate (rvAffineMonomial O P coeff u (x ∘ coords ∘ Sum.inl) i)}

/-- The retained coordinates remain in the same pullback and the
omitted coordinates become positive residues. -/
@[expose]
def affineRVTarget : Set (Fin n ⊕ Fin m → RV0 O) :=
  {y | (∀ i, IsPositiveRV O (y i)) ∧ y ∘ Sum.inr ∈ D ∧
    ∀ i, valueCoordinate (y (.inl i)) = 1}

/-- Dividing by the monomial lift and multiplying back gives the
equivalence for an individual positive piece. -/
def affineRVChartEquiv
    (hLift : ∀ t : Fin m → RV0 O, (∀ j, IsPositiveRV O (t j)) →
      ∀ i, IsPositiveRV O (rvAffineMonomial O P coeff u t i)) :
    affineRVSource O P coords coeff u D ≃ affineRVTarget O (n := n) D := by
  let lift := rvAffineMonomial O P coeff u
  let f (x : affineRVSource O P coords coeff u D) :=
    affineChartTuple O P (coords ∘ Sum.inl) (coords ∘ Sum.inr) coeff u x.val
  let b (y : affineRVTarget O (n := n) D) : I → RV0 O :=
    Sum.elim (y.val ∘ Sum.inr)
      (fun i => y.val (.inl i) * lift (y.val ∘ Sum.inr) i) ∘ coords.symm
  have hLiftF (x : affineRVSource O P coords coeff u D) (i : Fin n) :
      IsPositiveRV O (lift (x.val ∘ coords ∘ Sum.inl) i) :=
    hLift _ (fun j => x.property.1 (coords (.inl j))) i
  have hLiftB (y : affineRVTarget O (n := n) D) (i : Fin n) :
      IsPositiveRV O (lift (y.val ∘ Sum.inr) i) :=
    hLift _ (fun j => y.property.1 (.inr j)) i
  have hb₁ (y : affineRVTarget O (n := n) D) : b y ∘ coords ∘ Sum.inl = y.val ∘ Sum.inr := by
    funext j
    simp only [b, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  have hb₂ (y : affineRVTarget O (n := n) D) (i : Fin n) :
      b y (coords (.inr i)) = y.val (.inl i) * lift (y.val ∘ Sum.inr) i := by
    simp only [b, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  refine
    { toFun := fun x => ⟨f x, ?_⟩
      invFun := fun y => ⟨b y, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨fun j => ?_, x.property.2.1, fun i => ?_⟩
    · cases j with
      | inl i => exact IsPositiveRV.div O (x.property.1 _) (hLiftF x i)
      | inr j => exact x.property.1 _
    · change valueCoordinate (x.val (coords (.inr i)) / lift (x.val ∘ coords ∘ Sum.inl) i) = 1
      rw [valueCoordinate_div O (IsPositiveRV.ne_zero O (x.property.1 _))
        (IsPositiveRV.ne_zero O (hLiftF x i)), x.property.2.2, div_self']
  · refine ⟨fun j => ?_, (hb₁ y).symm ▸ y.property.2.1, fun i => ?_⟩
    · obtain ⟨j, rfl⟩ := coords.surjective j
      cases j with
      | inl j =>
        rw [show b y (coords (.inl j)) = y.val (.inr j) from congrFun (hb₁ y) j]
        exact y.property.1 (.inr j)
      | inr i =>
        rw [hb₂]
        exact IsPositiveRV.mul O (y.property.1 (.inl i)) (hLiftB y i)
    · change valueCoordinate (b y (coords (.inr i))) =
        valueCoordinate (lift (b y ∘ coords ∘ Sum.inl) i)
      rw [hb₁, hb₂, valueCoordinate_mul (IsPositiveRV.ne_zero O (y.property.1 (.inl i)))
        (IsPositiveRV.ne_zero O (hLiftB y i)), y.property.2.2, one_mul]
  · intro x
    apply Subtype.ext
    funext j
    obtain ⟨j, rfl⟩ := coords.surjective j
    cases j with
    | inl j => simp only [b, f, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inl, affineChartTuple, Sum.elim_inr]
    | inr i =>
      simp only [b, f, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr,
        affineChartTuple, Sum.elim_inl]
      exact div_mul_cancel₀ (G₀ := RV0 O) _ (IsPositiveRV.ne_zero O (hLiftF x i))
  · intro y
    apply Subtype.ext
    funext j
    cases j with
    | inl i =>
      change b y (coords (.inr i)) / lift (b y ∘ coords ∘ Sum.inl) i = y.val (.inl i)
      rw [hb₂, hb₁, div_eq_mul_inv (G := RV0 O), mul_assoc (G := RV0 O),
        mul_inv_cancel₀ (G₀ := RV0 O) (IsPositiveRV.ne_zero O (hLiftB y i)), mul_one (M := RV0 O)]
    | inr j => exact congrFun (hb₁ y) j

/-- The affine chart is a definable bijection over the same base as the
source and the specified intercept representatives. -/
theorem affineRVChart_definablyEquivalent
    {L : Language.{u, v}} [L.Structure K] [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (A : ∀ s, Set (CanonicalSort O s)) (hu : ∀ i, u i ∈ A .rv)
    (hLift : ∀ t : Fin m → RV0 O, (∀ j, IsPositiveRV O (t j)) →
      ∀ i, IsPositiveRV O (rvAffineMonomial O P coeff u t i))
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      {x : ∀ s, RVVariables I s → CanonicalSort O s |
        x .rv ∈ affineRVSource O P coords coeff u D}) :
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO P) A
      (affineRVSource O P coords coeff u D) (affineRVTarget O (n := n) D) := by
  refine ⟨affineRVChartEquiv O P coords coeff u D hLift, ?_⟩
  exact definable_affineChartTuple_graph O hO P _ hD (coords ∘ Sum.inl) (coords ∘ Sum.inr)
    coeff (fun i => ⟨u i, hu i⟩)

end GeneralizedEuler.Section2
