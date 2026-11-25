module

public import Section3.Contraction
public import Section2.WeakOminimal
import all Section2.WeakOminimal

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2

variable {X I : Type*} [LinearOrder X]

/-- The members of a disjoint convex family cut by a unary set. -/
@[expose]
def cutLabels (D : I → Set X) (A : Set X) : Set I :=
  {i | (D i ∩ A).Nonempty ∧ (D i \ A).Nonempty}

private theorem one_right_cut (D : I → Set X) (hD : ∀ i, (D i).OrdConnected)
    (hd : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (A : Set X) (hA : A.OrdConnected) :
    {i | ∃ x ∈ D i ∩ A, ∃ y ∈ D i \ A, x ≤ y}.Subsingleton := by
  rintro i ⟨x, ⟨hx, hxa⟩, y, ⟨hy, hya⟩, hxy⟩ j ⟨z, ⟨hz, hza⟩, w, ⟨hw, hwa⟩, hzw⟩
  by_contra hij
  rcases le_total x z with hxz | hzx
  · by_cases hyz : y ≤ z
    · exact hya (hA.out hxa hza ⟨hxy, hyz⟩)
    · exact Set.disjoint_left.mp (hd i j hij) ((hD i).out hx hy ⟨hxz, le_of_not_ge hyz⟩) hz
  · by_cases hwx : w ≤ x
    · exact hwa (hA.out hza hxa ⟨hzw, hwx⟩)
    · exact Set.disjoint_left.mp (hd i j hij) hx ((hD j).out hz hw ⟨hzx, le_of_not_ge hwx⟩)

/-- Each convex component can cut at most one member on either side. -/
theorem finite_cutLabels_of_ordConnected (D : I → Set X) (hD : ∀ i, (D i).OrdConnected)
    (hd : ∀ i j, i ≠ j → Disjoint (D i) (D j)) {A : Set X} (hA : A.OrdConnected) :
    (cutLabels D A).Finite := by
  have hR := one_right_cut D hD hd A hA
  have hL := one_right_cut (X := Xᵒᵈ) D (fun i => (hD i).dual) hd A hA.dual
  apply (hR.finite.union hL.finite).subset
  rintro i ⟨⟨x, hx⟩, y, hy⟩
  exact (le_total x y).imp (fun h => ⟨x, hx, y, hy, h⟩) (fun h => ⟨x, hx, y, hy, h⟩)

/-- The HNF counting argument used in 3.9, 3.22 and the unary case of 3.26. -/
theorem finite_cutLabels (D : I → Set X) (hD : ∀ i, (D i).OrdConnected)
    (hd : ∀ i j, i ≠ j → Disjoint (D i) (D j)) {A : Set X} (hA : FiniteConvexUnion A) :
    (cutLabels D A).Finite := by
  obtain ⟨n, C, hc, rfl⟩ := hA
  apply (Set.finite_iUnion (fun j => finite_cutLabels_of_ordConnected D hD hd (hc j))).subset
  rintro i ⟨⟨x, hxi, hx⟩, y, hyi, hy⟩
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨j, ⟨x, hxi, hxj⟩, y, hyi, fun hyj => hy (Set.mem_iUnion.mpr ⟨j, hyj⟩)⟩

/-- In dimension one the boundary consists of finitely many actual RV labels,
including the radius-zero coordinate convention. -/
theorem finite_unary_rvBoundary {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) (hO : IsOrderConvex O) {A : Set K} (hA : FiniteConvexUnion A) :
    (rvBoundary (rv O) A).Finite := by
  let D (t : RV0 O) := rv O ⁻¹' {t}
  have hd (i j : RV0 O) (h : i ≠ j) : Disjoint (D i) (D j) :=
    Set.disjoint_left.mpr (fun _ hi hj => h (hi.symm.trans hj))
  apply (finite_cutLabels D (rv_fiber_ordConnected O hO) hd hA).subset
  rintro i ⟨⟨x, hx, rfl⟩, y, hy, hy'⟩
  exact ⟨⟨x, rfl, hx⟩, y, hy, hy'⟩

end GeneralizedEuler.Section3
