module

public import Section5.LabelProjection
public import Section2.WeakOminimal
public import Mathlib.Topology.Homeomorph.Lemmas
import all Section2.WeakOminimal

/-! The dimension-zero case of Lemma 5.12 reduces to finite RV sets. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

private theorem finite_of_emptyInterior_of_finiteConvexUnion {Y : Type*}
    [LinearOrder Y] [DenselyOrdered Y] [TopologicalSpace Y] [OrderTopology Y]
    {C : Set Y} (hC : FiniteConvexUnion C) (h : interior C = ∅) : C.Finite := by
  obtain ⟨m,P,hP,hUnion⟩ := hC
  have hp (i : Fin m) : (P i).Subsingleton := by
    have notLess : ∀ x ∈ P i, ∀ y ∈ P i, ¬ x < y := by
      intro x hx y hy hxy
      obtain ⟨t,ht⟩ := exists_between hxy
      have sub : Set.Ioo x y ⊆ C := by
        intro w hw
        rw [hUnion]
        exact Set.mem_iUnion.mpr ⟨i,(hP i).out hx hy ⟨hw.1.le,hw.2.le⟩⟩
      have hm := (interior_maximal sub isOpen_Ioo) ht
      simp only [h,Set.mem_empty_iff_false] at hm
    intro x hx y hy
    exact le_antisymm (le_of_not_gt (notLess y hy x hx)) (le_of_not_gt (notLess x hx y hy))
  rw [hUnion]
  exact Set.finite_iUnion (fun i => (hp i).finite)

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {n : ℕ}
  [LinearOrder (X .rv)] [DenselyOrdered (X .rv)]
  [TopologicalSpace (X .rv)] [OrderTopology (X .rv)]

/-- In a weakly o-minimal RV sort, the coordinate images of a
zero-dimensional definable set are finite. Their product is finite. -/
theorem finite_of_labelProjectionDimension_le_zero
    (tame : ∀ B : Set (X .rv),
      SortedDefinableOver M S.carrier {b : labelAssignment 1 X | b .rv 0 ∈ B} →
      FiniteConvexUnion B)
    {A : Set (labelAssignment n X)} (hA : SortedDefinableOver M S.carrier A)
    (hDim : labelProjectionDimension A ≤ 0) : A.Finite := by
  let T : Set (Fin n → X .rv) := rvTupleAssignment ⁻¹' A
  have cover : A ⊆ rvTupleAssignment '' T := by
    intro a ha
    have he : rvTupleAssignment (a .rv) = a := by
      funext s j
      cases s with
      | vf => exact j.elim
      | rv => rfl
    exact ⟨a .rv,he.symm ▸ ha,he⟩
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ((Set.finite_empty : (∅ : Set (Fin n → X .rv)).Finite).image _).subset
      (hT ▸ cover)
  have hD : projectionDimension T = 0 := by
    change projectionDimensionWithBot T ≤ 0 at hDim
    rw [projectionDimensionWithBot, dimensionWithBot_of_nonempty hT] at hDim
    exact Nat.eq_zero_of_le_zero (WithBot.coe_le_coe.mp hDim)
  let B (i : Fin n) : Set (X .rv) := (fun x : Fin n → X .rv => x i) '' T
  have hBDef (i : Fin n) :
      SortedDefinableOver M S.carrier {b : labelAssignment 1 X | b .rv 0 ∈ B i} := by
    let p : Fin 1 → Fin n := fun _ => i
    have defn := projectLabels_image_definable p hA
    convert defn using 1
    ext b
    constructor
    · rintro ⟨t,ht,he⟩
      refine ⟨rvTupleAssignment t,ht,?_⟩
      funext s j
      cases s with
      | vf => exact j.elim
      | rv =>
        have hj : j = 0 := Subsingleton.elim _ _
        exact hj.symm ▸ he
    · rintro ⟨a,ha,he⟩
      have hEq : rvTupleAssignment (a .rv) = a := by
        funext s j
        cases s with
        | vf => exact j.elim
        | rv => rfl
      exact ⟨a .rv,hEq.symm ▸ ha,congrFun (congrFun he .rv) 0⟩
  have emptyInterior (i : Fin n) : interior (B i) = ∅ := by
    let p : Fin 1 ↪ Fin n := ⟨fun _ => i,fun _ _ _ => Subsingleton.elim _ _⟩
    let ev := Homeomorph.funUnique (Fin 1) (X .rv)
    have he : ev '' (coordinateProjection p '' T) = B i := by
      rw [Set.image_image]
      rfl
    have h : interior (coordinateProjection p '' T) = ∅ := by
      by_contra hn
      exact (Nat.not_succ_le_zero 0) ((le_projectionDimension ⟨p,Set.nonempty_iff_ne_empty.2 hn⟩).trans
        (le_of_eq hD))
    rw [← he, ← ev.image_interior, h, Set.image_empty]
  have hFinite (i : Fin n) : (B i).Finite :=
    finite_of_emptyInterior_of_finiteConvexUnion (tame _ (hBDef i)) (emptyInterior i)
  have hProd : T ⊆ Set.pi Set.univ B := fun x hx i _ => ⟨x,hx,rfl⟩
  exact (((Set.Finite.pi hFinite).subset hProd).image rvTupleAssignment).subset cover

end GeneralizedEuler.Section5
