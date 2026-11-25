module

public import Section3.PartialDerivatives
public import Section3.Orientation
public import Mathlib.Topology.GDelta.Basic

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

/-- The slice exceptions of 3.31 give a nowhere dense set of labels.
The two tameness inputs are the boundary theorem 3.26 and preservation
of dimension under closure for the definable RV-interior in this chart. -/
theorem nowhereDense_exceptional_image {X Y U R : Type*} [TopologicalSpace U]
    [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    [TopologicalSpace R] [OrderTopology R] (p : X → U) (q : Y → R)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (bad : X → Set R)
    (hf : ∀ x, (bad x).Finite) :
    let S := {z : X × Y | q z.2 ∈ bad z.1}
    IsNowhereDense (rvBoundary (Prod.map p q) S) →
    (interior (rvInterior (Prod.map p q) S) = ∅ → IsNowhereDense (rvInterior (Prod.map p q) S)) →
    IsNowhereDense (Prod.map p q '' S) := by
  intro S hboundary hclosure
  rw [image_eq_interior_union_boundary]
  apply IsNowhereDense.union _ hboundary
  apply hclosure
  apply empty_interior_of_finite_last_fibers
  intro u
  obtain ⟨x,rfl⟩ := hp u
  exact finite_interior_fiber p q bad hq x (hf x)

/-- A single open domain for all the adjacent partials. The exceptional
set is measured in the ambient residue coordinates, even for arity zero. -/
theorem common_open_good_labels {R I : Type*} [TopologicalSpace R] [Finite I] {n : ℕ}
    {A W : Set (Fin n → R)} (hW : IsOpen W) (hWA : W ⊆ A)
    (hfirst : IsNowhereDense (A \ W)) (bad : I → Set (Fin n → R))
    (hb : ∀ i, IsNowhereDense (bad i)) :
    ∃ U, IsOpen U ∧ U ⊆ A ∧ projectionDimensionWithBot (A \ U) < (n : WithBot ℕ) ∧
      U ⊆ W ∧ ∀ i, Disjoint U (bad i) := by
  let E := closure (⋃ i, bad i)
  let U := W \ E
  have he : IsNowhereDense E := (IsNowhereDense.iUnion hb).closure
  have hsub : A \ U ⊆ (A \ W) ∪ E := by
    intro a ha
    by_cases hw : a ∈ W
    · exact Or.inr (not_not.mp (fun h => ha.2 ⟨hw,h⟩))
    · exact Or.inl ⟨ha.1,hw⟩
  have hthin := (hfirst.union he).mono hsub
  refine ⟨U,hW.sdiff isClosed_closure,fun _ hx => hWA hx.1,
    dimensionWithBot_lt_arity_iff.mpr ?_,fun _ hx => hx.1,?_⟩
  · exact eq_empty_of_subset_empty ((interior_mono subset_closure).trans hthin.subset)
  · intro i
    exact disjoint_left.mpr (fun x hx hi => hx.2 (subset_closure (mem_iUnion_of_mem i hi)))

/-- Corollary 3.33 after applying the residue orientation theorem.
Singular labels and the exceptions for the first partials are discarded
once, and every representative over each surviving label has the sign. -/
theorem constant_sign_off_exceptional_labels {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)
    {R X : Type*} [TopologicalSpace R] {n : ℕ} (label : X → Fin n → R)
    (U singular exceptions : Set (Fin n → R)) (hs : IsNowhereDense singular)
    (he : IsNowhereDense exceptions) (J : X → Matrix (Fin n) (Fin n) O)
    (reduced : (Fin n → R) → Matrix (Fin n) (Fin n) (Residue O)) :
    letI := residueLinearOrder O hO
    (∀ x, label x ∈ U → label x ∉ exceptions → ∀ i j,
      IsLocalRing.residue O (J x i j) = reduced (label x) i j) →
    ((∀ t ∈ U \ singular, 0 < (reduced t).det) ∨ (∀ t ∈ U \ singular, (reduced t).det < 0)) →
    ∃ E ⊆ U, projectionDimensionWithBot E < (n : WithBot ℕ) ∧
      ((∀ x, label x ∈ U \ E → 0 < ((J x).det : K)) ∨
       (∀ x, label x ∈ U \ E → ((J x).det : K) < 0)) := by
  let := residueLinearOrder O hO
  intro hJ horient
  let E := U ∩ (singular ∪ exceptions)
  have hE := (hs.union he).mono (inter_subset_right (s := U))
  have good {t} (h : t ∈ U \ E) : t ∈ U \ singular ∧ t ∉ exceptions :=
    ⟨⟨h.1,fun hs => h.2 ⟨h.1,Or.inl hs⟩⟩,fun he => h.2 ⟨h.1,Or.inr he⟩⟩
  refine ⟨E,inter_subset_left,dimensionWithBot_lt_arity_iff.mpr ?_,?_⟩
  · exact eq_empty_of_subset_empty ((interior_mono subset_closure).trans hE.subset)
  · rcases horient with hp | hn
    · left
      intro x hx
      have h := hp _ (good hx).1
      exact (jacobian_sign_of_residue O hO _ _ (hJ x hx.1 (good hx).2) h.ne').1.mpr h
    · right
      intro x hx
      have h := hn _ (good hx).1
      exact (jacobian_sign_of_residue O hO _ _ (hJ x hx.1 (good hx).2) h.ne).2.mpr h

end GeneralizedEuler.Section3
