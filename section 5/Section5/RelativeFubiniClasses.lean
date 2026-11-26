module

public import Section5.RelativeProjectionClasses

/-! The inner lift on each fixed-base projection and its outer class.
The fiber statement transports to the RV quotient along the integration
equivalence once that equivalence is available. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U : TCsort → Type}

structure GradedLiftCover (M : SortedStructure L E X) (S : SortedSubstructure M)
    (D : Set (SortedAssignment X P)) (A : Set (SortedAssignment X (SumVariables P U)))
    (zero : S.carrier .rv) where
  schemes : Finset (RelativeGradedLiftScheme M S P U)
  pieces : {i // i ∈ schemes} → Set (SortedAssignment X P)
  definable : ∀ i, SortedDefinableOver M S.carrier (pieces i)
  valid : ∀ i p, p ∈ pieces i → i.val.valid zero A p
  disjoint : Pairwise (fun i j => Disjoint (pieces i) (pieces j))
  covers : (⋃ i, pieces i) = D

theorem exists_graded_lift_cover [Finite (U .vf)] [Finite (U .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (D : Set (SortedAssignment X P)) (defD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (defA : SortedDefinableOver M S.carrier A)
    (zero : S.carrier .rv) (pointwise : ∀ p ∈ D, ∃ W : RelativeGradedLiftScheme M S P U, W.valid zero A p) :
    Nonempty (GradedLiftCover M S D A zero) := by
  obtain ⟨C,B,d,v,s,c⟩ := uniform_graded_relative_lift_schemes sat zero D defD A defA pointwise
  exact ⟨⟨C,B,d,v,s,c⟩⟩

section Projection

variable [TopologicalSpace (X .vf)] {q m b n b' n' : ℕ}

local notation "V" => MixedVariables q (Fin m)

/-- A retained projection can have size zero here. The same theorem
also applies when all field coordinates are retained. -/
theorem projection_fubini_field_classes
    (e : Fin (b+n) ≃ Fin q) (e' : Fin (b'+n') ≃ Fin q)
    (A : Set (SortedAssignment X V)) (defA : SortedDefinableOver M S.carrier A)
    (finite : ∀ x : Fin q → X .vf, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (zero : S.carrier .rv)
    (C : GradedLiftCover M S (fieldProjection (splitFieldSpace e A)) (splitFieldSpace e A) zero)
    (C' : GradedLiftCover M S (fieldProjection (splitFieldSpace e' A)) (splitFieldSpace e' A) zero) :
    let I := Σ i : {i // i ∈ C.schemes}, Fin i.val.count
    let J := Σ j : {j // j ∈ C'.schemes}, Fin j.val.count
    let R (i : I) := onlyOver (C.pieces i.1) (relativeRVLift (M := M) (i.1.val.object i.2).labelGraph)
    let R' (j : J) := onlyOver (C'.pieces j.1) (relativeRVLift (M := M) (j.1.val.object j.2).labelGraph)
    ∃ (B : I → VFObject M S) (B' : J → VFObject M S),
      (∀ i, MixedDefinablyEquivalent M S (R i) (B i).2.carrier) ∧
      (∀ j, MixedDefinablyEquivalent M S (R' j) (B' j).2.carrier) ∧
      (∑ i, fieldClass M S (B i)) = ∑ j, fieldClass M S (B' j) := by
  intro I J R R'
  obtain ⟨B,g,eq⟩ := uniform_projection_total_class e A defA finite zero C.schemes C.pieces
    C.definable C.valid C.disjoint C.covers
  obtain ⟨B',g',eq'⟩ := uniform_projection_total_class e' A defA finite zero C'.schemes C'.pieces
    C'.definable C'.valid C'.disjoint C'.covers
  exact ⟨B,B',g,g',eq.symm.trans eq'⟩

end Projection

section Inner

variable [TopologicalSpace (X .vf)] {n m : ℕ}

theorem RelativeGradedLiftScheme.fiber_class_under_integration_equiv
    (W : RelativeGradedLiftScheme M S P (MixedVariables n (Fin m)))
    (A : Set (SortedAssignment X (SumVariables P (MixedVariables n (Fin m)))))
    (defA : SortedDefinableOver M S.carrier A)
    (p : SortedAssignment X P) (zero : S.carrier .rv)
    (hzero : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (valid : W.valid zero A p)
    (finite : ∀ x : Fin n → X .vf,
      {r | (x,r) ∈ mixedTuple '' {a : SortedAssignment X (MixedVariables n (Fin m)) | appendAssignments p a ∈ A}}.Finite)
    {R : Type*} [CommSemiring R] :
    let T := M.termGenerated (namedTuple S p)
    ∀ (q : RVSemiring M T →+* R) (e : R ≃+* VFSemiring M T),
      (∀ B : GradedObject M T, e (q (objectClass M T B)) = liftObjectClass B) →
      ∃ B : ∀ i : Fin W.count, RVObject M T (W.object i).degree,
        (∀ i, (B i).arity = (W.object i).arity) ∧
        (∀ i, MixedDefinablyEquivalent M T {u | appendAssignments p u ∈ W.source i} (ObjectLift.carrier (B i))) ∧
        (∑ i, q (objectClass M T ⟨(W.object i).degree,B i⟩)) =
          e.symm (fieldClass M T (mixedFieldObject T _ (definable_scheme_at_fiber p A defA) finite)) := by
  intro T q e commutes
  obtain ⟨B,arity,iso,eq⟩ := W.fiber_class_eq_sum A defA p zero hzero valid finite
  refine ⟨B,arity,iso,e.injective ?_⟩
  rw [e.apply_symm_apply,map_sum,eq]
  exact Finset.sum_congr rfl fun i _ => commutes ⟨_,B i⟩

end Inner

end GeneralizedEuler.Section5
