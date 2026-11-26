module

public import Section5.RelativeFiberClasses
public import Section5.GradedLiftTotalBijections

/-! For a field parameter tuple, the original total space and the
uniform relative lift have the same class in the filtered VF semiring. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {b n m : ℕ} [TopologicalSpace (X .vf)]

local notation "P" => MixedVariables b Empty
local notation "U" => MixedVariables n (Fin m)

@[expose] def totalCoordinates :
    (s : TCsort) → MixedVariables (b+n) (Fin m) s ≃ SumVariables P U s
  | .vf => finSumFinEquiv.symm
  | .rv => (Equiv.emptySum Empty (Fin m)).symm

@[expose] def totalMixedSet (A : Set (SortedAssignment X (SumVariables P U))) :
    Set (SortedAssignment X (MixedVariables (b+n) (Fin m))) :=
  {x | (fun s => x s ∘ (totalCoordinates s).symm) ∈ A}

omit [TopologicalSpace (X .vf)] in
theorem totalMixedSet_definable {A : Set (SortedAssignment X (SumVariables P U))}
    (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier (totalMixedSet A) :=
  defA.pullback_relabel (fun s => (totalCoordinates s).symm)

omit [TopologicalSpace (X .vf)] in
theorem totalMixedSet_finite
    {D : Set (SortedAssignment X P)} {A : Set (SortedAssignment X (SumVariables P U))}
    (finiteFibers : ∀ p ∈ D, ∀ x : Fin n → X .vf,
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment X U | appendAssignments p u ∈ A}}.Finite)
    (x : Fin (b+n) → X .vf) :
    {r | (x,r) ∈ mixedTuple '' totalMixedSet (onlyOver D A)}.Finite := by
  classical
  let p : SortedAssignment X P := fieldTupleAssignment (x ∘ finSumFinEquiv ∘ Sum.inl)
  let y : Fin n → X .vf := x ∘ finSumFinEquiv ∘ Sum.inr
  by_cases hp : p ∈ D
  · apply (finiteFibers p hp y).subset
    rintro r ⟨w,hw,e⟩
    have hx : w .vf = x := congrArg Prod.fst e
    have hr : w .rv = r := congrArg Prod.snd e
    let u : SortedAssignment X U := fun | .vf => y | .rv => r
    refine ⟨u,?_ ,rfl⟩
    have eq : appendAssignments p u = fun s => w s ∘ (totalCoordinates s).symm := by
      funext s i
      cases s with
      | vf =>
        change Sum.elim (x ∘ finSumFinEquiv ∘ Sum.inl) y i = (w .vf ∘ finSumFinEquiv) i
        rw [hx]
        cases i <;> rfl
      | rv =>
        rcases i with i | i
        · exact i.elim
        · exact (congrFun hr i).symm
    change appendAssignments p u ∈ A
    rw [eq]
    exact hw.1
  · apply Set.finite_empty.subset
    rintro r ⟨w,hw,e⟩
    have hx : w .vf = x := congrArg Prod.fst e
    have eq : (fun s => w s ∘ (totalCoordinates s).symm ∘ Sum.inl) = p := by
      funext s i
      cases s
      · exact congrFun hx (finSumFinEquiv (.inl i))
      · exact i.elim
    exact (hp (eq ▸ hw.2)).elim

theorem uniform_graded_total_class
    (D : Set (SortedAssignment X P)) (defD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (defA : SortedDefinableOver M S.carrier A)
    (finiteFibers : ∀ p ∈ D, ∀ x : Fin n → X .vf,
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment X U | appendAssignments p u ∈ A}}.Finite)
    (zero : S.carrier .rv) (C : Finset (RelativeGradedLiftScheme M S P U))
    (pieces : {i // i ∈ C} → Set (SortedAssignment X P))
    (defPieces : ∀ i, SortedDefinableOver M S.carrier (pieces i))
    (valid : ∀ i p, p ∈ pieces i → i.val.valid zero A p)
    (disj : Pairwise (fun i j => Disjoint (pieces i) (pieces j))) (cover : (⋃ i, pieces i) = D) :
    let I := Σ i : {i // i ∈ C}, Fin i.val.count
    let R (i : I) := onlyOver (pieces i.1) (relativeRVLift (M := M) (i.1.val.object i.2).labelGraph)
    ∃ B : I → VFObject M S,
      (∀ i, MixedDefinablyEquivalent M S (R i) (B i).2.carrier) ∧
      fieldClass M S (mixedFieldObject S (totalMixedSet (onlyOver D A))
        (totalMixedSet_definable (onlyOver_definable defD defA)) (totalMixedSet_finite finiteFibers)) =
        ∑ i, fieldClass M S (B i) := by
  classical
  intro I R
  let L (i : I) := onlyOver (pieces i.1) (i.1.val.source i.2)
  obtain ⟨disjL,coverL,glue⟩ := uniform_graded_lift_total_bijections D A zero C pieces defPieces valid disj cover
  let A₀ := mixedFieldObject S (totalMixedSet (onlyOver D A))
    (totalMixedSet_definable (onlyOver_definable defD defA)) (totalMixedSet_finite finiteFibers)
  let F (i : I) := totalMixedSet (L i)
  have defF (i : I) : SortedDefinableOver M S.carrier (F i) := totalMixedSet_definable (glue i).1
  have sub (i : I) : F i ⊆ A₀.2.carrier := by
    intro x hx
    change (fun s => x s ∘ (totalCoordinates s).symm) ∈ onlyOver D A
    rw [← coverL]
    exact Set.mem_iUnion.2 ⟨i,hx⟩
  have disjF : Pairwise (fun i j => Disjoint (F i) (F j)) :=
    fun _ _ ne => Set.disjoint_left.2 (fun _ hi hj => Set.disjoint_left.1 (disjL ne) hi hj)
  have coverF : (⋃ i, F i) = A₀.2.carrier := by
    ext x
    rw [Set.mem_iUnion]
    change (∃ i, (fun s => x s ∘ (totalCoordinates s).symm) ∈ L i) ↔
      (fun s => x s ∘ (totalCoordinates s).symm) ∈ onlyOver D A
    rw [← Set.mem_iUnion,coverL]
  let W (i : I) := i.1.val.object i.2
  have rfinite (i : I) (p : SortedAssignment X P) (hp : p ∈ pieces i.1)
      (x : Fin (W i).degree → X .vf) :
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment X (MixedVariables (W i).degree (Fin (W i).arity)) |
        appendAssignments p u ∈ relativeRVLift (M := M) (W i).labelGraph}}.Finite := by
    have h := ((valid i.1 p hp).2.2 i.2).1
    apply (relativeRVLift_finite_fibers (M := M) h x).subset
    rintro r ⟨u,hu,eq⟩
    have hf : u .vf = x := congrArg Prod.fst eq
    have hr : u .rv = r := congrArg Prod.snd eq
    let a : SortedAssignment X (MixedVariables (W i).degree (Fin (W i).arity)) :=
      fun | .vf => x | .rv => r
    have e : a = u := by
      funext s
      cases s
      · exact hf.symm
      · exact hr.symm
    change appendAssignments p a ∈ relativeRVLift (M := M) (W i).labelGraph
    rwa [e]
  let B (i : I) := mixedFieldObject S (totalMixedSet (R i))
    (totalMixedSet_definable (glue i).2.1) (totalMixedSet_finite (rfinite i))
  have isoR (i : I) : MixedDefinablyEquivalent M S (R i) (B i).2.carrier :=
    mixed_reindex_equivalent totalCoordinates (R i) (glue i).2.1
  let e := (Fintype.equivFin I).symm
  have reindexedCover : (⋃ j, F (e j)) = A₀.2.carrier := by
    simpa only [e.surjective.iUnion_comp] using coverF
  have part := fieldClass_partition A₀ (fun j => F (e j)) (fun j => defF (e j)) (fun j => sub (e j))
    (fun _ _ ne => disjF (fun eq => ne (e.injective eq))) reindexedCover
  refine ⟨B,isoR,part.trans ?_⟩
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  let i := e j
  have isoL : MixedDefinablyEquivalent M S (L i) (F i) :=
    mixed_reindex_equivalent totalCoordinates (L i) (glue i).1
  obtain ⟨e,_,graph⟩ := (glue i).2.2
  have toR : MixedDefinablyEquivalent M S (L i) (R i) := ⟨e,graph⟩
  exact fieldClass_of_iso M S (A := restrictedFieldObject A₀ (F i) (sub i) (defF i))
    (B := B i) (isoL.symm.trans (toR.trans (isoR i)))

end GeneralizedEuler.Section5
