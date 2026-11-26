module

public import Section5.RelativeTotalClasses

/-! Retain any field subtuple. Reindexing back to the original field
coordinates identifies the total class with the sum for the inner lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {b n q m : ℕ}

local notation "P" => MixedVariables b Empty
local notation "U" => MixedVariables n (Fin m)
local notation "V" => MixedVariables q (Fin m)

@[expose] def splitFieldCoordinates (e : Fin (b+n) ≃ Fin q) : (s : TCsort) → V s → SumVariables P U s
  | .vf => finSumFinEquiv.symm ∘ e.symm
  | .rv => Sum.inr

@[expose] def splitFieldSpace (e : Fin (b+n) ≃ Fin q) (A : Set (SortedAssignment X V)) :
    Set (SortedAssignment X (SumVariables P U)) :=
  {x | (fun s => x s ∘ splitFieldCoordinates e s) ∈ A}

theorem splitFieldSpace_definable (e : Fin (b+n) ≃ Fin q)
    {A : Set (SortedAssignment X V)} (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier (splitFieldSpace e A) :=
  defA.pullback_relabel (splitFieldCoordinates e)

@[expose] def fieldProjection (A : Set (SortedAssignment X (SumVariables P U))) :
    Set (SortedAssignment X P) := {p | ∃ u : SortedAssignment X U, appendAssignments p u ∈ A}

theorem fieldProjection_definable {A : Set (SortedAssignment X (SumVariables P U))}
    (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier (fieldProjection A) :=
  definable_project_mixed defA

theorem onlyOver_fieldProjection (A : Set (SortedAssignment X (SumVariables P U))) :
    onlyOver (fieldProjection A) A = A := by
  ext a
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha,fun s => a s ∘ Sum.inr,?_⟩
    convert ha using 1
    funext s i
    cases i <;> rfl

theorem splitFieldSpace_finite_fibers (e : Fin (b+n) ≃ Fin q)
    {A : Set (SortedAssignment X V)}
    (finite : ∀ x : Fin q → X .vf, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (p : SortedAssignment X P) (x : Fin n → X .vf) :
    {r | (x,r) ∈ mixedTuple '' {a : SortedAssignment X U | appendAssignments p a ∈ splitFieldSpace e A}}.Finite := by
  let y : Fin q → X .vf := Sum.elim (p .vf) x ∘ finSumFinEquiv.symm ∘ e.symm
  apply (finite y).subset
  rintro r ⟨a,mem,eq⟩
  let a' : SortedAssignment X V := fun s => appendAssignments p a s ∘ splitFieldCoordinates e s
  have h₁ : a .vf = x := congrArg Prod.fst eq
  have h₂ : a .rv = r := congrArg Prod.snd eq
  refine ⟨a',mem,Prod.ext ?_ h₂⟩
  change Sum.elim (p .vf) (a .vf) ∘ finSumFinEquiv.symm ∘ e.symm = y
  rw [h₁]

theorem splitFieldSpace_total_iso (e : Fin (b+n) ≃ Fin q)
    {A : Set (SortedAssignment X V)} (defA : SortedDefinableOver M S.carrier A) :
    MixedDefinablyEquivalent M S A
      (totalMixedSet (onlyOver (fieldProjection (splitFieldSpace e A)) (splitFieldSpace e A))) := by
  let rename : (s : TCsort) → MixedVariables (b+n) (Fin m) s ≃ V s
    | .vf => e
    | .rv => Equiv.refl _
  have iso := mixed_reindex_equivalent rename A defA
  rw [onlyOver_fieldProjection]
  have eq : totalMixedSet (splitFieldSpace e A) =
      {y : SortedAssignment X (MixedVariables (b+n) (Fin m)) | (fun s => y s ∘ (rename s).symm) ∈ A} := by
    ext y
    have eval : (fun s => y s ∘ (totalCoordinates s).symm ∘ splitFieldCoordinates e s) =
        (fun s => y s ∘ (rename s).symm) := by
      funext s i
      cases s with
      | vf => exact congrArg (y .vf) (finSumFinEquiv.apply_symm_apply (e.symm i))
      | rv => rfl
    change (fun s => y s ∘ (totalCoordinates s).symm ∘ splitFieldCoordinates e s) ∈ A ↔
      (fun s => y s ∘ (rename s).symm) ∈ A
    rw [eval]
  rw [eq]
  exact iso

variable [TopologicalSpace (X .vf)]

theorem uniform_projection_total_class (e : Fin (b+n) ≃ Fin q)
    (A : Set (SortedAssignment X V)) (defA : SortedDefinableOver M S.carrier A)
    (finite : ∀ x : Fin q → X .vf, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (zero : S.carrier .rv) (C : Finset (RelativeGradedLiftScheme M S P U))
    (pieces : {i // i ∈ C} → Set (SortedAssignment X P))
    (defPieces : ∀ i, SortedDefinableOver M S.carrier (pieces i))
    (valid : ∀ i p, p ∈ pieces i → i.val.valid zero (splitFieldSpace e A) p)
    (disj : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (cover : (⋃ i, pieces i) = fieldProjection (splitFieldSpace e A)) :
    let I := Σ i : {i // i ∈ C}, Fin i.val.count
    let R (i : I) := onlyOver (pieces i.1) (relativeRVLift (M := M) (i.1.val.object i.2).labelGraph)
    ∃ objects : I → VFObject M S,
      (∀ i, MixedDefinablyEquivalent M S (R i) (objects i).2.carrier) ∧
      fieldClass M S (mixedFieldObject S A defA finite) = ∑ i, fieldClass M S (objects i) := by
  classical
  intro I R
  let B := splitFieldSpace e A
  let D := fieldProjection B
  have defB := splitFieldSpace_definable e defA
  have defD := fieldProjection_definable defB
  have bounded (p : SortedAssignment X P) (_ : p ∈ D) (x : Fin n → X .vf) :
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment X U | appendAssignments p u ∈ B}}.Finite :=
    splitFieldSpace_finite_fibers e finite p x
  obtain ⟨objects,isoR,eq⟩ := uniform_graded_total_class D defD B defB bounded zero C pieces defPieces valid disj cover
  refine ⟨objects,isoR,?_⟩
  exact (fieldClass_of_iso M S (splitFieldSpace_total_iso e defA)).trans eq

end GeneralizedEuler.Section5
