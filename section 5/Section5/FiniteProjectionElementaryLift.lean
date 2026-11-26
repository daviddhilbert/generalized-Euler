module

public import Section5.DefinableElementaryLift
public import Section5.DefinablePartitionBijection
public import Section4.LexicographicTags
import all Section4.FiniteScissors

/-! Partition an elementary blowup by the finite fibers of its retained
labels and glue the fixed-base lift bijections. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1)) (j : Fin (k+1))

private theorem carrier_restrict_iff {A : Set (Fin U.arity → RV0 O)}
    (sub : A ⊆ U.carrier) (hA : isRVSet 𝓜 S A)
    (x : SortedAssignment (CanonicalSort O) (ObjectLift.Vars U)) :
    x ∈ ObjectLift.carrier (U.restrict sub hA) ↔ x ∈ ObjectLift.carrier U ∧ x .rv ∈ A := by
  constructor
  · rintro ⟨a,ha,hx⟩
    exact ⟨⟨⟨a.val,sub a.property⟩,ha,hx⟩,ha ▸ a.property⟩
  · rintro ⟨⟨a,ha,hx⟩,h⟩
    exact ⟨⟨a.val,ha.symm ▸ h⟩,ha,hx⟩

private theorem elementary_restrict_iff {A : Set (Fin U.arity → RV0 O)}
    (sub : A ⊆ U.carrier) (hA : isRVSet 𝓜 S A)
    (x : SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U)) :
    x ∈ elementaryLiftCarrier O hO power S (U.restrict sub hA) j ↔
      x ∈ elementaryLiftCarrier O hO power S U j ∧ x .rv ∘ Sum.inl ∈ A := by
  constructor
  · rintro ⟨a,ha,hm,hx⟩
    refine ⟨⟨⟨a.val,sub a.property⟩,ha,hm,?_⟩,ha ▸ a.property⟩
    exact hx
  · rintro ⟨⟨a,ha,hm,hx⟩,h⟩
    refine ⟨⟨a.val,ha.symm ▸ h⟩,ha,hm,?_⟩
    exact hx

/-- A finite-to-one projection off the blown-up coordinate suffices for
the fixed-base bijection. The finite partition is taken in the fibers of
the structure map of the degree-lowered object. -/
theorem definable_elementary_lift_of_finite_projection
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite)
    (satRV : ∀ D : ℕ → Set (Fin k → RV0 O), (∀ i, isRVSet 𝓜 S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables k Empty))
      (BaseAssignments S.carrier (MixedVariables k Empty)))
    (elem : ∀ a : fieldAssignment k (CanonicalSort O),
      let B := (canonicalStructure (L := L) O hO power).termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize 𝓜 (fun s i => (v s i).val))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    ∃ e : ObjectLift.carrier U ≃ elementaryLiftCarrier O hO power S U j,
      DefinableRelation 𝓜 S.carrier (fun
        (a : SortedAssignment (CanonicalSort O) (ObjectLift.Vars U))
        (b : SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U)) =>
        ∃ ha : a ∈ ObjectLift.carrier U, (e ⟨a,ha⟩).val = b) := by
  classical
  let := rvLinearOrder O hO
  let lt (x y : Fin U.arity → RV0 O) := toLex x < toLex y
  have hlt : isRVSet 𝓜 S {t : Fin U.arity ⊕ Fin U.arity → RV0 O | lt (t ∘ Sum.inr) (t ∘ Sum.inl)} :=
    canonical_lex_definable O hO power S
  let Z := zeroBlowupObject U j finiteDelete
  obtain ⟨N,disj,cover⟩ := Z.tag_partition lt satRV
  let P (i : Fin N) := Z.tagPiece lt i.val
  have sub (i : Fin N) : P i ⊆ U.carrier := fun _ h => h.1
  have defP (i : Fin N) : isRVSet 𝓜 S (P i) := Z.tagPiece_definable lt hlt i.val
  let R (i : Fin N) := U.restrict (sub i) (defP i)
  have inj (i : Fin N) :
      Set.InjOn (projectLabels j.succAboveEmb) (ObjectLift.structureLabels (R i)) := by
    intro u hu v hv eq
    obtain ⟨a,rfl⟩ := hu
    obtain ⟨b,rfl⟩ := hv
    have e : a = b := Z.tagPiece_injective lt (fun h g => lt_trans h g)
      (fun _ => lt_irrefl _) (fun _ _ ne => lt_or_gt_of_ne (fun he => ne (toLex.injective he)))
      i.val (congrFun eq .rv)
    exact congrArg (rvTupleAssignment ∘ (R i).label) e
  have localBijection (i : Fin N) := definable_elementary_lift_of_injective_projection
    O hO power S (R i) j (inj i) sat elem F minusOne hm hF
  choose e _ graph using localBijection
  let D (i : Fin N) := ObjectLift.carrier (R i)
  let C (i : Fin N) := elementaryLiftCarrier O hO power S (R i) j
  have memD (i : Fin N) (x) : x ∈ D i ↔ x ∈ ObjectLift.carrier U ∧ x .rv ∈ P i :=
    carrier_restrict_iff O hO power S U (sub i) (defP i) x
  have memC (i : Fin N) (x) :
      x ∈ C i ↔ x ∈ elementaryLiftCarrier O hO power S U j ∧ x .rv ∘ Sum.inl ∈ P i :=
    elementary_restrict_iff O hO power S U j (sub i) (defP i) x
  apply definable_bijection_of_partitions D C
    (fun i x h => ((memD i x).1 h).1) (fun i x h => ((memC i x).1 h).1) ?_ ?_ ?_ ?_ e graph
  · intro i l ne
    exact Set.disjoint_left.2 fun x ha hb =>
      Set.disjoint_left.1 (disj ne) ((memD i x).1 ha).2 ((memD l x).1 hb).2
  · intro i l ne
    exact Set.disjoint_left.2 fun x ha hb =>
      Set.disjoint_left.1 (disj ne) ((memC i x).1 ha).2 ((memC l x).1 hb).2
  · intro x hx
    have old : x .rv ∈ U.carrier := by
      obtain ⟨a,he,_⟩ := hx
      exact he ▸ a.property
    obtain ⟨i,hi⟩ := Set.mem_iUnion.1 (cover.symm ▸ old : x .rv ∈ ⋃ i, P i)
    exact ⟨i,(memD i x).2 ⟨hx,hi⟩⟩
  · intro x hx
    have old : x .rv ∘ Sum.inl ∈ U.carrier := by
      obtain ⟨a,ha,_,_⟩ := hx
      exact ha ▸ a.property
    obtain ⟨i,hi⟩ := Set.mem_iUnion.1 (cover.symm ▸ old : x .rv ∘ Sum.inl ∈ ⋃ i, P i)
    exact ⟨i,(memC i x).2 ⟨hx,hi⟩⟩

end GeneralizedEuler.Section5
