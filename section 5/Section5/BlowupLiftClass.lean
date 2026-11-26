module

public import Section5.ElementaryStratumIsomorphisms
public import Section5.GradedBlowupCongruence

/-! Elementary blowups preserve positive VF classes. Hence the lift
homomorphism factors through the actual common-blowup congruence. -/

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
  [TopologicalSpace K]

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem elementary_lift_class_of_equiv {k m : ℕ} (U : RVObject 𝓜 S (k+1)) (j : Fin (k+1))
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv)
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite)
    (iso : MixedDefinablyEquivalent 𝓜 S (ObjectLift.carrier U)
      (elementaryLiftCarrier O hO power S U j)) :
    liftObjectClass ⟨k+1,U⟩ =
      liftObjectClass ⟨k,zeroBlowupObject U j finiteDelete⟩ +
        liftObjectClass ⟨k+1,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ := by
  obtain ⟨e,he⟩ := iso
  let Y := elementaryLiftCarrier O hO power S U j
  let C₀ := elementaryZeroStratum O hO power S U j
  let C₁ := elementaryNonzeroStratum O hO power S U j
  obtain ⟨def₁,iso₁⟩ := elementaryNonzeroStratum_definable_and_iso O hO power S U j finiteDelete idx hneg
  have def₀ := elementaryZeroStratum_definable O hO power S U j finiteDelete
  have iso₀ := elementaryZeroStratum_iso O hO power S U j finiteDelete
  let D₀ := {x | ∃ hx : x ∈ ObjectLift.carrier U, (e ⟨x,hx⟩).val ∈ C₀}
  let D₁ := {x | ∃ hx : x ∈ ObjectLift.carrier U, (e ⟨x,hx⟩).val ∈ C₁}
  obtain ⟨d₀,p₀⟩ := MixedDefinablyEquivalent.restrict_target e he C₀ (fun _ h => h.1) def₀
  obtain ⟨d₁,p₁⟩ := MixedDefinablyEquivalent.restrict_target e he C₁ (fun _ h => h.1) def₁
  have disj : Disjoint D₀ D₁ := by
    apply Set.disjoint_left.2
    rintro a ⟨ha,h₀⟩ ⟨ha',h₁⟩
    exact h₁.2 h₀.2
  have cover : D₀ ∪ D₁ = ObjectLift.carrier U := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (fun _ h => h.choose) (fun _ h => h.choose)
    · intro x hx
      let y := e ⟨x,hx⟩
      by_cases h : y.val .rv (.inr ()) = 0
      · exact Or.inl ⟨hx,y.property,h⟩
      · exact Or.inr ⟨hx,y.property,h⟩
  unfold liftObjectClass fieldClass
  rw [← map_add]
  exact field_scissors_sound 𝓜 S
    (.cut _ _ _ D₀ D₁ d₀ d₁ disj cover (p₀.trans iso₀) (p₁.trans iso₁))

/-- The elementarity and saturation assumptions here are exactly the
ones used to choose the relative focus in the elementary lift. -/
theorem elementary_lift_class {k m : ℕ} (U : RVObject 𝓜 S (k+1)) (j : Fin (k+1))
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv)
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
    liftObjectClass ⟨k+1,U⟩ =
      liftObjectClass ⟨k,zeroBlowupObject U j finiteDelete⟩ +
        liftObjectClass ⟨k+1,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ := by
  apply elementary_lift_class_of_equiv O hO power S U j idx hneg finiteDelete
  exact definable_elementary_lift_of_finite_projection O hO power S U j finiteDelete satRV sat elem F minusOne hm hF

variable (hneg : rv O (-1) ∈ S.carrier .rv)
  (liftIso : LiftsRVIsomorphisms (canonicalStructure (L := L) O hO power) S)

local notation "d" => gradedBlowupCongruence O hO power S hneg
local notation "lift" => liftClassHom liftIso
local notation "p" => residuePointClass O hO power S
local notation "q" => multiplierClass O hO power S hneg

theorem liftClassHom_point_blowup
    (satRV : ∀ D : ℕ → Set (Fin 0 → RV0 O), (∀ i, isRVSet 𝓜 S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables 0 Empty))
      (BaseAssignments S.carrier (MixedVariables 0 Empty)))
    (elem : ∀ a : fieldAssignment 0 (CanonicalSort O),
      let B := (canonicalStructure (L := L) O hO power).termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize 𝓜 (fun s i => (v s i).val))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    lift p = lift (1+q) := by
  let W := degreeZeroUnit 𝓜 S
  let nz := canonical_rvUnit_nonzero (L := L) O hO power
  let U := appendUnitLabel W nz
  let j := Fin.last 0
  let deletion := appendUnitLabel_finite_deletion W nz
  let idx : Fin (U.arity+1) ≃ Fin U.arity ⊕ Fin 1 := finSumFinEquiv.symm
  let Z := zeroBlowupObject U j deletion
  let P := positiveBlowupObject O hO power S U idx hneg j deletion
  have elementary := elementary_lift_class O hO power S U j idx hneg deletion satRV sat elem F minusOne hm hF
  obtain ⟨old,next⟩ := elementaryClassStep_center_realization O hO power S hneg ⟨0,W⟩
  change objectClass 𝓜 S ⟨1,U⟩ = objectClass 𝓜 S ⟨0,W⟩ * p at old
  change objectClass 𝓜 S ⟨0,Z⟩ + objectClass 𝓜 S ⟨1,P⟩ = objectClass 𝓜 S ⟨0,W⟩ * (1+q) at next
  rw [show objectClass 𝓜 S ⟨0,W⟩ = 1 from degreeZeroUnit_class 𝓜 S,one_mul] at old next
  rw [← old,← next,map_add]
  simpa only [liftClassHom_class] using elementary

/-- To factor the lift it is enough to check the actual blowup of the
degree-one point. The graded congruence is generated by this pair. -/
def quotientLiftClassHom (pointRelation : lift p = lift (1+q)) :
    (d).Quotient →+* VFSemiring 𝓜 S :=
  (d).lift lift (by
    rw [gradedBlowupCongruence_eq_generated]
    apply RingCon.ringConGen_le.mpr
    rintro _ _ ⟨rfl,rfl⟩
    exact pointRelation)

theorem quotientLiftClassHom_surjective (pointRelation : lift p = lift (1+q))
    (surj : Function.Surjective lift) :
    Function.Surjective (quotientLiftClassHom O hO power S hneg liftIso pointRelation) := by
  intro y
  obtain ⟨a,ha⟩ := surj y
  exact ⟨(d).mk' a,ha⟩

end GeneralizedEuler.Section5
