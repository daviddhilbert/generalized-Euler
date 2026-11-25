module

public import Section2.ResidueTopology

/-! Normalization-independent Euler characteristic and the invariant
form of the finite-value classification in Theorem 2.31. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language.{u, v}} [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  {E : Type w} (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

/-- A definable residue normal form, together with the definable
identification with its RV source. -/
def IsResidueNormalForm {I J : Type} (U : Set (I → RV0 O)) (R : Set (J → Residue O)) : Prop :=
  (Set.univ : Set (Residue O)).Definable L R ∧
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      U (embeddedResidueSet O R)

/-- Two definable residue presentations of the same RV set are
definably equivalent in the residue language. -/
theorem residueNormalForms_definablyEquivalent {I J J' : Type} [Finite I] [Finite J] [Finite J']
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    {U : Set (I → RV0 O)} {R : Set (J → Residue O)} {S : Set (J' → Residue O)}
    (hR : IsResidueNormalForm (L := L) O hO power U R)
    (hS : IsResidueNormalForm (L := L) O hO power U S) :
    ResidueDefinablyEquivalent (L := L) O R S := by
  exact (rvDefinablyEquivalent_iff_residue O _ hA R S).mp (hR.2.symm.trans hS.2)

/-- Choose a residue normal form for a definable set with finite value
image. All choices give the same residue Euler characteristic. -/
def residueNormalFormOfFiniteValue {n : ℕ} (U : Set (Fin n → RV0 O))
    [Finite (Set.range (fun x : U => unsignedValue O ∘ x.val))]
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    (hU : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {x : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | x .rv ∈ U}) :
    {R : Set ((Fin n ⊕ Unit) → Residue O) // IsResidueNormalForm (L := L) O hO power U R} :=
  let he := exists_internal_residue_normalization O hO power U hA hU
  ⟨he.choose, he.choose_spec⟩

/-- The Euler characteristic of an RV set of finite value image is the
o-minimal Euler characteristic of a residue normal form. -/
def finiteValueRVEulerCharacteristic (χ : ∀ I : Type, Set (I → Residue O) → ℤ)
    {n : ℕ} (U : Set (Fin n → RV0 O))
    [Finite (Set.range (fun x : U => unsignedValue O ∘ x.val))]
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    (hU : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {x : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | x .rv ∈ U}) : ℤ :=
  χ (Fin n ⊕ Unit) (residueNormalFormOfFiniteValue O hO power U hA hU).val

theorem finiteValueRVEulerCharacteristic_eq_normalForm
    (χ : ∀ I : Type, Set (I → Residue O) → ℤ)
    (hχ : ∀ {I J : Type} [Finite I] [Finite J] {R : Set (I → Residue O)} {S : Set (J → Residue O)},
      (Set.univ : Set (Residue O)).Definable L R → (Set.univ : Set (Residue O)).Definable L S →
      ResidueDefinablyEquivalent (L := L) O R S → χ I R = χ J S)
    {n : ℕ} (U : Set (Fin n → RV0 O))
    [Finite (Set.range (fun x : U => unsignedValue O ∘ x.val))]
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    (hU : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {x : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | x .rv ∈ U})
    {J : Type} [Finite J] {R : Set (J → Residue O)}
    (hR : IsResidueNormalForm (L := L) O hO power U R) :
    finiteValueRVEulerCharacteristic O hO power χ U hA hU = χ J R := by
  let S := residueNormalFormOfFiniteValue O hO power U hA hU
  exact hχ S.property.1 hR.1 (residueNormalForms_definablyEquivalent O hO power hA S.property hR)

set_option linter.style.haveILetI false in
/-- Theorem 2.31. The cited o-minimal classification applies to residue
normal forms, and the cited weakly o-minimal dimension theorem transports
projection dimension along the definable normalization in RV. -/
theorem rvDefinablyEquivalent_iff_projectionDimension_euler
    (χ : ∀ I : Type, Set (I → Residue O) → ℤ)
    (hbook :
      letI := residueOrderTopology O hO
      ∀ {I J : Type} [Finite I] [Finite J] {R : Set (I → Residue O)} {S : Set (J → Residue O)},
      (Set.univ : Set (Residue O)).Definable L R → (Set.univ : Set (Residue O)).Definable L S →
      (ResidueDefinablyEquivalent (L := L) O R S ↔
        finiteTupleProjectionDimension R = finiteTupleProjectionDimension S ∧ χ I R = χ J S))
    (hRVdim :
      letI := rvOrderTopology O hO
      ∀ {I J : Type} [Finite I] [Finite J] {D : Set (I → RV0 O)} {F : Set (J → RV0 O)},
      RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ) D F →
        finiteTupleProjectionDimension D = finiteTupleProjectionDimension F)
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    {n m : ℕ} (U : Set (Fin n → RV0 O)) (V : Set (Fin m → RV0 O))
    [Finite (Set.range (fun x : U => unsignedValue O ∘ x.val))]
    [Finite (Set.range (fun x : V => unsignedValue O ∘ x.val))]
    (hU : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {x : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | x .rv ∈ U})
    (hV : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {x : ∀ s, RVVariables (Fin m) s → CanonicalSort O s | x .rv ∈ V}) :
    letI := rvOrderTopology O hO
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ) U V ↔
      projectionDimension U = projectionDimension V ∧
        finiteValueRVEulerCharacteristic O hO power χ U hA hU =
          finiteValueRVEulerCharacteristic O hO power χ V hA hV := by
  letI := rvOrderTopology O hO
  letI := residueOrderTopology O hO
  let R := residueNormalFormOfFiniteValue O hO power U hA hU
  let S := residueNormalFormOfFiniteValue O hO power V hA hV
  have hUd : projectionDimension U = finiteTupleProjectionDimension R.val :=
    (finiteTupleProjectionDimension_fin U).symm.trans
      ((hRVdim R.property.2).trans (embeddedResidueSet_projectionDimension O hO R.val))
  have hVd : projectionDimension V = finiteTupleProjectionDimension S.val :=
    (finiteTupleProjectionDimension_fin V).symm.trans
      ((hRVdim S.property.2).trans (embeddedResidueSet_projectionDimension O hO S.val))
  rw [hUd, hVd, finiteValueRVEulerCharacteristic, finiteValueRVEulerCharacteristic]
  exact rvDefinablyEquivalent_iff_of_residue_classification O hO power U V R.val S.val hA
    R.property.2 S.property.2 _ _ _ _ (hbook R.property.1 S.property.1)

end GeneralizedEuler.Section2
