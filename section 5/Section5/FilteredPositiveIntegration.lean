module

public import Section5.IntegrationIsomorphism
public import Section5.LiftDimensionFiltration

/-! The positive integration isomorphism restricts to each
dimension filtration. Empty summands contribute the zero class. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Q" => (gradedBlowupCongruence O hO power S neg)
local notation "Z" => CanonicalSort O

def rvDegreeAtMost (k : ℕ) : AddSubmonoid (RVSemiring 𝓜 S) :=
  AddSubmonoid.closure {x | ∃ U : GradedObject 𝓜 S, U.1 ≤ k ∧ x = objectClass 𝓜 S U}

def vfDimensionAtMost (k : ℕ) : AddSubmonoid (VFSemiring 𝓜 S) :=
  AddSubmonoid.closure {x | ∃ A : VFObject 𝓜 S, A.1 ≤ k ∧ x = fieldClass 𝓜 S A}

/-- The dimension input is the mixed form of the fixed-base
projection-dimension invariance theorem. -/
@[expose] def MixedVFDimensionInvariant : Prop :=
  ∀ {n m d e : ℕ} {A : Set (SortedAssignment Z (MixedVariables n (Fin m)))}
    {B : Set (SortedAssignment Z (MixedVariables d (Fin e)))},
    SortedDefinableOver 𝓜 S.carrier A → SortedDefinableOver 𝓜 S.carrier B →
    MixedDefinablyEquivalent 𝓜 S A B →
    vfDimension (mixedTuple '' A) = vfDimension (mixedTuple '' B)

theorem liftClassHom_maps_filtration
    (H : IntegrationHypotheses S neg) (dim : MixedVFDimensionInvariant S) (k : ℕ) :
    (rvDegreeAtMost S k).map (liftClassHom H.liftIso).toAddMonoidHom = vfDimensionAtMost S k := by
  classical
  apply le_antisymm
  · apply AddSubmonoid.map_le_iff_le_comap.2
    apply AddSubmonoid.closure_le.2
    rintro _ ⟨U,le,rfl⟩
    change liftClassHom H.liftIso (objectClass 𝓜 S U) ∈ vfDimensionAtMost S k
    rw [liftClassHom_class]
    exact AddSubmonoid.subset_closure ⟨⟨U.1,liftFieldObject U.2⟩,le,rfl⟩
  · apply AddSubmonoid.closure_le.2
    rintro _ ⟨A,le,rfl⟩
    obtain ⟨U,D,parts,disj,cover⟩ := mixed_set_partition_into_lifts O hO power S H.head.minusOne
      H.head.minusOne_realizes H.head.fieldTerms H.head.fieldTerms_realize H.head.saturated H.head.immediate
      A.2.carrier A.2.definable A.2.finiteFibers
    have sub (s : Set (Fin A.2.vfArity)) : D s ⊆ A.2.carrier := cover ▸ Set.subset_iUnion D s
    have eq (s : Set (Fin A.2.vfArity)) :
        fieldClass 𝓜 S (restrictedFieldObject A (D s) (sub s) (parts s).1) = liftObjectClass (U s) :=
      fieldClass_of_iso 𝓜 S (parts s).2
    have each (s : Set (Fin A.2.vfArity)) : liftObjectClass (U s) ∈
        (rvDegreeAtMost S k).map (liftClassHom H.liftIso).toAddMonoidHom := by
      by_cases ne : (U s).2.carrier.Nonempty
      · have dU := lift_vfDimension_of_nonempty H.infinitesimal_ne H.infinitesimal_small (U s).2 ne
        have bound : vfDimension (mixedTuple '' D s) ≤ vfDimension (mixedTuple '' A.2.carrier) :=
          vfDimension_mono (X := Z) (Set.image_mono
            (f := mixedTuple (X := Z)) (sub s))
        have hd := dim (parts s).1 (ObjectLift.definable (U s).2) (parts s).2
        have deg : (U s).1 ≤ k := dU.symm.le.trans (hd.symm.le.trans (bound.trans (A.2.dimension.trans le)))
        exact ⟨objectClass 𝓜 S (U s),AddSubmonoid.subset_closure ⟨U s,deg,rfl⟩,
          liftClassHom_class H.liftIso (U s)⟩
      · have zero : objectClass 𝓜 S (U s) = 0 :=
          scissors_sound 𝓜 S (.zero (U s).2 (Set.not_nonempty_iff_eq_empty.1 ne))
        have e := liftClassHom_class H.liftIso (U s)
        rw [zero,map_zero] at e
        exact e ▸ AddSubmonoid.zero_mem _
    have h := fieldClass_partition A D (fun s => (parts s).1) sub disj cover
    rw [h]
    exact AddSubmonoid.sum_mem _ (fun s _ => (eq s).symm ▸ each s)

def filteredPositiveLiftEquiv
    (H : IntegrationHypotheses S neg) (dim : MixedVFDimensionInvariant S) (k : ℕ) :
    (rvDegreeAtMost S k).map ((Q).mk').toAddMonoidHom ≃+ vfDimensionAtMost S k := by
  let R := (rvDegreeAtMost S k).map ((Q).mk').toAddMonoidHom
  let e := positiveLiftEquiv S neg H
  let f := e.toRingHom.toAddMonoidHom
  have comp : f.comp ((Q).mk').toAddMonoidHom = (liftClassHom H.liftIso).toAddMonoidHom :=
    AddMonoidHom.ext (positiveLiftEquiv_mk S neg H)
  have eq : R.map f = vfDimensionAtMost S k := by
    unfold R
    rw [AddSubmonoid.map_map,comp,liftClassHom_maps_filtration S neg H dim k]
  have mapped := R.equivMapOfInjective f e.injective
  exact eq ▸ mapped

end GeneralizedEuler.Section5
