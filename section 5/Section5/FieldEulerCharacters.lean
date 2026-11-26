module

public import Section5.IntegrationIsomorphism
public import Section5.BlowupEulerQuotient

/-! Transfer the two Euler characters from the RV quotient to the
VF Grothendieck ring along the fixed-base integration isomorphism. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "R" => SemiringGroupification.Ring (VFSemiring 𝓜 S)

theorem field_euler_characters (inputs : IntegrationHypotheses S neg)
    {H : Language} [H.Structure (SignedValueGroup O)] (D : Set (SignedValueGroup O))
    (defSharp : ∀ {k} {V : Set (Fin k → SignedValueGroup O)}, D.Definable H V →
      isRVSet 𝓜 S (sharp 𝓜 (signedLabel O hO) V))
    (he : D.Definable H ({1} : Set (Fin 1 → SignedValueGroup O)))
    (ordinary : ResidueSemiring 𝓜 S (signedLabel O hO) →+* ℤ)
    (formula : SectionFourEulerFormulas O hO power S D @defSharp he ordinary) :
    ∃ q : R ≃+* ℤ × ℤ, ∀ f : R →+* ℤ,
      f = (RingHom.fst ℤ ℤ).comp q.toRingHom ∨ f = (RingHom.snd ℤ ℤ).comp q.toRingHom := by
  obtain ⟨q,hq⟩ := blowupQuotient_euler_characters O hO power S neg D @defSharp he ordinary formula
  let e := groupifyRingEquiv (A := VFSemiring 𝓜 S)
    (B := (gradedBlowupCongruence O hO power S neg).Quotient) (positiveLiftEquiv S neg inputs).symm
  refine ⟨e.trans q,?_⟩
  intro f
  rcases hq (f.comp e.symm.toRingHom) with h | h
  · left
    apply RingHom.ext
    intro x
    have hx := DFunLike.congr_fun h (e x)
    change f (e.symm (e x)) = (q (e x)).1 at hx
    rw [e.symm_apply_apply] at hx
    exact hx
  · right
    apply RingHom.ext
    intro x
    have hx := DFunLike.congr_fun h (e x)
    change f (e.symm (e x)) = (q (e x)).2 at hx
    rw [e.symm_apply_apply] at hx
    exact hx

end GeneralizedEuler.Section5
