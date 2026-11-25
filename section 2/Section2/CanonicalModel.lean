module

public import Section2.ConvexLanguage
public import Section2.SortedStructure
public import Section2.PowerOrder

/-! The canonical expansion of a proper T-convex pair in Proposition 2.13. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] {L : Language.{u, v}} [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] [TopologicalSpace (Residue O)]
  {E : Type w}

/-- The remaining model conditions after fixing the canonical RV quotient,
its order, and the embedded residue field. The power laws on RV follow
from the laws of the named field powers. -/
structure CanonicalTCVFModel (T : L.Theory) (g : E → PositiveField K →* PositiveField K)
    (P : E → RV0 O → RV0 O) : Prop where
  fieldModel : K ⊨ T
  residueModel : Residue O ⊨ T
  nontrivial : O.valuation.IsNontrivial
  tConvex : IsTConvex L O
  matching : MatchesContinuousFunctions L O
  power : ∀ e, AgreesWithFieldPower O (g e) (P e) ∧
    ∀ t, ¬IsPositiveRV O t → P e t = 0

/-- The canonical residue model and matching of the clamped field powers
give a unique interpretation of the power symbols on the canonical
leading-term quotient. -/
theorem existsUnique_canonicalTCVFModel (T : L.Theory)
    (g : E → PositiveField K →* PositiveField K)
    (hT : K ⊨ T) (hResidue : Residue O ⊨ T) (hProper : O.valuation.IsNontrivial)
    (hConvex : IsTConvex L O) (hMatch : MatchesContinuousFunctions L O)
    (gResidue : E → Residue O → Residue O)
    (hClamp : ∀ e, ResidueCompatible O (fun x => g e (clampForPower x)) (gResidue e))
    (hOne : ∀ e, gResidue e 1 = 1) :
    ∃! P : E → RV0 O → RV0 O, CanonicalTCVFModel O T g P := by
  have hO : IsOrderConvex O := hConvex.isOrderConvex
  obtain ⟨P, hp, hu⟩ := existsUnique_leadingTermPowerFamily O hO g gResidue hClamp hOne
  exact ⟨P, ⟨hT, hResidue, hProper, hConvex, hMatch, hp⟩, fun Q hQ => hu Q hQ.power⟩

end GeneralizedEuler.Section2
