module

public import Section5.VerticalCenters
public import Section2.SmallImmediateAdjunction

/-! Adjoining finitely many field variables preserves the smallness
needed for the immediate-isomorphism argument. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Cardinal

universe u v w

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language.{u,v}} [L.Structure K] {E : Type w}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

theorem centerBase_card_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hL : #(Σ i, L.Functions i) ≤ μ) (hS : #(S.carrier .vf) ≤ μ)
    {n : ℕ} (y : Fin n → K) :
    #(((canonicalStructure (L := L) O hO power).termGenerated
        (centerAssignment O hO power S y)).carrier .vf) ≤ μ := by
  rw [vf_carrier_termGenerated_eq O hO power]
  apply card_fieldClosure_le hμ hL
  apply mk_range_le.trans
  change #((S.carrier .vf) ⊕ Fin n) ≤ μ
  rw [mk_sum, lift_uzero, lift_mk_fin]
  exact add_le_of_le hμ hS (natCast_lt_aleph0.le.trans hμ)

end GeneralizedEuler.Section5
