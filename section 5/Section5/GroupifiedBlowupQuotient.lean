module

public import Section5.GradedBlowupCongruence
public import Section4.SemiringGroupification
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Groupifying the positive common-blowup quotient gives the
Grothendieck ring modulo the principal elementary blowup ideal. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder
open SemiringGroupification

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (hneg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "ℛ" => RVSemiring 𝓜 S
local notation "C" => gradedBlowupCongruence O hO power S hneg
local notation "a" => residuePointClass O hO power S
local notation "b" => (1 + multiplierClass O hO power S hneg)

@[expose] def elementaryBlowupIdeal : Ideal (SemiringGroupification.Ring ℛ) :=
  Ideal.span {of ℛ b - of ℛ a}

/-- This comparison uses the universal properties of the two quotients. -/
def groupifiedBlowupQuotientEquiv :
    (SemiringGroupification.Ring ℛ ⧸ elementaryBlowupIdeal O hO power S hneg) ≃+*
      SemiringGroupification.Ring (C).Quotient := by
  let I := elementaryBlowupIdeal O hO power S hneg
  let Q := (C).Quotient
  let blow := (C).mk'
  let kill : SemiringGroupification.Ring ℛ →+* SemiringGroupification.Ring Q :=
    SemiringGroupification.map blow
  have baseEq : blow a = blow b := Quotient.sound
    ⟨b,1,0,⟨b,degree_one_point_blowup O hO power S hneg,rfl⟩,rfl⟩
  have vanishes (x : SemiringGroupification.Ring ℛ) (hx : x ∈ I) : kill x = 0 := by
    have mem : I ≤ RingHom.ker kill := by
      apply Ideal.span_le.2
      rintro _ rfl
      change kill (of ℛ b - of ℛ a) = 0
      simp only [map_sub,kill,SemiringGroupification.map_of,baseEq,sub_self]
    exact mem hx
  let forward := Ideal.Quotient.lift I kill vanishes
  let quotient := Ideal.Quotient.mk I
  let underlying := quotient.comp (of ℛ)
  have identify : underlying a = underlying b := by
    have zero : quotient (of ℛ b - of ℛ a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    have eq : quotient (of ℛ b) - quotient (of ℛ a) = 0 :=
      (map_sub quotient (of ℛ b) (of ℛ a)).symm.trans zero
    exact (sub_eq_zero.1 eq).symm
  let reverseSemiring : Q →+* (SemiringGroupification.Ring ℛ ⧸ I) :=
    (C).lift underlying (by
      rw [gradedBlowupCongruence_eq_generated]
      apply RingCon.ringConGen_le.mpr
      rintro _ _ ⟨rfl,rfl⟩
      exact identify)
  let reverse : SemiringGroupification.Ring Q →+* (SemiringGroupification.Ring ℛ ⧸ I) :=
    SemiringGroupification.lift (R := Q) (T := SemiringGroupification.Ring ℛ ⧸ I) reverseSemiring
  have baseReverse (x : ℛ) : reverse (of Q (blow x)) = quotient (of ℛ x) := by
    change SemiringGroupification.lift (R := Q) (T := SemiringGroupification.Ring ℛ ⧸ I)
      reverseSemiring (of Q (blow x)) = _
    rw [SemiringGroupification.lift_of (R := Q) (T := SemiringGroupification.Ring ℛ ⧸ I)]
    rfl
  have baseForward (x : ℛ) : forward (quotient (of ℛ x)) = of Q (blow x) := by
    change kill (of ℛ x) = of Q (blow x)
    exact SemiringGroupification.map_of (R := ℛ) (V := Q) blow x
  apply RingEquiv.ofRingHom forward reverse
  · apply SemiringGroupification.hom_ext
    intro y
    obtain ⟨x,rfl⟩ := (C).mk'_surjective y
    change forward (reverse (of Q (blow x))) = of Q (blow x)
    rw [baseReverse,baseForward]
  · have onTop : (reverse.comp forward).comp quotient = quotient := by
      apply SemiringGroupification.hom_ext (R := ℛ) (T := SemiringGroupification.Ring ℛ ⧸ I)
        (f := (reverse.comp forward).comp quotient) (g := quotient)
      intro x
      change reverse (forward (quotient (of ℛ x))) = quotient (of ℛ x)
      rw [baseForward,baseReverse]
    apply RingHom.ext
    intro y
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective y
    exact DFunLike.congr_fun onTop x

theorem groupifiedBlowupQuotientEquiv_mk (x : ℛ) :
    groupifiedBlowupQuotientEquiv O hO power S hneg
      (Ideal.Quotient.mk (elementaryBlowupIdeal O hO power S hneg) (of ℛ x)) =
      of (C).Quotient ((C).mk' x) := by
  unfold groupifiedBlowupQuotientEquiv
  exact SemiringGroupification.map_of (R := ℛ) (V := (C).Quotient) ((C).mk') x

end GeneralizedEuler.Section5
