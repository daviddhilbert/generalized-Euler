module

public import Section5.GroupifiedBlowupQuotient
public import Section4.GeometricRVCoordinates
public import Section4.ResidueBaseValues
import all Section5.BlowupClassProducts
import all Section4.PositivePresentations
import all Section4.ValuePullback
import all Section4.SignedPuncturedIdeal
import all Section2.SortedStructure

/-! The punctured maximal ideal in the elementary blowup is the
sharp of the signed lower ray used in the Euler formulas. -/

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
local notation "idealValues" => allSigns (Z := SignTypeˣ) (lowerRay (V := Additive O.ValueGroupˣ))
local notation "lab" => signedLabel O hO

omit S hneg in
theorem sharp_signed_lower_ray :
    sharp 𝓜 lab idealValues =
      {x : Fin 1 → RV0 O | unsignedValue O (x 0) < 1 ∧ x 0 ≠ 0} := by
  ext x
  change ((∀ j : Fin 1, x j ≠ 0) ∧
    @LT.lt (Additive O.ValueGroupˣ) inferInstance (lab (x 0)).2 0) ↔
    unsignedValue O (x 0) < 1 ∧ x 0 ≠ 0
  constructor
  · rintro ⟨nz,lt⟩
    refine ⟨?_,nz 0⟩
    rw [unsignedValue_of_signedLabel O hO _ (nz 0)]
    exact lt
  · rintro ⟨lt,nz⟩
    refine ⟨fun j => ?_,?_⟩
    · rwa [Subsingleton.elim j (0 : Fin 1)]
    · rwa [unsignedValue_of_signedLabel O hO _ nz] at lt

theorem multiplierClass_eq_signed_lower_ray (hd : isRVSet 𝓜 S (sharp 𝓜 lab idealValues)) :
    multiplierClass O hO power S hneg =
      objectClass 𝓜 S ⟨1,sharpObject 𝓜 S lab idealValues hd⟩ := by
  have same (D D' : Set (Fin 1 → RV0 O)) (hD : isRVSet 𝓜 S D) (hD' : isRVSet 𝓜 S D')
      (nz : ∀ x ∈ D, ∀ i, x i ≠ (𝓜).funMap .rvZero (fun j => j.elim0))
      (nz' : ∀ x ∈ D', ∀ i, x i ≠ (𝓜).funMap .rvZero (fun j => j.elim0)) (eq : D = D') :
      identityRVObject (M := 𝓜) (C := S) D hD nz = identityRVObject (M := 𝓜) (C := S) D' hD' nz' := by
    subst D'
    rfl
  let D := {x : Fin 1 → RV0 O | unsignedValue O (x 0) < 1 ∧ x 0 ≠ 0}
  let hD := nonzero_multipliers_definable O hO power S hneg
  have nz : ∀ x ∈ D, ∀ i, x i ≠ (𝓜).funMap .rvZero (fun j => j.elim0) := by
    intro x hx i
    rw [Subsingleton.elim i (0 : Fin 1)]
    exact hx.2
  have eq := same D _ hD hd nz (fun _ hx => hx.1)
    (sharp_signed_lower_ray (L := L) O hO power).symm
  exact congrArg (fun u : RVObject 𝓜 S 1 => objectClass 𝓜 S ⟨1,u⟩) eq

theorem elementaryBlowupIdeal_eq_euler (hd : isRVSet 𝓜 S (sharp 𝓜 lab idealValues)) :
    elementaryBlowupIdeal O hO power S hneg = Ideal.span
      {1 + of ℛ (objectClass 𝓜 S ⟨1,sharpObject 𝓜 S lab idealValues hd⟩) -
        of ℛ (objectClass 𝓜 S ⟨1,residuePointObject O hO power S⟩)} := by
  rw [elementaryBlowupIdeal,map_add,map_one,multiplierClass_eq_signed_lower_ray O hO power S hneg hd]
  rfl

theorem blowupQuotient_euler_characters {H : Language} [H.Structure (SignedValueGroup O)]
    (D : Set (SignedValueGroup O))
    (defSharp : ∀ {k} {V : Set (Fin k → SignedValueGroup O)}, D.Definable H V →
      isRVSet 𝓜 S (sharp 𝓜 lab V))
    (he : D.Definable H ({1} : Set (Fin 1 → SignedValueGroup O)))
    (ordinary : ResidueSemiring 𝓜 S lab →+* ℤ)
    (formula : SectionFourEulerFormulas O hO power S D @defSharp he ordinary) :
    let Q := SemiringGroupification.Ring (gradedBlowupCongruence O hO power S hneg).Quotient
    ∃ q : Q ≃+* ℤ × ℤ, ∀ f : Q →+* ℤ,
      f = (RingHom.fst ℤ ℤ).comp q.toRingHom ∨ f = (RingHom.snd ℤ ℤ).comp q.toRingHom := by
  obtain ⟨di,⟨q,hq⟩,_⟩ := formula
  let toEuler := (groupifiedBlowupQuotientEquiv O hO power S hneg).symm.trans
    (Ideal.quotEquivOfEq (elementaryBlowupIdeal_eq_euler O hO power S hneg (defSharp di)))
  refine ⟨toEuler.trans q,?_⟩
  intro f
  rcases hq (f.comp toEuler.symm.toRingHom) with h | h
  · left
    apply RingHom.ext
    intro x
    have hx := DFunLike.congr_fun h (toEuler x)
    change f (toEuler.symm (toEuler x)) = (q (toEuler x)).1 at hx
    rwa [RingEquiv.symm_apply_apply] at hx
  · right
    apply RingHom.ext
    intro x
    have hx := DFunLike.congr_fun h (toEuler x)
    change f (toEuler.symm (toEuler x)) = (q (toEuler x)).2 at hx
    rwa [RingEquiv.symm_apply_apply] at hx

end GeneralizedEuler.Section5
