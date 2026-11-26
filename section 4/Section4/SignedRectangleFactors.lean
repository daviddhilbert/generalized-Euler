module

public import Section4.RectangleGeneration
public import Section4.RectangleMap
public import Section2.SignedValue
import all Section2.SignedValue
import all Section2.RVVectorSpace
import all Section4.RectangleClasses
import all Section4.ValuePullback
import all Section4.PositivePresentations
import all Section4.Objects

/-! Interpretation of the two chart factors in the signed value and residue categories. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 SignType
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

def signedLabel (t : RV0 O) : SignedValueGroup O := (signedValue O hO t).unzeroD 1

def positiveValueLabel (γ : Additive O.ValueGroupˣ) : SignedValueGroup O := (1,γ.toMul)

theorem signedLabel_pos {t : RV0 O} (ht : t ≠ 0) :
    (signedLabel O hO t).1 = 1 ↔ IsPositiveRV O t := by
  obtain ⟨x,rfl⟩ := rv_surjective O t
  have hx := (rv_eq_zero_iff O).not.mp ht
  rw [signedLabel,signedValue_rv_of_ne_zero O hO hx,isPositiveRV_rv_iff O hO]
  change (Units.mk0 (sign x) (sign_eq_zero_iff.not.mpr hx) : SignTypeˣ) = 1 ↔ 0 < x
  rw [← Units.val_inj]; exact sign_eq_one_iff

theorem signedLabel_code (t : PositiveRV O) :
    signedLabel O hO (positiveRVToRV0 O t) = positiveValueLabel O (Additive.ofMul (positiveValueMap O t)) := by
  have hpos := positiveRVToRV0_pos O t
  apply Prod.ext
  · exact (signedLabel_pos O hO (hpos.ne_zero O)).mpr hpos
  · apply Units.ext
    change ((signedLabel O hO (positiveRVToRV0 O t)).2 : O.ValueGroup) = (positiveValueMap O t : O.ValueGroup)
    rw [positiveValueMap_coe]
    obtain ⟨x,hx⟩ := rv_surjective O (positiveRVToRV0 O t)
    have ne : x ≠ 0 := (rv_eq_zero_iff O).not.mp (hx ▸ hpos.ne_zero O)
    rw [← hx,signedLabel,signedValue_rv_of_ne_zero O hO ne,unsignedValue_rv]
    rfl

variable [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)]
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

include hv in
theorem signed_sharp_positive {n} (D : Set (Fin n → Additive O.ValueGroupˣ)) :
    sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO)
      ((fun γ => positiveValueLabel O ∘ γ) '' D) = positiveSharp O v D := by
  ext x
  constructor
  · rintro ⟨nz,γ,hγ,e⟩
    have pos (i) : IsPositiveRV O (x i) :=
      (signedLabel_pos O hO (nz i)).mp ((congrArg Prod.fst (congrFun e i)).symm)
    choose z hz using fun i => exists_positiveRV_of_positive O (pos i)
    let t i := Additive.ofMul (z i)
    have eq : v ∘ t = γ := by
      funext i
      have label := (signedLabel_code O hO (z i)).symm.trans
        ((congrArg (signedLabel O hO) (hz i)).trans (congrFun e i).symm)
      exact (hv (t i)).trans (congrArg (fun p : SignedValueGroup O => Additive.ofMul p.2) label)
    exact ⟨t,show v ∘ t ∈ D by rwa [eq],funext hz⟩
  · rintro ⟨t,ht,rfl⟩
    refine ⟨fun i => (positiveRVToRV0_pos O _).ne_zero O, v ∘ t,ht,funext fun i => ?_⟩
    exact (congrArg (positiveValueLabel O) (hv (t i))).trans (signedLabel_code O hO _).symm

include hv in
theorem coded_residue_object {n r m} {G : Submodule F (Additive O.ValueGroupˣ)}
    (A : ValueFrame G r n) (e : Fin m ≃ A.dependent) (B : Set (A.dependent → v.ker))
    (hb : isRVSet _ S (codedResidues O v A e B)) :
    (positiveObject O hO P S _ hb (codedResidues_pos O v A e B)).IsResidue _ S (signedLabel O hO) := by
  apply (Set.finite_singleton (1 : Fin m → SignedValueGroup O)).subset
  rintro _ ⟨x,rfl⟩
  obtain ⟨b,_,eq⟩ := x.property
  change signedLabel O hO ∘ x.val = 1
  rw [← eq]
  funext i
  have unit : v (b (e i)).val = 0 := (b (e i)).property
  change signedLabel O hO (positiveRVToRV0 O (b (e i)).val.toMul) = 1
  rw [signedLabel_code,← hv,unit]; rfl

end GeneralizedEuler.Section4
