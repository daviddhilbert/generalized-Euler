module

public import Section4.SignedValueReflection
public import Section4.TaggedFiberMatching
public import Section4.SignedShears
import all Section2.RVVectorSpace
import all Section4.SignedValueGeneration
import all Section4.SignedRectangleFactors
import all Section4.SignedShears
import all Section4.TaggedFiberMatching
import all Section4.TaggedMatchGraph
import all Section4.Factors
import all Section4.ValuePullback

/-! Coordinatize the individual signed fibers of tagged objects by
positive representatives, compatibly with every fixed-base value shear. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) (hO : IsOrderConvex O)
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))

def signRepresentative (b : SignTypeˣ) : RV0 O := residueRV O (residue_for_sign O hO b).choose

theorem signRepresentative_nonzero (b) : signRepresentative O hO b ≠ 0 :=
  fun h => (residue_for_sign O hO b).choose_spec.1 (residueRV_injective O (h.trans (residueRV_zero O).symm))

theorem signRepresentative_label (b) : signedLabel O hO (signRepresentative O hO b) = (b,1) :=
  (residue_for_sign O hO b).choose_spec.2

def signedFiberCode (b : SignTypeˣ) (x : Additive (PositiveRV O)) : RV0 O :=
  signRepresentative O hO b * positiveRVToRV0 O x.toMul

theorem signedFiberCode_nonzero (b x) : signedFiberCode O hO b x ≠ 0 :=
  mul_ne_zero (signRepresentative_nonzero O hO b) (positiveRVToRV0_pos O _).ne_zero

include hv in
theorem signedFiberCode_label (b x) : signedLabel O hO (signedFiberCode O hO b x) = (b,(v x).toMul) := by
  rw [signedFiberCode,signedLabel_mul O hO (signRepresentative_nonzero _ _ _) (positiveRVToRV0_pos O _).ne_zero,
    signRepresentative_label,signedLabel_code,hv]
  exact Prod.ext (mul_one _) (one_mul _)

theorem signedFiberCode_injective (b) : Function.Injective (signedFiberCode O hO b) := by
  intro x y h
  change signRepresentative O hO b * positiveRVToRV0 O x.toMul = signRepresentative O hO b * positiveRVToRV0 O y.toMul at h
  apply Additive.toMul.injective
  apply positiveRVToRV0_injective O
  exact (Units.mk0 (signRepresentative O hO b) (signRepresentative_nonzero O hO b)).mul_right_inj.mp h

theorem signedFiberCode_surjective {t : RV0 O} (nz : t ≠ 0) :
    ∃ x, signedFiberCode O hO (signedLabel O hO t).1 x = t := by
  let b := (signedLabel O hO t).1
  let c := signRepresentative O hO b
  have nc := signRepresentative_nonzero O hO b
  have nu : t / c ≠ 0 := div_ne_zero (G₀ := RV0 O) nz nc
  have mul := signedLabel_mul O hO nu nc
  rw [div_mul_cancel₀ t nc,signRepresentative_label] at mul
  have eq : (signedLabel O hO (t / c)).1 = 1 := by
    apply mul_right_cancel (b := b)
    rw [one_mul]; exact (congrArg Prod.fst mul).symm
  obtain ⟨x,hx⟩ := exists_positiveRV_of_positive O ((signedLabel_pos O hO nu).mp eq)
  exact ⟨Additive.ofMul x,by change c * positiveRVToRV0 O x = t; rw [hx,mul_comm (G := RV0 O),div_mul_cancel₀ (G₀ := RV0 O) _ nc]⟩

variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))

theorem signedFiberCode_shear (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker) (b x) :
    signedShear v hv s hs G L (signedFiberCode O hO b x) =
      signedFiberCode O hO b (shear (T := Additive (PositiveRV O)) v G L x) := by
  rw [signedFiberCode,map_mul,signedShear_positive]
  have old : signedShear v hv s hs G L (signRepresentative O hO b) = signRepresentative O hO b := by
    apply signedShear_base
    have hz : RVValueSection.valueCoordinate (signRepresentative O hO b) = 1 := by
      apply Units.ext
      rw [RVValueSection.coe_valueCoordinate (signRepresentative_nonzero O hO b),
        unsignedValue_of_signedLabel O hO _ (signRepresentative_nonzero O hO b),signRepresentative_label]
    rw [hz]; exact G.zero_mem
  rw [old]; rfl

variable {J H : Language} [J.Structure K] [J.Structure (Residue O)] [H.Structure (SignedValueGroup O)]
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable H D → isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  {k : ℕ} (U : Over (J := H) A k)

@[expose] def signedFamily : FiberFamily (Additive O.ValueGroupˣ) where
  Tag := Fin U.tags × (Fin k → SignTypeˣ)
  height _ := k
  domain t := {z | signInsert t.2 z ∈ U.piece t.1}

def signedFamilyLabels : (signedFamily O A U).Label ≃ U.points A where
  toFun x := ⟨x.1.1,signInsert x.1.2 x.2.val,x.2.property⟩
  invFun p := ⟨(p.1,Prod.fst ∘ p.2.val),Prod.snd ∘ p.2.val,p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def signedFamilyCode (x : (signedFamily O A U).Lift (F := F) (T := Additive (PositiveRV O)) v) : (taggedSharp (S := S) (signedLabel O hO) A defSharp U).Points :=
  ⟨x.1.1,fun i => signedFiberCode O hO (x.1.2 i) (x.2.val i),fun i => signedFiberCode_nonzero O hO _ _,by
    have h : (fun i => signedLabel O hO (signedFiberCode O hO (x.1.2 i) (x.2.val i))) = signInsert x.1.2 (v ∘ x.2.val) :=
      funext fun i => signedFiberCode_label O hO v hv (x.1.2 i) (x.2.val i)
    exact (congrArg (· ∈ U.piece x.1.1) h).mpr x.2.property⟩

theorem signedFamilyCode_label (x : (signedFamily O A U).Lift (F := F) (T := Additive (PositiveRV O)) v) :
    sharpLabel (S := S) (signedLabel O hO) A defSharp U (signedFamilyCode O hO v hv P S A defSharp U x) =
      signedFamilyLabels O A U ((signedFamily O A U).label (F := F) (T := Additive (PositiveRV O)) v x) :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun i => signedFiberCode_label O hO v hv (x.1.2 i) (x.2.val i))))

theorem signedFamilyCode_bijective : Function.Bijective (signedFamilyCode O hO v hv P S A defSharp U) := by
  constructor
  · intro a b eq
    have el := congrArg (sharpLabel (S := S) (signedLabel O hO) A defSharp U) eq
    rw [signedFamilyCode_label,signedFamilyCode_label] at el
    have tags := congrArg Sigma.fst ((signedFamilyLabels O A U).injective el)
    obtain ⟨i,a⟩ := a; obtain ⟨j,b⟩ := b
    obtain rfl : i=j := tags
    have coords := congrArg Subtype.val (Sigma.mk.inj_iff.mp eq).2.eq
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun n => signedFiberCode_injective O hO _ (congrFun coords n))))
  · rintro ⟨i,t⟩
    choose x hx using fun n => signedFiberCode_surjective O hO (t.property.1 n)
    let b := fun n => (signedLabel O hO (t.val n)).1
    have eq : signInsert b (v ∘ x) = signedLabel O hO ∘ t.val := funext fun n =>
      (signedFiberCode_label O hO v hv (b n) (x n)).symm.trans (congrArg (signedLabel O hO) (hx n))
    exact ⟨⟨(i,b),x,(congrArg (· ∈ U.piece i) eq).mpr t.property.2⟩,Sigma.ext rfl (heq_of_eq (Subtype.ext (funext hx)))⟩

end GeneralizedEuler.Section4
