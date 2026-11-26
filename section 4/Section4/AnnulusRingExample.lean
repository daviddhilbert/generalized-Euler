module

public import Section4.BoundedRVAnnuli
public import Section4.TwoAnnulusClasses
public import Section4.RVObjectClassEquality
import all Section4.SemiringGroupification
import all Section4.BoundedIntervalScissors
public import Section4.LiftQuotientProfiles
public import Section4.SignedTensorFactors
import all Section4.SignedTensorFactors
import all Section4.SignedRectangleFactors
import all Section4.BoundedValueBoxes
import all Section4.QuotientSpanProfiles
import all Section4.SignedValueGeneration
import all Section4.ValueEmbedding
import all Section4.ValueScissors
import all Section4.UnaryTaggedComparison
import all Section4.Factors
import all Section4.TaggedLiftRealization
import all Section4.RVTaggedEquivalence

/-! Two products of annuli are distinguished by the positive RV semiring
and have the same image in the Grothendieck ring. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject Set
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J JS : Language} [J.Structure K] [J.Structure (Residue O)]
  [JS.Structure (SignedValueGroup O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (liftIso : ∀ {k} (D E : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS E →
    ∀ f : D ≃ E, A.Definable JS {z : Fin k ⊕ Fin k → SignedValueGroup O | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D) (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) E))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO

variable [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F (Additive O.ValueGroupˣ)]
local notation "V" => Additive O.ValueGroupˣ


local notation "embed" => mapTuples (positiveValueEmb O)
variable {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)]

include hv hs agrees units clamp powers defSharp liftIso in
theorem two_annuli_distinct_before_groupification
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    (signedDef : ∀ {n} {D : Set (Fin n → V)}, (G : Set V).Definable JG D → A.Definable JS (embed '' D))
    (lang : ValueLanguage (J := JG) G)
    (order : (G : Set V).Definable JG {x : Fin 2 → V | x 0 ≤ x 1})
    (leDef : ∀ t ∈ G, (G : Set V).Definable JG {x : Unit → V | x () ≤ t})
    (step : V) (pos : 0 < step)
    (sat : ∀ fs : Finset V, UnaryValueSaturation JG (↑(G ⊔ Submodule.span F (fs : Set V)) : Set V))
    (a b : V) (ha : 0 < a) (hb : 0 < b) (oa : a ∈ G) (ob : b ∈ G)
    (small : ∀ c : F, 0 < c → c • a < b)
    (da : (G : Set V).Definable JG {x : Unit → V | x () ∈ Ioo 0 a})
    (db : (G : Set V).Definable JG {x : Unit → V | x () ∈ Ioo 0 b})
    (dr : (G : Set V).Definable JG (upperRay 0))
    (dp : (G : Set V).Definable JG ({0} : Set (Fin 1 → V))) :
    ∃ (d : isRVSet M S (sharp M val (embed '' boundedBox ![a,b])))
      (d' : isRVSet M S (sharp M val (embed '' boundedBox ![b,b]))),
      let U := sharpObject M S val _ d
      let W := sharpObject M S val _ d'
      objectClass M S ⟨2,U⟩ ≠ objectClass M S ⟨2,W⟩ ∧
      SemiringGroupification.of _ (objectClass M S ⟨2,U⟩) =
        SemiringGroupification.of _ (objectClass M S ⟨2,W⟩) := by
  have ds : ∀ i : Fin 2, (G : Set V).Definable JG {x : Unit → V | x () ∈ Ioo 0 (![a,b] i)} := by
    intro i; fin_cases i; exact da; exact db
  have dt : ∀ i : Fin 2, (G : Set V).Definable JG {x : Unit → V | x () ∈ Ioo 0 (![b,b] i)} := by
    intro i; fin_cases i <;> exact db
  let D := boundedBox ![a,b]
  let E := boundedBox ![b,b]
  have dD := boundedBox_definable G _ ds
  have dE := boundedBox_definable G _ dt
  let U := sharpObject M S val (embed '' D) (defSharp (signedDef dD))
  let W := sharpObject M S val (embed '' E) (defSharp (signedDef dE))
  have leftEq : sharp M val (embed '' D) = positiveSharp O v D := signed_sharp_positive O hO v hv P _
  have rightEq : sharp M val (embed '' E) = positiveSharp O v E := signed_sharp_positive O hO v hv P _
  refine ⟨defSharp (signedDef dD),defSharp (signedDef dE),?_,?_⟩
  · intro eq
    have iso := (objectClass_eq_iff_definably_equivalent U W).mp eq
    change RVDefinablyEquivalent M S.carrier (sharp M val (embed '' D)) (sharp M val (embed '' E)) at iso
    rw [leftEq,rightEq] at iso
    obtain ⟨e,scale⟩ := (bounded_rv_annuli_iff_same_scales O v hv s hs G hO P g agrees units clamp powers
      S A defSharp liftIso base qe signedDef lang order leDef step pos sat ![a,b] ![b,b]
      (by intro i; fin_cases i; exact ha; exact hb) (by intro i; fin_cases i <;> exact hb)
      (by intro i; fin_cases i; exact oa; exact ob) (by intro i; fin_cases i <;> exact ob) ds dt).mp iso
    have same := scale 0
    have target : ∀ i : Fin 2, ![b,b] i = b := by intro i; fin_cases i <;> rfl
    rw [target] at same
    have mem : b ∈ scaleSpace F a := same.symm ▸ self_mem_scaleSpace F b
    obtain ⟨c,hc,h⟩ := (mem_scaleSpace_iff F ha).mp mem
    rw [abs_of_pos hb] at h
    exact (small c hc).not_ge h
  · have di : (G : Set V).Definable JG (intervalPiece a) := da.preimage_comp (fun _ : Unit => (0 : Fin 1))
    have dj : (G : Set V).Definable JG (intervalPiece b) := db.preimage_comp (fun _ : Unit => (0 : Fin 1))
    let lift := (valueFactorHom M S val A defSharp liftIso).comp (signedPieceMap O G A signedDef)
    have same := (bounded_pair_group_class G lang a b oa ob ha hb di dj dr dp dD).trans
      (bounded_pair_group_class G lang b b ob ob hb hb dj dj dr dp dE).symm
    have image := congrArg (SemiringGroupification.map lift) same
    simp only [SemiringGroupification.map_of,lift,RingHom.comp_apply,signedPieceMap_class,valueFactorHom_piece] at image
    exact image

end GeneralizedEuler.Section4
