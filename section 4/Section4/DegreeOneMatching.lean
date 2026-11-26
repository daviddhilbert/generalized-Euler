module

public import Section4.UnaryRemainders
public import Section4.FiniteFiberEuler
public import Section4.SignedWholeMatches
import all Section4.MatchingRectangles
import all Section4.TaggedMatchGraph
import all Section4.UnaryTaggedComparison
import all Section4.Factors

/-! Complete the whole-fiber matching. Saturation makes both complementary
label sets finite, and the Euler characteristic of their actual fibers
gives equality of their cardinalities. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) (hO : IsOrderConvex O) [Module F (Additive O.ValueGroupˣ)]
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J H JG : Language} [J.Structure K] [J.Structure (Residue O)] [H.Structure (SignedValueGroup O)]
  [JG.Structure O.ValueGroupˣ] (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (A : Set (SignedValueGroup O)) (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable H D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
local instance unaryMatchingBaseStructure : JG.Structure (Additive O.ValueGroupˣ) := inferInstanceAs (JG.Structure O.ValueGroupˣ)
local instance unaryMatchingSignedStructure : H.Structure (SignTypeˣ × Additive O.ValueGroupˣ) := inferInstanceAs (H.Structure (SignedValueGroup O))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO
local notation "lab" => sharpLabel (S := S) val A defSharp
local notation "sh" => taggedSharp (S := S) val A defSharp

theorem conclude_unary_matching
    (interpret : SignedInterpretation (J := JG) (H := H) (G : Set (Additive O.ValueGroupˣ)) A)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))
    (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet M S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (he : A.Definable H ({1} : Set (Fin 1 → SignedValueGroup O)))
    (μ : LocalRVMeasure M S (positiveUnit O hO) 1 ℤ)
    (chi : μ.weight (positiveUnitLine (J := J) O hO P) (positiveUnitLine_good O hO P S A defSharp he) = -1)
    (U W : Over (J := H) A 1) (f : (sh U).Points ≃ (sh W).Points)
    (graph : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ f i j))
    (defR : ∀ i j, A.Definable H (taggedGraph U W (WholeMatch (lab U) (lab W) f) i j))
    (defRev : ∀ j i, A.Definable H (taggedGraph W U (fun b a => WholeMatch (lab U) (lab W) f a b) j i))
    (old : ∀ a, (¬ ∃ b, WholeMatch (lab U) (lab W) f a b) → Additive.ofMul ((pointTuple U a 0).2) ∈ G)
    (old' : ∀ b, (¬ ∃ a, WholeMatch (lab U) (lab W) f a b) → Additive.ofMul ((pointTuple W b 0).2) ∈ G) :
    taggedValueClass A U = taggedValueClass A W := by
  classical
  let R := WholeMatch (lab U) (lab W) f
  let D : Set (U.points A) := {a | ∃ b, R a b}
  let E : Set (W.points A) := {b | ∃ a, R a b}
  have surj (V : Over (J := H) A 1) : Function.Surjective (lab V) := by
    rintro ⟨i,a⟩
    choose x nz eq using fun n => signedLabel_rep O hO (a.val n)
    have h := funext eq
    exact ⟨⟨i,x,nz,(congrArg (· ∈ V.piece i) h).mpr a.property⟩,Sigma.ext rfl (heq_of_eq (Subtype.ext h))⟩
  have single {a b c} (h : R a b) (k : R a c) := wholeMatch_functional _ _ f (surj W) h k
  have inj {a b c} (h : R a c) (k : R b c) := wholeMatch_injective _ _ f (surj U) h k
  let g : D ≃ E := matchingGraphEquiv R (fun h k => single h k) (fun h k => inj h k)
  have law : (fun a b => ∃ p : D, p.val=a ∧ (g p).val=b) = R := by
    funext a b; apply propext
    exact ⟨fun ⟨p,h,e⟩ => h ▸ (matchingGraphEquiv_iff R (fun t u => single t u) (fun t u => inj t u) p b).mp e,
      fun h => ⟨⟨a,b,h⟩,rfl,(matchingGraphEquiv_iff R _ _ _ b).mpr h⟩⟩
  have fd : Dᶜ.Finite := old_unary_tags_finite (J := JG) (H := H) G A @interpret U sat _
    (tagged_relation_remainder A U W R defR) (fun a h => old a h)
  have fe : Eᶜ.Finite := old_unary_tags_finite (J := JG) (H := H) G A @interpret W sat _
    (tagged_relation_remainder A W U (fun b a => R a b) defRev) (fun b h => old' b h)
  have du (a : (Dᶜ : Set _)) : A.Definable H {pointTuple U a.val} :=
    old_signed_tuple_definable (J := JG) (H := H) G A @interpret _ (fun i => by rw [Subsingleton.elim i 0]; exact old a.val a.property)
  have dw (b : (Eᶜ : Set _)) : A.Definable H {pointTuple W b.val} :=
    old_signed_tuple_definable (J := JG) (H := H) G A @interpret _ (fun i => by rw [Subsingleton.elim i 0]; exact old' b.val b.property)
  apply complete_tagged_matching U W D E g (by rw [law]; exact defR) fd fe du dw
  let := fd.fintype
  let := fe.fintype
  let e := (Fintype.equivFin (Dᶜ : Set _)).symm
  let t := (Fintype.equivFin (Eᶜ : Set _)).symm
  have iso := selected_iso (S := S) val A defSharp U W Dᶜ e (fun i => du (e i)) Eᶜ t (fun i => dw (t i)) f graph
    (fun (x : (sh U).Points) => not_congr (wholeMatch_preserves_matched (lab U) (lab W) f x))
  simpa only [Nat.card_eq_fintype_card] using finite_fiber_euler_counts O hO P S A defSharp @witness he μ chi U W Dᶜ Eᶜ e t _ _ iso

end GeneralizedEuler.Section4
