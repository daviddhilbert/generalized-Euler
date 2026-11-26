module

public import Section4.ValueFactorMap
public import Section4.RVProducts
public import Mathlib.Data.Set.Card
import all Section4.ValueFactorMap
import all Section4.ValueDescent
import all Section4.Factors
import all Section4.ValuePullback
import all Section4.Objects
import all Section4.Scissors

/-! Degree zero of Question 4.16. Counting actual RV points descends
to the semiring and distinguishes every finite tagged degree-zero object. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
variable {L : Language} {F : Type*} {Z : TCsort → Type*} (M : SortedStructure L F Z) (S : SortedSubstructure M)

def rvCardinality : RVSemiring M S →+* ℕ∞ := by
  let w (U : GradedObject M S) := U.2.carrier.encard
  apply descendWeights M S w
  intro a b relation
  cases relation with
  | iso U V h => simpa [w] using ENat.card_congr h.choose
  | zero U h => simp [w,h]
  | one U h => obtain ⟨x,hx⟩ := h; simp [w,hx]
  | cut U V W A B _ _ disj cov ha hb =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_add,w]
    rw [← cov,Set.encard_union_eq disj]
    exact congrArg₂ (·+·) (ENat.card_congr ha.choose) (ENat.card_congr hb.choose)
  | prod U V W h =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul,w]
    exact (ENat.card_congr ((productPoints U.carrier V.carrier).trans h.choose).symm).trans (ENat.card_prod _ _)

@[simp] theorem rvCardinality_class (U : GradedObject M S) :
    rvCardinality M S (objectClass M S U) = U.2.carrier.encard := by
  unfold rvCardinality
  apply descendWeights_class

variable {J : Language} {Γ : Type*} [J.Structure Γ] (v : Z .rv → Γ) (A : Set Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D B : Set (Fin k → Γ)), A.Definable J D → A.Definable J B →
    ∀ e : D ≃ B, A.Definable J {w : Fin k ⊕ Fin k → Γ | ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v B))

private theorem zero_sharp_card (D : Set (Fin 0 → Γ)) : (sharp M v D).encard = D.encard := by
  let f : sharp M v D ≃ D :=
    { toFun := fun x => ⟨v ∘ x.val,x.property.2⟩
      invFun := fun y => ⟨fun i => i.elim0,fun i => i.elim0,(congrArg (· ∈ D) (Subsingleton.elim y.val (v ∘ fun i : Fin 0 => i.elim0))).mp y.property⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  exact ENat.card_congr f

def taggedValueClass {k} (U : Over (J := J) A k) : SemiringOfSets (J := J) A :=
  (ringConGen (Relation (J := J) A)).mk' (MvPolynomial.X ⟨k,U⟩)

theorem degree_zero_lift_card (U : Over (J := J) A 0) :
    rvCardinality M S (valueFactorHom M S v A defSharp liftIso (taggedValueClass A U)) = ENat.card (U.points A) := by
  change rvCardinality M S (MvPolynomial.eval₂ _ (sharpMeasure M S v A defSharp liftIso).tagged (MvPolynomial.X ⟨0,U⟩)) = _
  rw [MvPolynomial.eval₂_X]
  change rvCardinality M S (∑ i, objectClass M S ⟨0,sharpObject M S v (U.piece i) _⟩) = _
  rw [map_sum]
  simp only [rvCardinality_class]
  change (∑ i, (sharp M v (U.piece i)).encard) = ENat.card (Σ i, U.piece i)
  simp_rw [zero_sharp_card]
  classical
  let inst (i) : Fintype (U.piece i) := Fintype.ofFinite _
  change (∑ i, ENat.card (U.piece i)) = _
  simp only [ENat.card_eq_coe_fintype_card,Fintype.card_sigma,Nat.cast_sum]

theorem degree_zero_value_injective (U V : Over (J := J) A 0)
    (eq : valueFactorHom M S v A defSharp liftIso (taggedValueClass A U) =
      valueFactorHom M S v A defSharp liftIso (taggedValueClass A V)) : taggedValueClass A U = taggedValueClass A V := by
  classical
  have h := congrArg (rvCardinality M S) eq
  rw [degree_zero_lift_card,degree_zero_lift_card] at h
  let : Fintype (U.points A) := Fintype.ofFinite (Σ i, U.piece i)
  let : Fintype (V.points A) := Fintype.ofFinite (Σ i, V.piece i)
  simp only [ENat.card_eq_coe_fintype_card, Nat.cast_inj] at h
  let e := Fintype.equivOfCardEq h
  apply relation_sound (Relation.iso U V ⟨e,?_⟩)
  intro i j
  exact Subsingleton.set_cases (p := fun D => A.Definable J D) Set.definable_empty Set.definable_univ _

end GeneralizedEuler.Section4
