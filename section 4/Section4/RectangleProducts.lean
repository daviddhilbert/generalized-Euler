module

public import Section4.RVProducts
public import Section4.ResidueProducts
import all Section4.ValueFactorMap
import all Section4.ValueScissors
import all Section4.Scissors
import all Section4.RectangleClasses
import all Section4.CanonicalChartMaps

/-! Regrouping the residue coordinates and the value coordinates in a
product of two rectangles is a fixed-base coordinate permutation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}

def swapMiddle (I J H K : Type) : (I ⊕ H) ⊕ (J ⊕ K) ≃ (I ⊕ J) ⊕ (H ⊕ K) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr h) => .inr (.inl h)
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr k) => .inr (.inr k)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr j) => .inr (.inl j)
    | .inr (.inl h) => .inl (.inr h)
    | .inr (.inr k) => .inr (.inr k)
  left_inv := fun t => by rcases t with (i|h)|(j|k) <;> rfl
  right_inv := fun t => by rcases t with (i|j)|(h|k) <;> rfl

theorem productSet_shuffle {I J H K : Type} [Finite I] [Finite J] [Finite H] [Finite K]
    {A : Set (I → Z .rv)} {B : Set (J → Z .rv)} {C : Set (H → Z .rv)} {D : Set (K → Z .rv)}
    (ha : isRVSet M S A) (hb : isRVSet M S B) (hc : isRVSet M S C) (hd : isRVSet M S D) :
    RVDefinablyEquivalent M S.carrier (productSet (productSet A B) (productSet C D))
      (productSet (productSet A C) (productSet B D)) := by
  let X := productSet (productSet A B) (productSet C D)
  let Y := productSet (productSet A C) (productSet B D)
  have eq : {t | t ∘ (swapMiddle I J H K).symm ∈ X} = Y := Set.ext fun _ =>
    ⟨fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩,fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩⟩
  rw [← show {t | t ∘ (swapMiddle I J H K).symm ∈ X} = productSet (productSet A C) (productSet B D) from eq]
  exact rv_reindex_equivalent M S _ X (rv_product_definable (rv_product_definable ha hb) (rv_product_definable hc hd))

theorem productSet_cartesian {n m} {A : Set (Fin n → Z .rv)} {B : Set (Fin m → Z .rv)}
    (ha : isRVSet M S A) (hb : isRVSet M S B) :
    RVDefinablyEquivalent M S.carrier (productSet A B) (cartesian A B) :=
  rv_reindex_equivalent M S finSumFinEquiv.symm _ (rv_product_definable ha hb)

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)

theorem positiveSharp_product {n m} (D : Set (Fin n → Additive O.ValueGroupˣ)) (B : Set (Fin m → Additive O.ValueGroupˣ)) :
    positiveSharp O v (cartesian D B) = cartesian (positiveSharp O v D) (positiveSharp O v B) := by
  let l := finSumFinEquiv (m := n) (n := m) ∘ Sum.inl
  let r := finSumFinEquiv (m := n) (n := m) ∘ Sum.inr
  ext x; constructor
  · rintro ⟨z,h,rfl⟩; exact ⟨⟨z ∘ l,h.1,rfl⟩,z ∘ r,h.2,rfl⟩
  · rintro ⟨⟨z,hz,ez⟩,w,hw,ew⟩
    let t := Sum.elim z w ∘ finSumFinEquiv.symm
    have L : t ∘ l = z := funext fun i => by simp [t,l,Function.comp_def]
    have R : t ∘ r = w := funext fun i => by simp [t,r,Function.comp_def]
    refine ⟨t,⟨(congrArg (fun y => v ∘ y ∈ D) L).mpr hz,(congrArg (fun y => v ∘ y ∈ B) R).mpr hw⟩,?_⟩
    funext i; obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective i
    cases a with
    | inl i => exact (congrArg (fun y : Fin n → Additive (PositiveRV O) => codeTuple O y i) L).trans (congrFun ez i)
    | inr j => exact (congrArg (fun y : Fin m → Additive (PositiveRV O) => codeTuple O y j) R).trans (congrFun ew j)

end GeneralizedEuler.Section4
