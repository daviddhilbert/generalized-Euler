module

public import Section5.UnaryChainRules
import all Section5.RelativeUnaryShears

/-! The coordinate exchange in the factorization is a fixed-base
composition of three unary field updates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {I : Type}

@[expose] def fieldEquivAssignment (e : (Fin n → X .vf) ≃ (Fin n → X .vf))
    (x : SortedAssignment X (MixedVariables n I)) : SortedAssignment X (MixedVariables n I)
  | .vf => e (x .vf)
  | .rv => x .rv

theorem fieldEquivAssignment_injective (e : (Fin n → X .vf) ≃ (Fin n → X .vf)) :
    Function.Injective (fieldEquivAssignment (I := I) e) := by
  intro x y eq
  funext s j
  cases s
  · exact congrFun (e.injective (congrFun eq .vf)) j
  · exact congrFun (congrFun eq .rv) j

@[expose] def fieldEquivOnSet
    (D : MixedCarrier X n I) (defD : SortedDefinableOver M S.carrier D)
    (e : (Fin n → X .vf) ≃ (Fin n → X .vf))
    (defE : DefinableRelation M S.carrier (fun (x y : SortedAssignment X (MixedVariables n I)) =>
      e (x .vf) = y .vf ∧ x .rv = y .rv)) :
    MixedGraphIso M S D (Set.range (fun x : D => fieldEquivAssignment e x.val)) :=
  MixedGraphIso.toRange _ ((fieldEquivAssignment_injective e).comp Subtype.val_injective)
    ((defE.inter_left defD).congr (fun x y => by
      constructor
      · rintro ⟨⟨h,g⟩,mem⟩
        refine ⟨mem,?_⟩
        funext s j
        cases s
        · exact congrFun h j
        · exact congrFun g j
      · rintro ⟨mem,e⟩
        exact ⟨⟨congrFun e .vf,congrFun e .rv⟩,mem⟩))

theorem fieldEquivOnSet_apply
    (D : MixedCarrier X n I) (defD : SortedDefinableOver M S.carrier D)
    (e : (Fin n → X .vf) ≃ (Fin n → X .vf))
    (defE : DefinableRelation M S.carrier (fun (x y : SortedAssignment X (MixedVariables n I)) =>
      e (x .vf) = y .vf ∧ x .rv = y .rv)) (x : D) :
    ((fieldEquivOnSet D defD e defE).equiv x).val = fieldEquivAssignment e x.val := rfl

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Y" => CanonicalSort O

theorem unary_piecewise_swap
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : MixedCarrier Y n I) (defD : SortedDefinableOver 𝓜 S₀.carrier D)
    (moving : Finset (Fin n)) (i j : Fin n) (hi : i ∈ moving) (hj : j ∈ moving) :
    ∃ (B : MixedCarrier Y n I) (f : MixedGraphIso 𝓜 S₀ D B),
      UnaryPiecewise 𝓜 S₀ n moving f ∧ ∀ a : D,
        (f.equiv a).val .vf = a.val .vf ∘ Equiv.swap i j ∧ (f.equiv a).val .rv = a.val .rv := by
  by_cases eq : i = j
  · have g := (DefinableRelation.diagonal (M := 𝓜) (A := S₀.carrier)
      (U := MixedVariables n I)).inter_left defD
    let f : MixedGraphIso 𝓜 S₀ D D := ⟨Equiv.refl D,g.congr (fun a b => by
      exact ⟨fun ⟨e,h⟩ => ⟨h,e⟩,fun ⟨h,e⟩ => ⟨e,h⟩⟩)⟩
    exact ⟨D,f,.fixed f (fun _ _ _ => rfl),fun a => by simp [f,eq]⟩
  let plus := addCoordinate (K := K) i j (Ne.symm eq)
  let reflect := reflectCoordinate (K := K) j i eq
  let minus := plus.symm
  let Δ := SortedAssignment Y (MixedVariables n I)
  have g₁ := fieldAddUpdate_definable O hO power S₀ (I := I) i j (Ne.symm eq) F minusOne hm hF
  have g₂ : DefinableRelation 𝓜 S₀.carrier (fun (x y : Δ) =>
      reflect (x .vf) = y .vf ∧ x .rv = y .rv) :=
    fieldSubtractionUpdates_definable O hO power S₀ j i F minusOne hm hF true
  have g₃ : DefinableRelation 𝓜 S₀.carrier (fun (x y : Δ) =>
      minus (x .vf) = y .vf ∧ x .rv = y .rv) :=
    fieldSubtractionUpdates_definable O hO power S₀ i j F minusOne hm hF false
  let f₁ := fieldEquivOnSet D defD plus g₁
  let f₂ := fieldEquivOnSet _ (f₁.target_definable defD) reflect g₂
  let f₃ := fieldEquivOnSet _ (f₂.target_definable (f₁.target_definable defD)) minus g₃
  have h₁ : UnaryPiecewise 𝓜 S₀ n moving f₁ := .unary f₁ i hi (by
    intro a l nl
    exact Function.update_of_ne (fun h => nl (Finset.mem_singleton.2 h)) _ _)
  have h₂ : UnaryPiecewise 𝓜 S₀ n moving f₂ := .unary f₂ j hj (by
    intro a l nl
    exact Function.update_of_ne (fun h => nl (Finset.mem_singleton.2 h)) _ _)
  have h₃ : UnaryPiecewise 𝓜 S₀ n moving f₃ := .unary f₃ i hi (by
    intro a l nl
    exact Function.update_of_ne (fun h => nl (Finset.mem_singleton.2 h)) _ _)
  refine ⟨_,(f₁.trans f₂).trans f₃,.trans (.trans h₁ h₂) h₃,?_⟩
  intro a
  refine ⟨?_,rfl⟩
  exact (transposition_by_relatively_unary (A := I → RV0 O) i j eq).2.2.2 (a.val .vf)

end GeneralizedEuler.Section5
