module

public import Section5.RelativeTranslation

/-! Coordinate form of a relative centripetal transformation. The
selected coordinate can be anywhere in a finite tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

abbrev PreparationPoint (F I : Type*) := (F → K) × (I → RV0 O)

variable {F I : Type*}

/-- Split off a single coordinate of a tuple and keep the others in
their original order and indexing. -/
@[expose] def splitCoordinate {A : Type*} (i : F) :
    (F → A) ≃ ({j : F // j ≠ i} → A) × A := by
  classical
  exact {
    toFun := fun a => (fun j => a j.val, a i)
    invFun := fun p j => if h : j = i then p.2 else p.1 ⟨j,h⟩
    left_inv := by intro a; funext j; by_cases h : j = i <;> simp [h]
    right_inv := by
      intro p
      refine Prod.ext ?_ (by simp)
      funext j
      simp [j.property] }

@[expose] def coordinateBaseLabel (i : F) :
    (({j : F // j ≠ i} → K) × (I → RV0 O)) →
      (({j : F // j ≠ i} → RV0 O) × (I → RV0 O)) :=
  Prod.map (fun a => rv O ∘ a) id

structure CoordinatePreparation (F I : Type*) where
  coord : F
  translation : RelativeTranslation O (coordinateBaseLabel (I := I) O coord)

namespace CoordinatePreparation

variable {O} (T : CoordinatePreparation O F I)

@[expose] def splitSource :
    PreparationPoint O F I ≃ (({j : F // j ≠ T.coord} → K) × (I → RV0 O)) × K where
  toFun p := (((splitCoordinate T.coord p.1).1, p.2), (splitCoordinate T.coord p.1).2)
  invFun p := ((splitCoordinate T.coord).symm (p.1.1, p.2), p.1.2)
  left_inv p := by simp
  right_inv p := by simp

@[expose] def packTarget :
    (({j : F // j ≠ T.coord} → K) × (I → RV0 O)) × (K × RV0 O) ≃
      PreparationPoint O F (Option I) where
  toFun p := ((splitCoordinate T.coord).symm (p.1.1, p.2.1), fun i => i.elim p.2.2 p.1.2)
  invFun p := (((splitCoordinate T.coord p.1).1, p.2 ∘ some),
    (splitCoordinate T.coord p.1).2, p.2 none)
  left_inv p := by
    simp
    rfl
  right_inv p := by
    apply Prod.ext
    · simp
    · funext i; cases i <;> rfl

/-- A stage translates one field coordinate, keeps the original RV tuple,
and adjoins the previous leading term of the translated coordinate. -/
@[expose] def map (p : PreparationPoint O F I) : PreparationPoint O F (Option I) :=
  T.packTarget (T.translation.map (T.splitSource p))

theorem map_injective : Function.Injective T.map :=
  T.packTarget.injective.comp (T.translation.map_injective.comp T.splitSource.injective)

theorem old_aux (p : PreparationPoint O F I) (i : I) : (T.map p).2 (some i) = p.2 i := rfl

theorem old_lead (p : PreparationPoint O F I) : (T.map p).2 none = rv O (p.1 T.coord) := rfl

theorem untouched (p : PreparationPoint O F I) {j : F} (hj : j ≠ T.coord) :
    (T.map p).1 j = p.1 j := by
  classical
  simp [map, packTarget, splitSource, RelativeTranslation.map, splitCoordinate, hj]

/-- The inverse of target packing exposes the new field coordinate, the
old leading term and all unchanged coordinates. The pullback equation
is exactly the one-coordinate image equation in these variables. -/
theorem image_in_coordinates (A : Set ((({j : F // j ≠ T.coord} → RV0 O) × (I → RV0 O)) × RV0 O))
    (hfocus : ∀ x t, (coordinateBaseLabel O T.coord x, t) ∈ A →
      (coordinateBaseLabel O T.coord x, t) ∈ T.translation.locus →
      t ≠ 0 ∧ rv O (T.translation.focus x t) = t) :
    T.map '' {p | (coordinateBaseLabel O T.coord (T.splitSource p).1,
        rv O (T.splitSource p).2) ∈ A} =
      T.packTarget '' {b | (coordinateBaseLabel O T.coord b.1, b.2.2) ∈ A ∧
        (((coordinateBaseLabel O T.coord b.1, b.2.2) ∈ T.translation.locus ∧
            unsignedValue O (rv O b.2.1) < unsignedValue O b.2.2) ∨
          ((coordinateBaseLabel O T.coord b.1, b.2.2) ∉ T.translation.locus ∧
            rv O b.2.1 = b.2.2))} := by
  have h := T.translation.image_pullback A hfocus
  let B := {a : (({j : F // j ≠ T.coord} → K) × (I → RV0 O)) × K |
    (coordinateBaseLabel O T.coord a.1, rv O a.2) ∈ A}
  have e : T.splitSource '' (T.splitSource ⁻¹' B) = B :=
    Set.image_preimage_eq _ T.splitSource.surjective
  change (T.packTarget ∘ T.translation.map ∘ T.splitSource) '' (T.splitSource ⁻¹' B) = _
  calc
    _ = T.packTarget '' (T.translation.map '' (T.splitSource '' (T.splitSource ⁻¹' B))) := by
      simp only [Set.image_image, Function.comp_def]
    _ = _ := by rw [e, h]

end CoordinatePreparation

end GeneralizedEuler.Section5
