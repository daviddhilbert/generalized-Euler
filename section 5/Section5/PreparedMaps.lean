module

public import Section5.DefinableRelations
public import Section5.FiniteFieldPreimages

/-! Fixed-base data passed between the arity-induction steps. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type}

/-- Read all leading terms and all auxiliary coordinates of a point. -/
@[expose] def preparationLabel {F R : Type*} (p : PreparationPoint O F R) :
    (F → RV0 O) × (R → RV0 O) :=
  (rv O ∘ p.1, p.2)

/-- A finite-arity map between field and RV tuples, definable over the
original base. It is used for graph composition and transport. -/
@[expose] def PointMapDefinable {m n : ℕ} {P Q : Type}
    (M : SortedStructure L E (CanonicalSort O)) (S : SortedSubstructure M)
    (f : PreparationPoint O (Fin m) P → PreparationPoint O (Fin n) Q) : Prop :=
  DefinableRelation M S.carrier
    (fun a : SortedAssignment (CanonicalSort O) (MixedVariables m P) =>
      fun b : SortedAssignment (CanonicalSort O) (MixedVariables n Q) =>
        f (mixedTuple a) = mixedTuple b)

/-- The induction keeps the original RV tuple in specified output slots.
A single map prepares all tests (t), including external RV parameters
that never form part of the map's input. -/
structure PreparedMap
    (M : SortedStructure L E (CanonicalSort O)) (S : SortedSubstructure M)
    (G : Set (PreparationPoint O (Fin n) I × (J → RV0 O))) where
  tags : Type
  finiteTags : Finite tags
  oldIndex : I ↪ tags
  map : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) tags
  injective : Function.Injective map
  definable : PointMapDefinable M S map
  oldAux : ∀ p i, (map p).2 (oldIndex i) = p.2 i
  whole : ∀ p q, preparationLabel p = preparationLabel q →
    (p ∈ Set.range map ↔ q ∈ Set.range map)
  tests : ∀ p q, preparationLabel (map p) = preparationLabel (map q) →
    ∀ t, (p,t) ∈ G ↔ (q,t) ∈ G
  finiteFieldPreimages : FiniteFieldPreimages map

theorem mixedTuple_injective :
    Function.Injective (mixedTuple (X := CanonicalSort O) (n := n) (R := I)) := by
  intro a b he
  funext s i
  cases s with
  | vf => exact congrFun (congrArg Prod.fst he) i
  | rv => exact congrFun (congrArg Prod.snd he) i

namespace PreparedMap

/-- The map in field arity zero is the identity. Every fiber of the full
RV label is already a point. -/
@[expose] def zero [Finite I] (G : Set (PreparationPoint O (Fin 0) I × (J → RV0 O))) :
    PreparedMap M S G where
  tags := I
  finiteTags := inferInstance
  oldIndex := Function.Embedding.refl I
  map := id
  injective := fun _ _ h => h
  definable := by
    exact (DefinableRelation.diagonal (M := M) (A := S.carrier) (U := MixedVariables 0 I)).congr
      (fun _ _ => ⟨fun h => congrArg mixedTuple h, fun h => mixedTuple_injective h⟩)
  oldAux _ _ := rfl
  whole p q _ := by simp
  tests p q h t := by
    have hv : p.1 = q.1 := Subsingleton.elim _ _
    change preparationLabel p = preparationLabel q at h
    have hr : p.2 = q.2 := congrArg (fun v : (Fin 0 → RV0 O) × (I → RV0 O) => v.2) h
    rw [Prod.ext hv hr]
  finiteFieldPreimages := FiniteFieldPreimages.id

/-- Restricting the map to any represented output test gives an
RV-pullback, using the ambient image and test constancy together. -/
theorem test_image_whole {G : Set (PreparationPoint O (Fin n) I × (J → RV0 O))}
    (P : PreparedMap M S G) (t : J → RV0 O) {a b : PreparationPoint O (Fin n) P.tags}
    (he : preparationLabel a = preparationLabel b) :
    a ∈ P.map '' {p | (p,t) ∈ G} ↔ b ∈ P.map '' {p | (p,t) ∈ G} := by
  have step (u v : PreparationPoint O (Fin n) P.tags)
      (h : preparationLabel u = preparationLabel v)
      (hu : u ∈ P.map '' {p | (p,t) ∈ G}) : v ∈ P.map '' {p | (p,t) ∈ G} := by
    obtain ⟨p, hp, hpu⟩ := hu
    obtain ⟨q,hqv⟩ := (P.whole u v h).1 ⟨p,hpu⟩
    have eq : preparationLabel (P.map p) = preparationLabel (P.map q) :=
      (congrArg preparationLabel hpu).trans (h.trans (congrArg preparationLabel hqv).symm)
    exact ⟨q, (P.tests p q eq t).1 hp, hqv⟩
  exact ⟨step a b he, step b a he.symm⟩

end PreparedMap

end GeneralizedEuler.Section5
