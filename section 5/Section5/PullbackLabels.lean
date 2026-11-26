module

public import Section5.PreparedGraphContraction

/-! The labels of a mixed object are finite-to-one over the tuple of
field leading terms, once the object is prepared as a pullback. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

variable {K : Type*} [Field K] {O : ValuationSubring K}
  {F I : Type*}

theorem labeled_pullback_finite_over_lead
    (A : Set (PreparationPoint O F I))
    (whole : ∀ x y, preparationLabel x = preparationLabel y → (x ∈ A ↔ y ∈ A))
    (finite : ∀ a, {t | (a,t) ∈ A}.Finite) (s : F → RV0 O) :
    {t | (s,t) ∈ preparationLabel '' A}.Finite := by
  classical
  let a (j : F) := (rv_surjective O (s j)).choose
  have ha : rv O ∘ a = s := funext fun j => (rv_surjective O (s j)).choose_spec
  apply (finite a).subset
  rintro t ⟨p,hp,he⟩
  have hb : preparationLabel (O := O) (a,t) = (s,t) := Prod.ext ha rfl
  exact (whole p (a,t) (he.trans hb.symm)).1 hp

namespace PreparedMap

variable {L : Language} {E : Type*} {M : SortedStructure L E (CanonicalSort O)}
  {S : SortedSubstructure M} {n : ℕ} {I J : Type}
  {G : PointTests O n I J}

theorem domain_image_finite_fibers (P : PreparedMap M S G)
    (hf : ∀ a, {t | (a,t) ∈ testDomain G}.Finite) (a : Fin n → K) :
    {s | (a,s) ∈ P.map '' testDomain G}.Finite :=
  P.finiteFieldPreimages.image_finite_fibers _ hf a

theorem domain_labels_finite_over_lead (P : PreparedMap M S G)
    (hf : ∀ a, {t | (a,t) ∈ testDomain G}.Finite) (s : Fin n → RV0 O) :
    {t | (s,t) ∈ preparationLabel '' (P.map '' testDomain G)}.Finite :=
  labeled_pullback_finite_over_lead _ P.domain_image_whole (P.domain_image_finite_fibers hf) s

end PreparedMap

end GeneralizedEuler.Section5
