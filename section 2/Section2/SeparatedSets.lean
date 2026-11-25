module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Set.Finite.Basic

/-! Boolean combinations and projections of residue and value conditions
in the proof of Lemma 2.29. -/

public section

namespace GeneralizedEuler.Section2

/-- A finite union of rectangles whose factors satisfy the given predicates.
The predicates can record definability in the two reducts over fixed parameters. -/
inductive SeparatedSets {A B : Type*} (left : Set A → Prop) (right : Set B → Prop) :
    Set (A × B) → Prop where
  | empty : SeparatedSets left right ∅
  | insert {U V D} : left U → right V → SeparatedSets left right D →
      SeparatedSets left right ((U ×ˢ V) ∪ D)

namespace SeparatedSets

variable {A B : Type*} {left : Set A → Prop} {right : Set B → Prop}
  {D F : Set (A × B)}

theorem rect {U V} (hU : left U) (hV : right V) : SeparatedSets left right (U ×ˢ V) := by
  simpa only [Set.union_empty] using insert hU hV empty

theorem univ (hU : left Set.univ) (hV : right Set.univ) :
    SeparatedSets left right Set.univ := by
  simpa only [Set.univ_prod_univ] using rect hU hV

theorem union (hD : SeparatedSets left right D) (hF : SeparatedSets left right F) :
    SeparatedSets left right (D ∪ F) := by
  induction hD with
  | empty => simpa only [Set.empty_union] using hF
  | insert hU hV _ ih =>
    rw [Set.union_assoc]
    exact insert hU hV ih

theorem inter (hleft : ∀ {U U'}, left U → left U' → left (U ∩ U'))
    (hright : ∀ {V V'}, right V → right V' → right (V ∩ V'))
    (hD : SeparatedSets left right D) (hF : SeparatedSets left right F) :
    SeparatedSets left right (D ∩ F) := by
  have interRect {U V} (hU : left U) (hV : right V) :
      SeparatedSets left right ((U ×ˢ V) ∩ F) := by
    induction hF with
    | empty => simpa only [Set.inter_empty] using (empty (left := left) (right := right))
    | insert hU' hV' _ ih =>
      rw [Set.inter_union_distrib_left, Set.prod_inter_prod]
      exact insert (hleft hU hU') (hright hV hV') ih
  induction hD with
  | empty => simpa only [Set.empty_inter] using (empty (left := left) (right := right))
  | insert hU hV _ ih =>
    rw [Set.union_inter_distrib_right]
    exact (interRect hU hV).union ih

theorem compl (hU : left Set.univ) (hV : right Set.univ)
    (hleft : ∀ {U}, left U → left Uᶜ) (hright : ∀ {V}, right V → right Vᶜ)
    (hleftInter : ∀ {U U'}, left U → left U' → left (U ∩ U'))
    (hrightInter : ∀ {V V'}, right V → right V' → right (V ∩ V'))
    (hD : SeparatedSets left right D) : SeparatedSets left right Dᶜ := by
  induction hD with
  | empty => simpa only [Set.compl_empty] using univ hU hV
  | insert hA hB _ ih =>
    rw [Set.compl_union, Set.compl_prod_eq_union]
    exact inter hleftInter hrightInter
      ((rect (hleft hA) hV).union (rect hU (hright hB))) ih

/-- Projection on either factor is the image under a product map with
identity on the other factor. -/
theorem image {A' B' : Type*} {left' : Set A' → Prop} {right' : Set B' → Prop}
    (f : A → A') (g : B → B')
    (hf : ∀ {U}, left U → left' (f '' U)) (hg : ∀ {V}, right V → right' (g '' V))
    (hD : SeparatedSets left right D) : SeparatedSets left' right' (Prod.map f g '' D) := by
  induction hD with
  | empty => simpa only [Set.image_empty] using (empty (left := left') (right := right'))
  | insert hU hV _ ih =>
    rw [Set.image_union, Set.prodMap_image_prod]
    exact insert (hf hU) (hg hV) ih

theorem preimage {A' B' : Type*} {left' : Set A' → Prop} {right' : Set B' → Prop}
    (f : A' → A) (g : B' → B)
    (hf : ∀ {U}, left U → left' (f ⁻¹' U)) (hg : ∀ {V}, right V → right' (g ⁻¹' V))
    (hD : SeparatedSets left right D) : SeparatedSets left' right' (Prod.map f g ⁻¹' D) := by
  induction hD with
  | empty => simpa only [Set.preimage_empty] using (empty (left := left') (right := right'))
  | @insert U V D hU hV _ ih =>
    rw [Set.preimage_union]
    change SeparatedSets left' right' (((f ⁻¹' U) ×ˢ (g ⁻¹' V)) ∪ Prod.map f g ⁻¹' D)
    exact insert (hf hU) (hg hV) ih

/-- A functional relation that is a finite union of rectangles has finite
image. Each nonempty rectangle contributes at most one value. -/
theorem finite_snd_of_functional (hD : SeparatedSets left right D)
    (hfun : ∀ ⦃a b b'⦄, (a, b) ∈ D → (a, b') ∈ D → b = b') : (Prod.snd '' D).Finite := by
  induction hD with
  | empty => rw [Set.image_empty]; exact Set.finite_empty
  | @insert U V D _ _ _ ih =>
    rw [Set.image_union]
    apply Set.Finite.union _ (ih (by
      intro a b b' h h'
      exact hfun (Or.inr h) (Or.inr h')))
    rcases U.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [Set.empty_prod, Set.image_empty]
      exact Set.finite_empty
    · have hV : V.Subsingleton := fun b hb b' hb' => hfun (Or.inl ⟨ha, hb⟩) (Or.inl ⟨ha, hb'⟩)
      exact hV.finite.subset (by rintro _ ⟨⟨_, _⟩, h, rfl⟩; exact h.2)

/-- The same finite-image argument for a function in the opposite direction. -/
theorem finite_fst_of_functional (hD : SeparatedSets left right D)
    (hfun : ∀ ⦃a a' b⦄, (a, b) ∈ D → (a', b) ∈ D → a = a') : (Prod.fst '' D).Finite := by
  induction hD with
  | empty => rw [Set.image_empty]; exact Set.finite_empty
  | @insert U V D _ _ _ ih =>
    rw [Set.image_union]
    apply Set.Finite.union _ (ih (by
      intro a a' b h h'
      exact hfun (Or.inr h) (Or.inr h')))
    rcases V.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · rw [Set.prod_empty, Set.image_empty]
      exact Set.finite_empty
    · have hU : U.Subsingleton := fun a ha a' ha' => hfun (Or.inl ⟨ha, hb⟩) (Or.inl ⟨ha', hb⟩)
      exact hU.finite.subset (by rintro _ ⟨⟨_, _⟩, h, rfl⟩; exact h.1)

/-- Evaluating the second coordinates at a fixed tuple retains only the
first reduct's conditions. This is used with the tuple of residue units. -/
theorem slice (hEmpty : left ∅) (hUnion : ∀ {U U'}, left U → left U' → left (U ∪ U'))
    (b : B) (hD : SeparatedSets left right D) : left ((fun a => (a, b)) ⁻¹' D) := by
  induction hD with
  | empty => simpa only [Set.preimage_empty] using hEmpty
  | @insert U V D hU _ _ ih =>
    rw [Set.preimage_union]
    by_cases hb : b ∈ V
    · rw [Set.mk_preimage_prod_left hb]
      exact hUnion hU ih
    · rw [Set.mk_preimage_prod_left_eq_empty hb, Set.empty_union]
      exact ih

end SeparatedSets

end GeneralizedEuler.Section2
