module

public import Mathlib.Data.Set.Prod

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
