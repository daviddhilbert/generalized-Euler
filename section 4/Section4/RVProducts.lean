module

public import Section4.RectangleClasses
import all Section4.Scissors
import all Section4.FiniteScissors
import all Section4.ValueFactorMap
import all Section2.RVDefinableEquivalence

/-! Products of actual fixed-base definable bijections and products of
finite partitions. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {I J H K : Type}

def productPoints {V : Type*} (D : Set (I → V)) (E : Set (J → V)) : D × E ≃ productSet D E where
  toFun := fun x => ⟨Sum.elim x.1.val x.2.val,x.1.property,x.2.property⟩
  invFun := fun x => (⟨x.val ∘ Sum.inl,x.property.1⟩,⟨x.val ∘ Sum.inr,x.property.2⟩)
  left_inv _ := rfl
  right_inv x := Subtype.ext (funext fun i => by cases i <;> rfl)

theorem rv_product_equivalent {A : Set (I → Z .rv)} {B : Set (J → Z .rv)} {D : Set (H → Z .rv)} {E : Set (K → Z .rv)}
    (h : RVDefinablyEquivalent M S.carrier A D) (h' : RVDefinablyEquivalent M S.carrier B E) :
    RVDefinablyEquivalent M S.carrier (productSet A B) (productSet D E) := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  let e := (productPoints A B).symm.trans ((Equiv.prodCongr a b).trans (productPoints D E))
  let G₁ := {w : I ⊕ H → Z .rv | ∃ x : A, x.val = w ∘ Sum.inl ∧ (a x).val = w ∘ Sum.inr}
  let G₂ := {w : J ⊕ K → Z .rv | ∃ x : B, x.val = w ∘ Sum.inl ∧ (b x).val = w ∘ Sum.inr}
  have h₁ : isRVSet M S G₁ := ha
  have h₂ : isRVSet M S G₂ := hb
  let f : I ⊕ H → (I ⊕ J) ⊕ (H ⊕ K) := Sum.map Sum.inl Sum.inl
  let g : J ⊕ K → (I ⊕ J) ⊕ (H ⊕ K) := Sum.map Sum.inr Sum.inr
  have hg := (isRVSet_precomp f h₁).inter (isRVSet_precomp g h₂)
  refine ⟨e,?_⟩
  convert hg using 1
  ext w
  change (∃ u : productSet A B, u.val = w .rv ∘ Sum.inl ∧ (e u).val = w .rv ∘ Sum.inr) ↔
    (w .rv ∘ f ∈ G₁ ∧ w .rv ∘ g ∈ G₂)
  constructor
  · rintro ⟨u,eq,eq'⟩
    let x := (productPoints A B).symm u
    exact ⟨⟨x.1,congrArg (· ∘ Sum.inl) eq,congrArg (· ∘ Sum.inl) eq'⟩,
      ⟨x.2,congrArg (· ∘ Sum.inr) eq,congrArg (· ∘ Sum.inr) eq'⟩⟩
  · rintro ⟨⟨x,l,l'⟩,y,r,r'⟩
    exact ⟨productPoints A B (x,y),funext (fun i => by cases i with | inl j => exact congrFun l j | inr j => exact congrFun r j),
      funext (fun i => by cases i with | inl j => exact congrFun l' j | inr j => exact congrFun r' j)⟩

theorem rv_product_definable {A : Set (I → Z .rv)} {B : Set (J → Z .rv)} (ha : isRVSet M S A) (hb : isRVSet M S B) :
    isRVSet M S (productSet A B) := (isRVSet_precomp Sum.inl ha).inter (isRVSet_precomp Sum.inr hb)

theorem product_partitions {V : Type*} {A : Set (I → V)} {B : Set (J → V)}
    (a : H → Set (I → V)) (b : K → Set (J → V))
    (ha : Pairwise (fun i j => Disjoint (a i) (a j))) (hb : Pairwise (fun i j => Disjoint (b i) (b j)))
    (ca : (⋃ i, a i) = A) (cb : (⋃ j, b j) = B) :
    Pairwise (fun i j : H × K => Disjoint (productSet (a i.1) (b i.2)) (productSet (a j.1) (b j.2))) ∧
    (⋃ i : H × K, productSet (a i.1) (b i.2)) = productSet A B := by
  constructor
  · intro i j ne
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact ne (Prod.ext (by by_contra h; exact Set.disjoint_left.mp (ha h) hi.1 hj.1)
      (by by_contra h; exact Set.disjoint_left.mp (hb h) hi.2 hj.2))
  · ext x
    rw [Set.mem_iUnion,← ca,← cb]
    change _ ↔ (x ∘ Sum.inl ∈ ⋃ i, a i) ∧ (x ∘ Sum.inr ∈ ⋃ j, b j)
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i,h⟩ => ⟨⟨_,h.1⟩,⟨_,h.2⟩⟩,fun ⟨⟨i,hi⟩,j,hj⟩ => ⟨(i,j),hi,hj⟩⟩

end GeneralizedEuler.Section4
