module

public import Section4.ValuePullback
import all Section4.Objects
import all Section2.RVDefinableEquivalence

/-! Finite disjoint unions in the concrete RV semiring and its residue
subcategory. Restrictions inherit the original finite-to-one label. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  {M : SortedStructure L E Z} {S : SortedSubstructure M} {k : ℕ}

theorem isRVSet_precomp {I J : Type} (p : I → J) {D : Set (I → Z .rv)} (hd : isRVSet M S D) :
    isRVSet M S {x : J → Z .rv | x ∘ p ∈ D} := by
  let f : ∀ s, RVVariables I s → RVVariables J s
    | .vf => PEmpty.elim
    | .rv => p
  exact hd.pullback_relabel f

theorem isRVSet_iUnion {I J : Type} [Finite J] {D : J → Set (I → Z .rv)}
    (hd : ∀ i, isRVSet M S (D i)) : isRVSet M S (⋃ i, D i) := by
  unfold isRVSet
  convert SortedDefinableOver.iUnion hd using 1
  ext x; simp

theorem isRVSet_inter {I : Type} {A B : Set (I → Z .rv)}
    (ha : isRVSet M S A) (hb : isRVSet M S B) : isRVSet M S (A ∩ B) := ha.inter hb

namespace RVObject
variable (U : RVObject M S k) {A : Set (Fin U.arity → Z .rv)}

def restrict (sub : A ⊆ U.carrier) (ha : isRVSet M S A) : RVObject M S k where
  arity := U.arity
  carrier := A
  definable := ha
  label x := U.label ⟨x.val,sub x.property⟩
  graph := by
    let D := {x : ∀ s, RVVariables (Fin U.arity ⊕ Fin k) s → Z s | x .rv ∘ Sum.inl ∈ A}
    have hd : SortedDefinableOver M S.carrier D := isRVSet_precomp Sum.inl ha
    convert hd.inter U.graph using 1
    ext x
    change (∃ a : A, a.val = x .rv ∘ Sum.inl ∧ U.label _ = x .rv ∘ Sum.inr) ↔
      x .rv ∘ Sum.inl ∈ A ∧ ∃ a : U.carrier, a.val = x .rv ∘ Sum.inl ∧ U.label a = x .rv ∘ Sum.inr
    constructor
    · rintro ⟨a,ea,ef⟩; exact ⟨ea ▸ a.property,⟨a.val,sub a.property⟩,ea,ef⟩
    · rintro ⟨hx,a,ea,ef⟩; exact ⟨⟨a.val,ea.symm ▸ hx⟩,ea,ef⟩
  nonzero x := U.nonzero ⟨x.val,sub x.property⟩
  finiteFibers y := by
    let f (x : A) : U.carrier := ⟨x.val,sub x.property⟩
    have inj : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun z : U.carrier => z.val) h)
    change (f ⁻¹' (U.label ⁻¹' {y})).Finite
    exact (U.finiteFibers y).preimage inj.injOn

theorem restrict_residue {Γ : Type*} (v : Z .rv → Γ) (h : U.IsResidue M S v)
    (sub : A ⊆ U.carrier) (ha : isRVSet M S A) : (U.restrict sub ha).IsResidue M S v := by
  apply h.subset
  rintro _ ⟨x,rfl⟩
  exact ⟨⟨x.val,sub x.property⟩,rfl⟩

end RVObject

/-- The same induction works in RV and RES. Every class equality in the
induction uses only empty sets and binary definable cuts. -/
theorem finite_scissor_sum {I : Type} [Fintype I] {X T : Type*} [AddCommMonoid T]
    {P : Set X → Prop} (b : ∀ A, P A → T) (empty : P ∅) (zero : b ∅ empty = 0)
    (union : ∀ {A B}, P A → P B → P (A ∪ B))
    (cut : ∀ A B (ha : P A) (hb : P B), Disjoint A B →
      b (A ∪ B) (union ha hb) = b A ha + b B hb)
    (A : I → Set X) (ha : ∀ i, P (A i)) (disj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∃ hu : P (⋃ i, A i), b (⋃ i, A i) hu = ∑ i, b (A i) (ha i) := by
  classical
  have go (t : Finset I) : ∃ h : P (⋃ i ∈ t, A i), b _ h = ∑ i ∈ t, b (A i) (ha i) := by
    induction t using Finset.induction_on with
    | empty => simpa using ⟨empty,zero⟩
    | insert i t hi ih =>
      obtain ⟨h,eq⟩ := ih
      simp only [Finset.set_biUnion_insert,Finset.sum_insert hi]
      refine ⟨union (ha i) h,(cut _ _ _ _ ?_).trans (congrArg (b (A i) (ha i) + ·) eq)⟩
      exact Set.disjoint_iUnion_right.mpr fun j => Set.disjoint_iUnion_right.mpr fun hj =>
        disj (fun he => hi (he ▸ hj))
  simpa using go Finset.univ

theorem objectClass_partition (U : RVObject M S k) {I : Type} [Fintype I]
    (A : I → Set (Fin U.arity → Z .rv)) (ha : ∀ i, isRVSet M S (A i))
    (disj : Pairwise (fun i j => Disjoint (A i) (A j))) (cover : ⋃ i, A i = U.carrier) :
    objectClass M S ⟨k,U⟩ = ∑ i, objectClass M S
      ⟨k,U.restrict (cover ▸ Set.subset_iUnion A i) (ha i)⟩ := by
  let P (D : Set (Fin U.arity → Z .rv)) := D ⊆ U.carrier ∧ isRVSet M S D
  let b (D) (h : P D) := objectClass M S ⟨k,U.restrict h.1 h.2⟩
  have h0 : P ∅ := ⟨Set.empty_subset _,⟨.falsum,fun _ => Iff.rfl⟩⟩
  have add {D E} (hD : P D) (hE : P E) : P (D ∪ E) :=
    ⟨Set.union_subset hD.1 hE.1,hD.2.union hE.2⟩
  have cut (D E) (hD : P D) (hE : P E) (h : Disjoint D E) :
      b (D ∪ E) (add hD hE) = b D hD + b E hE := by
    apply scissors_sound M S
    exact RVRelation.cut _ _ _ D E hD.2 hE.2 h rfl
      ⟨Equiv.refl _,definable_identity_label M S hD.2⟩
      ⟨Equiv.refl _,definable_identity_label M S hE.2⟩
  obtain ⟨h,eq⟩ := finite_scissor_sum b h0
    (scissors_sound M S (RVRelation.zero (U.restrict h0.1 h0.2) rfl)) @add cut A
    (fun i => ⟨cover ▸ Set.subset_iUnion A i,ha i⟩) disj
  apply Eq.trans _ eq
  apply scissors_sound M S
  apply RVRelation.iso
  change RVDefinablyEquivalent M S.carrier U.carrier (⋃ i, A i)
  rw [cover]
  exact ⟨Equiv.refl _,definable_identity_label M S U.definable⟩

end GeneralizedEuler.Section4
