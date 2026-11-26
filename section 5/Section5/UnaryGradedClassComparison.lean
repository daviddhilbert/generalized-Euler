module

public import Section5.UnaryLabelObjects
public import Section5.InjectiveObjectLifts
import all Section4.Objects

/-! Cut the unary label isomorphism at the zero leading term and
compare the scissor classes in each degree. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

section RVCut

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {I J : Type} {A : Set (I → X .rv)} {B : Set (J → X .rv)}

theorem rvDefinableEquiv_of_preserved_cut (f : A ≃ B)
    (graph : SortedDefinableOver M S.carrier (rvGraph fun a => (f a).val))
    (P : (I → X .rv) → Prop) (Q : (J → X .rv) → Prop)
    (preserve : ∀ a : A, P a.val ↔ Q (f a).val)
    (defCut : isRVSet M S {a ∈ A | P a}) :
    RVDefinablyEquivalent M S.carrier {a ∈ A | P a} {b ∈ B | Q b} := by
  let e : {a ∈ A | P a} ≃ {b ∈ B | Q b} :=
    { toFun := fun a =>
        let x := f ⟨a.val,a.property.1⟩
        ⟨x.val,x.property,(preserve _).1 a.property.2⟩
      invFun := fun b =>
        let x := f.symm ⟨b.val,b.property.1⟩
        ⟨x.val,x.property,(preserve x).2 (by rw [f.apply_symm_apply]; exact b.property.2)⟩
      left_inv := fun a => Subtype.ext (congrArg (fun x : A => x.val) (f.symm_apply_apply ⟨a.val,a.property.1⟩))
      right_inv := fun b => Subtype.ext (congrArg (fun y : B => y.val) (f.apply_symm_apply ⟨b.val,b.property.1⟩)) }
  refine ⟨e,rvGraph_of_relation (((ObjectLift.relation_of_rvGraph graph).inter_left defCut).congr ?_)⟩
  intro a b
  constructor
  · rintro ⟨⟨x,hx,hy⟩,ha⟩
    have eq : (⟨a .rv,ha.1⟩ : A) = x := Subtype.ext hx.symm
    refine ⟨⟨a .rv,ha⟩,rfl,?_⟩
    change (f ⟨a .rv,ha.1⟩).val = b .rv
    rw [eq]
    exact hy
  · rintro ⟨x,hx,hy⟩
    have mem : a .rv ∈ {x ∈ A | P x} := hx ▸ x.property
    exact ⟨⟨⟨x.val,x.property.1⟩,hx,hy⟩,mem⟩

end RVCut

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I J : Type} [Finite I] [Finite J] {m n : ℕ}
  {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cls" => objectClass 𝓜 S

private theorem zeroLeadCut_definable {H : Type} :
    isRVSet 𝓜 S {w : Fin 1 ⊕ H → RV0 O | w (.inl 0) = 0} := by
  have h := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier)
    (Var := RVVariables (Fin 1 ⊕ H)) .rv (.inl 0) rvZeroTerm
  unfold isRVSet
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq,realize_rvZeroTerm O hO power]

theorem unary_label_classes_of_mutual_contraction
    (idx : Fin m ≃ Fin 1 ⊕ I) (idy : Fin n ≃ Fin 1 ⊕ J)
    (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (finA : UnaryFiniteFibers A) (finB : UnaryFiniteFibers B)
    (f : A ≃ B) (graph : UnaryMixedGraphDefinable O hO power S f)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) f)
    (backward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) f.symm)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) :
    let a := unaryLabelObjects O hO power S A idx defA fullA finA
    let b := unaryLabelObjects O hO power S B idy defB fullB finB
    cls ⟨0,a.1⟩ = cls ⟨0,b.1⟩ ∧ cls ⟨1,a.2⟩ = cls ⟨1,b.2⟩ := by
  intro a b
  obtain ⟨e,eDef,deg⟩ := mutually_contracted_unary_labels O hO power S f graph fullA fullB forward backward he small
  let D := unaryLabelSet O A
  let F := unaryLabelSet O B
  let z {H : Type} (t : Fin 1 ⊕ H → RV0 O) := t (.inl 0) = 0
  have zA : isRVSet 𝓜 S {x ∈ D | z x} :=
    (unaryLabelSet_definable O hO power S defA).inter (zeroLeadCut_definable O hO power S (H := I))
  have zB : isRVSet 𝓜 S {x ∈ F | z x} :=
    (unaryLabelSet_definable O hO power S defB).inter (zeroLeadCut_definable O hO power S (H := J))
  have nzA : isRVSet 𝓜 S {x ∈ D | ¬ z x} :=
    (unaryLabelSet_definable O hO power S defA).inter (zeroLeadCut_definable O hO power S (H := I)).compl
  have nzB : isRVSet 𝓜 S {x ∈ F | ¬ z x} :=
    (unaryLabelSet_definable O hO power S defB).inter (zeroLeadCut_definable O hO power S (H := J)).compl
  have iso₀ : RVDefinablyEquivalent 𝓜 S.carrier {x ∈ D | z x} {y ∈ F | z y} :=
    rvDefinableEquiv_of_preserved_cut (M := 𝓜) (S := S) e eDef z z deg zA
  have iso₁ : RVDefinablyEquivalent 𝓜 S.carrier {x ∈ D | ¬ z x} {y ∈ F | ¬ z y} :=
    rvDefinableEquiv_of_preserved_cut (M := 𝓜) (S := S) e eDef
      (fun x => ¬ z x) (fun y => ¬ z y) (fun x => not_congr (deg x)) nzA
  constructor
  · apply scissors_sound 𝓜 S
    apply RVRelation.iso
    change RVDefinablyEquivalent 𝓜 S.carrier a.1.carrier b.1.carrier
    exact (rv_reindex_equivalent 𝓜 S idx _ zA).symm.trans (iso₀.trans (rv_reindex_equivalent 𝓜 S idy _ zB))
  · apply scissors_sound 𝓜 S
    apply RVRelation.iso
    change RVDefinablyEquivalent 𝓜 S.carrier a.2.carrier b.2.carrier
    exact (rv_reindex_equivalent 𝓜 S idx _ nzA).symm.trans (iso₁.trans (rv_reindex_equivalent 𝓜 S idy _ nzB))

end GeneralizedEuler.Section5
