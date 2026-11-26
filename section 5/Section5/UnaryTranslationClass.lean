module

public import Section5.UnaryPostStrata
public import Section5.RVAppendLabel
public import Section5.PartialFocusBlowup
import all Section4.Objects

/-! A unary focus step on a fixed-base pullback gives one elementary
blowup of its graded label class. The unchanged labels are identified
by dropping their determined final coordinate. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I : Type} [Finite I] {m : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cls" => objectClass 𝓜 S

omit [Finite I] in
private theorem appendUnaryLabel_equiv (D : Set (Fin m → RV0 O)) (defD : isRVSet 𝓜 S D)
    (d : (Fin m → RV0 O) → RV0 O)
    (defd : DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment (CanonicalSort O) (RVVariables (Fin m)))
      (b : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1))) => d (a .rv) = b .rv 0)) :
    RVDefinablyEquivalent 𝓜 S.carrier D (appendUnaryLabelSet O D (fun x b => b = d x)) := by
  have h := rv_equiv_append_label (M := 𝓜) (S := S) D defD d defd
  have hdef := isRVSet_of_rvEquiv (M := 𝓜) (S := S) h
  exact h.trans (rv_reindex_equivalent 𝓜 S finSumFinEquiv.symm _ hdef)

omit [Finite I] in
private theorem appendZeroLabel_equiv (D : Set (Fin m → RV0 O)) (defD : isRVSet 𝓜 S D) :
    RVDefinablyEquivalent 𝓜 S.carrier D (appendUnaryLabelSet O D (fun _ b => b = 0)) := by
  apply appendUnaryLabel_equiv O hO power S D defD (fun _ => 0)
  let W := SumVariables (RVVariables (Fin m)) (RVVariables (Fin 1))
  have h := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W) .rv (.inr 0) rvZeroTerm
  unfold DefinableRelation
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq,realize_rvZeroTerm O hO power]
  exact eq_comm

omit [Finite I] in
private theorem appendExistingLabel_equiv (D : Set (Fin m → RV0 O)) (defD : isRVSet 𝓜 S D) (j : Fin m) :
    RVDefinablyEquivalent 𝓜 S.carrier D (appendUnaryLabelSet O D (fun x b => b = x j)) :=
  appendUnaryLabel_equiv O hO power S D defD (fun x => x j)
    (SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier)
      (Var := SumVariables (RVVariables (Fin m)) (RVVariables (Fin 1))) .rv (.inl j) (.inr 0))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
theorem unary_translation_is_elementary_blowup
    (A : Set (K × (I → RV0 O))) (idx : Fin m ≃ Fin 1 ⊕ I)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (defT : UnaryOffsetDefinable O hO power S T)
    (defA : UnaryPullbackDefinable O hO power S A) (full : IsUnaryPullback O A) (finite : UnaryFiniteFibers A)
    (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t)
    (offsets : (Set.range (fun p : (I → RV0 O) × RV0 O => T.offset p.1 p.2)).Finite)
    (defB : UnaryPullbackDefinable O hO power S (encodedUnaryImage O A T))
    (hneg : rv O (-1) ∈ S.carrier .rv) :
    let a := unaryLabelObjects O hO power S A idx defA full finite
    let B := encodedUnaryImage O A T
    let pb := reindexUnaryImage_is_pullback O (unaryTagAppend O) _
      (recodeUnaryTranslation_preserves_pullback O T A full valid)
    let b := unaryLabelObjects O hO power S B (unaryPostIndex idx) defB pb
      (encodedUnaryImage_finiteFibers O A T finite offsets)
    ElementaryClassStep O hO power S hneg (cls ⟨0,a.1⟩ + cls ⟨1,a.2⟩) (cls ⟨0,b.1⟩ + cls ⟨1,b.2⟩) := by
  intro a B pb b
  let j := idx.symm (.inl 0)
  let D := unarySelectedLabels O A idx T
  let R := a.2.carrier \ D
  have defD : isRVSet 𝓜 S D :=
    isRVSet_inter (reindexedUnaryLabels_definable O hO power S A idx defA)
      (isRVSet_precomp idx.symm (translatedUnaryCut_definable O hO power S T defT))
  have sub : D ⊆ a.2.carrier := fun _ h => ⟨h.1,unarySelectedLabel_nonzero O idx T valid h⟩
  have defR : isRVSet 𝓜 S R := a.2.definable.inter defD.compl
  let U := ObjectLift.restrictTags a.2 sub defD
  let W := ObjectLift.restrictTags a.2 (Set.sdiff_subset : R ⊆ a.2.carrier) defR
  let k := (0 : Fin 1)
  have hdel (t : Fin 0 → RV0 O) : {w ∈ Set.range U.label | w ∘ k.succAbove = t}.Finite := by
    have injective : Function.Injective (fun w : Fin 1 → RV0 O => w 0) := by
      intro x y eq
      funext i
      rwa [Subsingleton.elim i (0 : Fin 1)]
    apply ((offsets.image (rv O)).preimage injective.injOn).subset
    rintro _ ⟨⟨x,rfl⟩,_⟩
    let tag := x.val ∘ idx.symm ∘ Sum.inr
    let lead := x.val j
    have h : T.offset tag lead ≠ 0 := x.property.2
    have locus := (unary_offset_ne_zero_iff O T valid tag lead).1 h
    refine ⟨T.offset tag lead,⟨(tag,lead),rfl⟩,?_⟩
    change rv O (T.offset tag lead) = lead
    have eq : T.offset tag lead = T.focus tag lead := by
      classical
      change (if (tag,lead) ∈ T.locus then T.focus tag lead else 0) = _
      rw [ite_eq_left locus.1]
    rw [eq]
    exact valid tag lead locus.1
  let idx' : Fin (m+1) ≃ Fin U.arity ⊕ Fin 1 := finSumFinEquiv.symm
  let Z := zeroBlowupObject U k hdel
  let P := translatedPositiveObject O hO power S U idx' k hneg hdel
  have step : ElementaryClassStep O hO power S hneg (cls ⟨1,a.2⟩)
      (cls ⟨0,Z⟩ + cls ⟨1,P⟩ + cls ⟨1,W⟩) :=
    partial_focus_blowup_class O hO power S a.2 k D hneg defD sub hdel
  let N₀ := appendUnaryLabelSet O a.1.carrier (fun _ b => b = 0)
  let C₀ := appendUnaryLabelSet O D (fun _ b => b = 0)
  let N₁ := appendUnaryLabelSet O R (fun x b => b = x j)
  let C₁ := appendUnaryLabelSet O D (fun x b => unsignedValue O b < unsignedValue O (x j) ∧ b ≠ 0)
  have n₀ := appendZeroLabel_equiv O hO power S a.1.carrier a.1.definable
  have c₀ := appendZeroLabel_equiv O hO power S D defD
  have n₁ := appendExistingLabel_equiv O hO power S R defR j
  have c₁Eq : C₁ = P.carrier := by
    ext x
    change (x ∘ blowupOldIndices idx' ∈ D ∧
      unsignedValue O (x (blowupExtraIndex idx')) < unsignedValue O ((x ∘ blowupOldIndices idx') j) ∧
      x (blowupExtraIndex idx') ≠ 0) ↔
      ∃ y : U.carrier, y.val = x ∘ blowupOldIndices idx' ∧
        unsignedValue O (x (blowupExtraIndex idx')) < unsignedValue O (U.label y k) ∧ x (blowupExtraIndex idx') ≠ 0
    constructor
    · rintro ⟨h,hv,hn⟩
      exact ⟨⟨_,h⟩,rfl,hv,hn⟩
    · rintro ⟨y,eq,hv,hn⟩
      have h : x ∘ blowupOldIndices idx' ∈ D := eq ▸ y.property
      change unsignedValue O (x (blowupExtraIndex idx')) < unsignedValue O (y.val j) at hv
      rw [eq] at hv
      exact ⟨h,hv,hn⟩
  have cov₀ : N₀ ∪ C₀ = b.1.carrier := (unary_post_zero_strata O A idx T full valid).symm
  have cov₁ : N₁ ∪ C₁ = b.2.carrier := (unary_post_positive_strata O A idx T full valid).symm
  have dis₀ : Disjoint N₀ C₀ := Set.disjoint_left.2 fun w hw hv =>
    unarySelectedLabel_nonzero O idx T valid hv.1 hw.1.2
  have dis₁ : Disjoint N₁ C₁ := Set.disjoint_left.2 fun w hw hv => hw.1.2 hv.1
  have h₀ : cls ⟨0,b.1⟩ = cls ⟨0,a.1⟩ + cls ⟨0,Z⟩ := by
    apply scissors_sound 𝓜 S
    exact RVRelation.cut b.1 a.1 Z N₀ C₀ (isRVSet_of_rvEquiv n₀) (isRVSet_of_rvEquiv c₀) dis₀ cov₀ n₀.symm c₀.symm
  have d₁ : isRVSet 𝓜 S C₁ := c₁Eq.symm ▸ P.definable
  have i₁ : RVDefinablyEquivalent 𝓜 S.carrier C₁ P.carrier := by
    rw [c₁Eq]
    exact ⟨Equiv.refl _,definable_identity_label 𝓜 S P.definable⟩
  have h₁ : cls ⟨1,b.2⟩ = cls ⟨1,W⟩ + cls ⟨1,P⟩ := by
    apply scissors_sound 𝓜 S
    exact RVRelation.cut b.2 W P N₁ C₁ (isRVSet_of_rvEquiv n₁) d₁ dis₁ cov₁ n₁.symm i₁
  rw [h₀,h₁]
  simpa only [add_assoc,add_comm,add_left_comm] using elementaryClassStep_add O hO power S hneg step (cls ⟨0,a.1⟩)

end GeneralizedEuler.Section5
