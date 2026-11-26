module

public import Section5.UnaryTranslationGraph
public import Section5.PairedFocusDefinability
import all Section5.PairedSourceTranslation

/-! The prescribed target focus and the old mixed bijection determine
the fixed-base graph of the paired source translation. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I J : Type} [Finite I] [Finite J]
  {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
  (e : A ≃ B) (C : Set (RV0 O × (J → RV0 O))) (focus : RV0 O × (J → RV0 O) → B)

local notation "𝓜" => canonicalStructure (L := L) O hO power

abbrev unaryPair {H : Type} (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H)) :
    K × (H → RV0 O) := (a .vf 0,a .rv)

abbrev decodeUnaryLabel {H : Type} (l : (Fin 1 ⊕ H) → RV0 O) : RV0 O × (H → RV0 O) :=
  (l (.inl 0),l ∘ Sum.inr)

@[expose] def unaryLabelAssignment {H : Type}
    (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H)) :
    SortedAssignment (CanonicalSort O) (RVVariables (Fin 1 ⊕ H))
  | .vf => PEmpty.elim
  | .rv => encodeUnaryLabel O (unaryPair O a)

theorem unaryLabelAssignment_definable {H : Type} [Finite H] :
    DefinableRelation 𝓜 S.carrier
      (fun a b => unaryLabelAssignment O (H := H) a = b) := by
  refine (packPullbackLabel_definable hO power S (n := 1) (I := H)).congr ?_
  intro a b
  have same : packPullbackLabel (mixedTuple a) = encodeUnaryLabel O (unaryPair O a) := by
    funext i
    cases i with
    | inl i => rw [Subsingleton.elim i (0 : Fin 1)]; rfl
    | inr i => rfl
  rw [same]
  constructor
  · intro he
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => exact congrFun he i
  · exact fun h => congrFun h .rv

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rv_assignments_same_iff {H : Type}
    (a b : SortedAssignment (CanonicalSort O) (MixedVariables 1 H)) :
    unaryLabelAssignment O a = unaryLabelAssignment O b ↔
      unaryMixedLabel O (unaryPair O a) = unaryMixedLabel O (unaryPair O b) := by
  constructor
  · intro h
    exact congrArg (fun v : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1 ⊕ H)) =>
      decodeUnaryLabel O (v .rv)) h
  · intro h
    funext s i
    cases s with
    | vf => exact i.elim
    | rv =>
      cases i with
      | inl i =>
        rw [Subsingleton.elim i (0 : Fin 1)]
        exact congrArg Prod.fst h
      | inr i => exact congrFun (congrArg Prod.snd h) i

omit [Finite I] in
private theorem unary_field_projection_definable :
    DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
      (b : fieldAssignment 1 (CanonicalSort O)) => a .vf 0 = b .vf 0) :=
  SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier)
    (Var := SumVariables (MixedVariables 1 I) (MixedVariables 1 Empty)) .vf (.inl 0) (.inr 0)

abbrev targetFocusGraphDefinable :=
  DefinableRelation 𝓜 S.carrier
    (fun (t : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1 ⊕ J)))
      (y : SortedAssignment (CanonicalSort O) (MixedVariables 1 J)) =>
      decodeUnaryLabel O (t .rv) ∈ C ∧ (focus (decodeUnaryLabel O (t .rv))).val = unaryPair O y)

@[expose] def selectedPairedSourceFocus
    (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)) (c : K) : Prop :=
  ∃ ha : unaryPair O a ∈ A,
    let t := unaryMixedLabel O (e ⟨unaryPair O a,ha⟩).val
    let y := e.symm (focus t)
    t ∈ C ∧ unaryMixedLabel O (unaryPair O a) = unaryMixedLabel O y.val ∧ c = y.val.1

/-- The source focus is computed by pulling back the target focus and
checking that it lies in the original source label. -/
theorem selectedPairedSourceFocus_definable (eDef : UnaryMixedGraphDefinable O hO power S e)
    (cDef : targetFocusGraphDefinable O hO power S C focus)
    (full : IsUnaryPullback O A)
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e) :
    DefinableRelation 𝓜 S.carrier
      (fun a (v : fieldAssignment 1 (CanonicalSort O)) =>
        selectedPairedSourceFocus O e C focus a (v .vf 0)) := by
  let p := unaryLabelAssignment O (H := I)
  let q := unaryLabelAssignment O (H := J)
  have pDef := unaryLabelAssignment_definable O hO power S (H := I)
  have qDef := unaryLabelAssignment_definable O hO power S (H := J)
  have paired := paired_focus_graph_definable p q _ _ pDef qDef eDef cDef
  have comp := (pDef.comp paired).comp (unary_field_projection_definable O hO power S (I := I))
  refine comp.congr ?_
  intro a v
  constructor
  · rintro ⟨x,⟨u,hu,hLabel,a',b,y,he,⟨ha',hfa⟩,⟨hC,hy⟩,⟨hx,hfx⟩⟩,hCoord⟩
    subst u
    let z : A := ⟨unaryPair O x,hx⟩
    have xEq : unaryMixedLabel O z.val = unaryMixedLabel O (unaryPair O a) :=
      (rv_assignments_same_iff O _ _).1 hLabel
    have aEq : unaryMixedLabel O (unaryPair O a') = unaryMixedLabel O z.val :=
      ((rv_assignments_same_iff O _ _).1 he).trans xEq.symm
    have tEq : unaryMixedLabel O (e ⟨unaryPair O a',ha'⟩).val = unaryMixedLabel O (e z).val :=
      contract _ _ aEq
    have place : decodeUnaryLabel O ((q b) .rv) = unaryMixedLabel O (e z).val :=
      (congrArg (unaryMixedLabel O) hfa).symm.trans tEq
    have ey : e z = focus (unaryMixedLabel O (e z).val) := by
      apply Subtype.ext
      exact hfx.trans (hy.symm.trans (congrArg (fun t => (focus t).val) place))
    have mem : unaryPair O a ∈ A := full z.val z.property _ xEq
    let w : A := ⟨unaryPair O a,mem⟩
    have out : unaryMixedLabel O (e w).val = unaryMixedLabel O (e z).val := contract w z xEq.symm
    have back : e.symm (focus (unaryMixedLabel O (e w).val)) = z := by
      rw [out,← ey,e.symm_apply_apply]
    refine ⟨mem,?_,?_,?_⟩
    · change unaryMixedLabel O (e w).val ∈ C
      rw [out,← place]
      exact hC
    · rw [back]
      exact xEq.symm
    · rw [back]
      exact hCoord.symm
  · rintro ⟨ha,hc,he,hv⟩
    let z : A := ⟨unaryPair O a,ha⟩
    let t := unaryMixedLabel O (e z).val
    let y := e.symm (focus t)
    let pack {H : Type} (w : K × (H → RV0 O)) :
        SortedAssignment (CanonicalSort O) (MixedVariables 1 H)
      | .vf => fun _ => w.1
      | .rv => w.2
    refine ⟨pack y.val,⟨p a,rfl,?_,a,pack (e z).val,pack (focus t).val,rfl,⟨ha,rfl⟩,
      ⟨hc,rfl⟩,⟨y.property,congrArg Subtype.val (e.apply_symm_apply (focus t))⟩⟩,hv.symm⟩
    exact (rv_assignments_same_iff O _ _).2 he.symm

section OffsetGraphs

theorem pairedSourceOffset_definable
    (eDef : UnaryMixedGraphDefinable O hO power S e)
    (cDef : targetFocusGraphDefinable O hO power S C focus)
    (full : IsUnaryPullback O A)
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e) :
    DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
        (v : fieldAssignment 1 (CanonicalSort O)) =>
        v .vf 0 = (pairedSourceTranslation O e C focus).offset (a .rv) (rv O (a .vf 0))) := by
  classical
  have hf := selectedPairedSourceFocus_definable O hO power S e C focus eDef cDef full contract
  refine (default_zero_focus_definable O hO power S (selectedPairedSourceFocus O e C focus) hf).congr ?_
  intro a v
  by_cases ha : unaryPair O a ∈ A
  · let x : A := ⟨unaryPair O a,ha⟩
    let t := unaryMixedLabel O (e x).val
    let y := e.symm (focus t)
    have offset := pairedSourceTranslation_offset O e C focus contract x
    change (selectedPairedSourceFocus O e C focus a (v .vf 0) ∨
      ((∀ c, ¬ selectedPairedSourceFocus O e C focus a c) ∧ v .vf 0 = 0)) ↔
      v .vf 0 = (pairedSourceTranslation O e C focus).offset x.val.2 (rv O x.val.1)
    rw [offset]
    have cond (c : K) : selectedPairedSourceFocus O e C focus a c ↔
        (t ∈ C ∧ unaryMixedLabel O x.val = unaryMixedLabel O y.val) ∧ c = y.val.1 := by
      exact ⟨fun ⟨_,ht,he,hc⟩ => ⟨⟨ht,he⟩,hc⟩,fun ⟨⟨ht,he⟩,hc⟩ => ⟨ha,ht,he,hc⟩⟩
    simp only [cond]
    by_cases h : t ∈ C ∧ unaryMixedLabel O x.val = unaryMixedLabel O y.val
    · rw [ite_eq_left h]
      simp [h,y,t]
    · rw [ite_eq_right h]
      simp [h]
  · have no (c : K) : ¬ selectedPairedSourceFocus O e C focus a c := fun ⟨h, _⟩ => ha h
    have outside : ((a .rv),rv O (a .vf 0)) ∉ (pairedSourceTranslation O e C focus).locus := by
      intro hl
      change ((a .rv),rv O (a .vf 0)) ∈ pairedSourceLocus O e C focus at hl
      obtain ⟨x,hx,_,_⟩ := hl
      exact ha (full x.val x.property _ hx)
    simp [no,RelativeTranslation.offset,outside]

theorem pairedTargetOffset_definable
    (cDef : targetFocusGraphDefinable O hO power S C focus) :
    DefinableRelation 𝓜 S.carrier
      (fun (b : SortedAssignment (CanonicalSort O) (MixedVariables 1 J))
        (v : fieldAssignment 1 (CanonicalSort O)) =>
        v .vf 0 = (pairedTargetTranslation O C focus).offset (b .rv) (rv O (b .vf 0))) := by
  classical
  let chosen (b : SortedAssignment (CanonicalSort O) (MixedVariables 1 J)) (c : K) :=
    unaryMixedLabel O (unaryPair O b) ∈ C ∧ c = (focus (unaryMixedLabel O (unaryPair O b))).val.1
  have graph := ((unaryLabelAssignment_definable O hO power S (H := J)).comp cDef).comp
    (unary_field_projection_definable O hO power S (I := J))
  have hf : DefinableRelation 𝓜 S.carrier
      (fun b (v : fieldAssignment 1 (CanonicalSort O)) => chosen b (v .vf 0)) := by
    refine graph.congr ?_
    intro b v
    constructor
    · rintro ⟨y,⟨u,hu,hC,hy⟩,hv⟩
      subst u
      exact ⟨hC,hv.symm.trans (congrArg Prod.fst hy).symm⟩
    · rintro ⟨hC,hv⟩
      let w := (focus (unaryMixedLabel O (unaryPair O b))).val
      let y : SortedAssignment (CanonicalSort O) (MixedVariables 1 J)
        | .vf => fun _ => w.1
        | .rv => w.2
      exact ⟨y,⟨unaryLabelAssignment O b,rfl,hC,rfl⟩,hv.symm⟩
  refine (default_zero_focus_definable O hO power S chosen hf).congr ?_
  intro b v
  unfold RelativeTranslation.offset pairedTargetTranslation
  change (chosen b (v .vf 0) ∨ ((∀ c, ¬ chosen b c) ∧ v .vf 0 = 0)) ↔
    v .vf 0 = (if unaryMixedLabel O (unaryPair O b) ∈ C then
      (focus (unaryMixedLabel O (unaryPair O b))).val.1 else 0)
  by_cases h : unaryMixedLabel O (unaryPair O b) ∈ C
  · rw [ite_eq_left h]
    simp [chosen,h]
  · rw [ite_eq_right h]
    simp [chosen,h]

end OffsetGraphs

end GeneralizedEuler.Section5
