module

public import Section5.ProjectedScaling
public import Section5.ScaleTerms

/-! The field graph after restoring omitted coordinates is definable over
the same base as the projected lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

private abbrev FourFieldTuples (n : ℕ) : TCsort → Type :=
  SumVariables (SumVariables (MixedVariables n Empty) (MixedVariables n Empty))
    (SumVariables (MixedVariables n Empty) (MixedVariables n Empty))

private theorem omitted_scale_definable (p q : Fin k ↪ Fin n)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    SortedDefinableOver 𝓜 S.carrier
      {w : SortedAssignment (CanonicalSort O) (FourFieldTuples n) | ∀ i : Omitted p,
        w .vf (.inl (.inr (omittedEquiv p q i).val)) =
          w .vf (.inr (.inr (omittedEquiv p q i).val)) * w .vf (.inl (.inl i.val)) /
            w .vf (.inr (.inl i.val))} := by
  let r := omittedEquiv p q
  let W := WithBase S.carrier (FourFieldTuples n)
  let t (i : Omitted p) : SortedTerm L E W .vf :=
    scaleVF F (.var (.inr (.inr (.inl i.val)))) (.var (.inr (.inr (.inr (r i).val))))
      (.var (.inr (.inl (.inl i.val))))
  have h := SortedDefinableOver.iInter (fun i : Omitted p =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := FourFieldTuples n)
      .vf (.inl (.inr (r i).val)) (t i))
  convert h using 1
  ext w
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, t, eval_scaleVF O hO power F minusOne hm hF]
  rfl

/-- The projected lift and the two definable choices determine the graph
of the full lift by field equations on the deleted coordinates. -/
theorem definable_lift_of_projected {U V : Set (labelAssignment n (CanonicalSort O))}
    (p q : Fin k ↪ Fin n) (e : U ≃ V)
    (hp : Set.InjOn (projectLabels p) U) (hq : Set.InjOn (projectLabels q) V)
    (hU : SortedDefinableOver 𝓜 S.carrier U)
    (A : fieldLiftDomain 𝓜 (projectLabels p '' U) → fieldLiftDomain 𝓜 U)
    (B : fieldLiftDomain 𝓜 (projectLabels q '' V) → fieldLiftDomain 𝓜 V)
    (hA : ∀ a, projectFields p (A a).val = a.val)
    (hB : ∀ b, projectFields q (B b).val = b.val)
    (nonzeroA : ∀ a (i : Omitted p), (A a).val .vf i.val ≠ 0)
    (nonzeroB : ∀ b (i : Omitted q), (B b).val .vf i.val ≠ 0)
    (defA : DefinableRelation 𝓜 S.carrier (fun a u =>
      ∃ ha : a ∈ fieldLiftDomain 𝓜 (projectLabels p '' U), (A ⟨a,ha⟩).val = u))
    (defB : DefinableRelation 𝓜 S.carrier (fun b v =>
      ∃ hb : b ∈ fieldLiftDomain 𝓜 (projectLabels q '' V), (B ⟨b,hb⟩).val = v))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (small : HasDefinableFieldLift S (projectedLabelEquiv e p q hp hq)) :
    HasDefinableFieldLift S e := by
  obtain ⟨f,hf,defF⟩ := small
  obtain ⟨lift,hLabel,hRetain,hScale⟩ :=
    lift_projected_by_scaling (L := L) O hO power p q e hp hq A B hA hB nonzeroA nonzeroB f hf
  let W := MixedVariables n Empty
  let r := omittedEquiv p q
  let R (x y u v : fieldAssignment n (CanonicalSort O)) :=
    ∀ i : Omitted p, y .vf (r i).val = v .vf (r i).val * x .vf i.val / u .vf i.val
  have retained := ((projectFields_definable p).comp defF).comp (projectFields_definable q).transpose
  have sourceReps := (projectFields_definable p).comp defA
  have targetReps := (projectFields_definable q).comp defB
  unfold DefinableRelation at retained sourceReps targetReps
  let renameRet (s : TCsort) : SumVariables W W s → FourFieldTuples n s := Sum.inl
  let renameSrc (s : TCsort) : SumVariables W W s → FourFieldTuples n s :=
    Sum.map Sum.inl Sum.inl
  let renameTgt (s : TCsort) : SumVariables W W s → FourFieldTuples n s :=
    Sum.map Sum.inr Sum.inr
  have relation := (retained.pullback_relabel renameRet).inter
    (((sourceReps.pullback_relabel renameSrc).inter (targetReps.pullback_relabel renameTgt)).inter
      (omitted_scale_definable O hO power S p q F minusOne hm hF))
  have proj := definable_project_mixed relation
  let P (x y : fieldAssignment n (CanonicalSort O)) :=
    (∃ hx : projectFields p x ∈ fieldLiftDomain 𝓜 (projectLabels p '' U),
      (f ⟨projectFields p x,hx⟩).val = projectFields q y) ∧
    ∃ u v, (∃ ha : projectFields p x ∈ fieldLiftDomain 𝓜 (projectLabels p '' U),
        (A ⟨projectFields p x,ha⟩).val = u) ∧
      (∃ hb : projectFields q y ∈ fieldLiftDomain 𝓜 (projectLabels q '' V),
        (B ⟨projectFields q y,hb⟩).val = v) ∧ R x y u v
  have Pdef : DefinableRelation 𝓜 S.carrier P := by
    unfold DefinableRelation
    convert proj using 1
    ext w
    let x : fieldAssignment n (CanonicalSort O) := fun s => w s ∘ Sum.inl
    let y : fieldAssignment n (CanonicalSort O) := fun s => w s ∘ Sum.inr
    change P x y ↔ ∃ t : SortedAssignment (CanonicalSort O) (SumVariables W W),
      ((∃ b, (∃ a, projectFields p x = a ∧
        (∃ ha : a ∈ fieldLiftDomain 𝓜 (projectLabels p '' U), (f ⟨a,ha⟩).val = b)) ∧
        projectFields q y = b) ∧
       (((∃ a, projectFields p x = a ∧ ∃ ha : a ∈ fieldLiftDomain 𝓜 (projectLabels p '' U),
          (A ⟨a,ha⟩).val = (fun s => t s ∘ Sum.inl)) ∧
         (∃ b, projectFields q y = b ∧ ∃ hb : b ∈ fieldLiftDomain 𝓜 (projectLabels q '' V),
          (B ⟨b,hb⟩).val = (fun s => t s ∘ Sum.inr))) ∧
         R x y (fun s => t s ∘ Sum.inl) (fun s => t s ∘ Sum.inr)))
    constructor
    · rintro ⟨⟨hx,hf'⟩,u,v,⟨ha,rfl⟩,⟨hb,rfl⟩,hR⟩
      exact ⟨fun s => Sum.elim ((A ⟨projectFields p x,ha⟩).val s) ((B ⟨projectFields q y,hb⟩).val s),
        ⟨projectFields q y,⟨projectFields p x,rfl,hx,hf'⟩,rfl⟩,
        ⟨⟨projectFields p x,rfl,ha,rfl⟩,⟨projectFields q y,rfl,hb,rfl⟩⟩,hR⟩
    · rintro ⟨t,⟨_,⟨_,rfl,hx,hf'⟩,rfl⟩,⟨⟨_,rfl,ha,hAp⟩,⟨_,rfl,hb,hBp⟩⟩,hR⟩
      exact ⟨⟨hx,hf'⟩,_,_,⟨ha,hAp⟩,⟨hb,hBp⟩,hR⟩
  refine ⟨lift,hLabel,(Pdef.inter_left (definable_fieldLead_preimage hU)).congr ?_⟩
  intro x y
  constructor
  · rintro ⟨⟨⟨hx,hRet⟩,a,b,⟨ha,hea⟩,⟨hb,heb⟩,hR⟩,hX⟩
    let x' : fieldLiftDomain 𝓜 U := ⟨x,hX⟩
    let z := lift x'
    have he : projectFields q z.val = projectFields q y :=
      (congrArg Subtype.val (hRetain x')).trans hRet
    have he' : (⟨projectFields q y,hb⟩ : fieldLiftDomain 𝓜 (projectLabels q '' V)) =
        f (projectFieldLift p x') := Subtype.ext hRet.symm
    refine ⟨hX,fieldAssignment_ext (fun j => ?_)⟩
    by_cases hj : j ∈ Set.range q
    · obtain ⟨i,rfl⟩ := hj
      exact congrFun (congrFun he .vf) i
    · let i := r.symm ⟨j,hj⟩
      have hq' : r i = ⟨j,hj⟩ := r.apply_symm_apply _
      have H := hScale x' i
      change z.val .vf (r i).val =
        (B (f (projectFieldLift p x'))).val .vf (r i).val * x .vf i.val /
          (A (projectFieldLift p x')).val .vf i.val at H
      rw [← he', heb, show (A (projectFieldLift p x')).val = a from hea] at H
      change z.val .vf j = y .vf j
      have hIdx : (r i).val = j := congrArg Subtype.val hq'
      rw [← hIdx]
      exact H.trans (hR i).symm
  · rintro ⟨hX,rfl⟩
    let x' : fieldLiftDomain 𝓜 U := ⟨x,hX⟩
    let a := projectFieldLift p x'
    let b := projectFieldLift q (lift x')
    have he : b = f a := hRetain x'
    exact ⟨⟨⟨a.property,(congrArg Subtype.val he).symm⟩,
      (A a).val,(B b).val,⟨a.property,rfl⟩,⟨b.property,rfl⟩,
      fun i => he.symm ▸ hScale x' i⟩,hX⟩

/-- The projected lift suffices on any pair of pieces with injective RV
coordinate projections. The representatives are chosen using only the
retained field tuple and the original base. -/
theorem definable_lift_of_injective_projection {U V : Set (labelAssignment n (CanonicalSort O))}
    (p q : Fin k ↪ Fin n) (e : U ≃ V)
    (hp : Set.InjOn (projectLabels p) U) (hq : Set.InjOn (projectLabels q) V)
    (hU : SortedDefinableOver 𝓜 S.carrier U) (hV : SortedDefinableOver 𝓜 S.carrier V)
    (nonzeroU : ∀ u ∈ U, ∀ i, u .rv i ≠ 0) (nonzeroV : ∀ v ∈ V, ∀ i, v .rv i ≠ 0)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables k Empty))
      (BaseAssignments S.carrier (MixedVariables k Empty)))
    (elem : ∀ a : fieldAssignment k (CanonicalSort O), let C := (𝓜).termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → C.carrier s),
        φ.realize C.structureOn v ↔ φ.realize 𝓜 (fun s i => (v s i).val))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (small : HasDefinableFieldLift S (projectedLabelEquiv e p q hp hq)) :
    HasDefinableFieldLift S e := by
  have surj : Function.Surjective (𝓜).rvMap := by
    intro t
    obtain ⟨x,hx⟩ := rv_surjective O t
    exact ⟨x,(canonicalStructure_rvMap O hO power x).trans hx⟩
  obtain ⟨A,hA,defA⟩ := definable_projected_field_completion p surj sat elem hU
  obtain ⟨B,hB,defB⟩ := definable_projected_field_completion q surj sat elem hV
  have aNZ (a) (i : Omitted p) : (A a).val .vf i.val ≠ 0 := by
    intro hz
    have hu := nonzeroU _ (A a).property i.val
    apply hu
    change (𝓜).rvMap ((A a).val .vf i.val) = 0
    rw [canonicalStructure_rvMap,hz]
    exact map_zero _
  have bNZ (b) (i : Omitted q) : (B b).val .vf i.val ≠ 0 := by
    intro hz
    have hv := nonzeroV _ (B b).property i.val
    apply hv
    change (𝓜).rvMap ((B b).val .vf i.val) = 0
    rw [canonicalStructure_rvMap,hz]
    exact map_zero _
  exact definable_lift_of_projected O hO power S p q e hp hq hU A B hA hB aNZ bNZ defA defB
    F minusOne hm hF small

end GeneralizedEuler.Section5
