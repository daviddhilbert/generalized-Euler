module

public import Section5.UnaryWitnessPreparation
public import Section5.RelativeRVRows
public import Section5.HeadStartZeroPatterns

/-! The full history of a prepared unary base is a definable RV index.
Its last leading term determines finitely many histories. The zero
stratum therefore remains finite after that term is omitted. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {h : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

variable (cs : List (S.carrier .vf))
  (e : Fin h ≃ HistoryIndex cs.length)

local notation "line" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

@[expose] def preparedHistoryLabels (D : Set (fieldAssignment 1 Z)) : Set (Fin h → RV0 O) :=
  {t | ∃ p ∈ D, (line).label (p .vf 0) = decodeHistory O cs.length (t ∘ e.symm)}

@[expose] def preparedHistoryRelation (D : Set (fieldAssignment 1 Z))
    (p : fieldAssignment 1 Z) (q : SortedAssignment Z (RVVariables (Fin h))) : Prop :=
  p ∈ D ∧ (line).label (p .vf 0) = decodeHistory O cs.length (q .rv ∘ e.symm)

theorem preparedHistoryRelation_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {D : Set (fieldAssignment 1 Z)} (defD : SortedDefinableOver 𝓜 S.carrier D) :
    DefinableRelation 𝓜 S.carrier (preparedHistoryRelation O hO power S cs e D) := by
  let U := MixedVariables 1 Empty
  let W := SumVariables U (RVVariables (HistoryIndex cs.length))
  let V := SumVariables U (RVVariables (Fin h))
  let reindex : (s : TCsort) → W s → V s
    | .vf => Sum.map id PEmpty.elim
    | .rv => Sum.map id e.symm
  have d := unary_prepared_history_graph O hO power S cs F minusOne hm hF
  unfold DefinableRelation at d ⊢
  have defSource := defD.pullback_relabel (fun s => (Sum.inl : U s → V s))
  exact defSource.inter (d.pullback_relabel reindex)

theorem preparedHistoryLabels_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {D : Set (fieldAssignment 1 Z)} (defD : SortedDefinableOver 𝓜 S.carrier D) :
    isRVSet 𝓜 S (preparedHistoryLabels O hO power S cs e D) := by
  have d := (unary_prepared_history_graph O hO power S cs F minusOne hm hF).image defD
  have set : isRVSet 𝓜 S {t : HistoryIndex cs.length → RV0 O |
      ∃ p ∈ D, (line).label (p .vf 0) = decodeHistory O cs.length t} := d
  exact isRVSet_precomp e.symm set

theorem preparedHistoryLabels_finite_over_last
    (D : Set (fieldAssignment 1 Z)) (y : RV0 O) :
    {t ∈ preparedHistoryLabels O hO power S cs e D | t (e.symm (lastIndex cs.length)) = y}.Finite := by
  let d (x : Fin h → RV0 O) := decodeHistory O cs.length (x ∘ e.symm)
  have inj : Function.Injective d := by
    intro x x' he
    have eq := congrArg (encodeHistory O cs.length) he
    change encodeHistory O cs.length (decodeHistory O cs.length (x ∘ e.symm)) =
      encodeHistory O cs.length (decodeHistory O cs.length (x' ∘ e.symm)) at eq
    rw [encode_decode_history,encode_decode_history] at eq
    funext i
    have same := congrFun eq (e i)
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using same
  have f := UnaryPreparation.prepared_labels_finite_over_lead O Subtype.val cs y
  apply (f.preimage inj.injOn).subset
  rintro t ⟨⟨p,_,ep⟩,ey⟩
  refine ⟨⟨p .vf 0,ep⟩,?_⟩
  change (line).lead (decodeHistory O cs.length (t ∘ e.symm)) = y
  exact (lead_decode_history O Subtype.val cs (t ∘ e.symm)).trans ey

/-- A domain tested by the preparation becomes a full pullback over
its retained histories. -/
theorem preparedHistoryLabels_image (D : Set (fieldAssignment 1 Z))
    (same : ∀ p q : fieldAssignment 1 Z, (line).label (p .vf 0) = (line).label (q .vf 0) →
      (p ∈ D ↔ q ∈ D)) :
    (fun p : fieldAssignment 1 Z => (((line).map (p .vf 0)).1,
      encodeHistory O cs.length ((line).label (p .vf 0)) ∘ e)) '' D =
      {y | y.2 ∈ preparedHistoryLabels O hO power S cs e D ∧
        rv O y.1 = y.2 (e.symm (lastIndex cs.length))} := by
  let T := line
  have encode_eval (x : K) : (encodeHistory O cs.length (T.label x) ∘ e) ∘ e.symm =
      encodeHistory O cs.length (T.label x) := by
    funext i
    exact congrArg (encodeHistory O cs.length (T.label x)) (e.apply_symm_apply i)
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    have code : decodeHistory O cs.length ((encodeHistory O cs.length (T.label (p .vf 0)) ∘ e) ∘ e.symm) =
        T.label (p .vf 0) := by rw [encode_eval,decode_encode_history]
    refine ⟨⟨p,hp,code.symm⟩,?_⟩
    change rv O (p .vf 0 - T.offset (T.label (p .vf 0))) =
      ((encodeHistory O cs.length (T.label (p .vf 0)) ∘ e) ∘ e.symm) (lastIndex cs.length)
    have last := lead_decode_history O Subtype.val cs
      ((encodeHistory O cs.length (T.label (p .vf 0)) ∘ e) ∘ e.symm)
    rw [code] at last
    exact (T.leading _).trans last
  · rintro ⟨⟨p,hp,ep⟩,lead⟩
    let x := y.1 + T.offset (T.label (p .vf 0))
    let a : fieldAssignment 1 Z := fieldTupleAssignment (fun _ => x)
    have hx : T.label x = T.label (p .vf 0) := by
      apply T.constant_label
      change rv O (y.1 + T.offset (T.label (p .vf 0)) - T.offset (T.label (p .vf 0))) = T.lead (T.label (p .vf 0))
      rw [add_sub_cancel_right,ep,lead_decode_history O Subtype.val cs]
      exact lead
    have ha : a ∈ D := (same a p hx).2 hp
    refine ⟨a,ha,Prod.ext ?_ ?_⟩
    · change x - T.offset (T.label x) = y.1
      rw [hx,add_sub_cancel_right]
    · change encodeHistory O cs.length (T.label x) ∘ e = y.2
      rw [hx,ep,encode_decode_history]
      funext i
      exact congrArg y.2 (e.symm_apply_apply i)

theorem preparedHistoryLabels_nonzero_index
    {D : Set (fieldAssignment 1 Z)}
    (defD : isRVSet 𝓜 S (preparedHistoryLabels O hO power S cs e D)) :
    ∃ J : RelativeRVIndex (X := Z) 𝓜 S h 1,
      J.labels = {t ∈ preparedHistoryLabels O hO power S cs e D | t (e.symm (lastIndex cs.length)) ≠ 0} ∧
      J.select 0 = e.symm (lastIndex cs.length) := by
  let sel : Fin 1 → Fin h := fun _ => e.symm (lastIndex cs.length)
  let B := preparedHistoryLabels O hO power S cs e D
  let zero : S.carrier .rv := ⟨(𝓜).funMap .rvZero (fun i => i.elim0),S.closed .rvZero _ (fun i => i.elim0)⟩
  let P := {t ∈ B | t (sel 0) ≠ 0}
  have defP : isRVSet 𝓜 S P := by
    have eq : isRVSet 𝓜 S {t : Fin h → RV0 O | t (sel 0) = 0} :=
      SortedDefinableOver.coordinate_eq_parameter (M := 𝓜) (A := S.carrier)
        (Var := RVVariables (Fin h)) .rv (sel 0) zero
    exact defD.inter eq.compl
  refine ⟨⟨P,defP,sel,fun t ht _ => ht.2,?_⟩,rfl,rfl⟩
  intro q
  apply (preparedHistoryLabels_finite_over_last O hO power S cs e D (q 0)).subset
  rintro t ⟨ht,he⟩
  exact ⟨ht.1,congrFun he 0⟩

theorem preparedHistoryLabels_zero_index
    {D : Set (fieldAssignment 1 Z)}
    (defD : isRVSet 𝓜 S (preparedHistoryLabels O hO power S cs e D)) :
    ∃ J : RelativeRVIndex (X := Z) 𝓜 S h 0,
      J.labels = {t ∈ preparedHistoryLabels O hO power S cs e D | t (e.symm (lastIndex cs.length)) = 0} := by
  let j := e.symm (lastIndex cs.length)
  let B := preparedHistoryLabels O hO power S cs e D
  let zero : S.carrier .rv := ⟨(𝓜).funMap .rvZero (fun i => i.elim0),S.closed .rvZero _ (fun i => i.elim0)⟩
  let P := {t ∈ B | t j = 0}
  have eq : isRVSet 𝓜 S {t : Fin h → RV0 O | t j = 0} :=
    SortedDefinableOver.coordinate_eq_parameter (M := 𝓜) (A := S.carrier)
      (Var := RVVariables (Fin h)) .rv j zero
  refine ⟨⟨P,defD.inter eq,Fin.elim0,fun _ _ i => i.elim0,?_⟩,rfl⟩
  intro q
  exact (preparedHistoryLabels_finite_over_last O hO power S cs e D 0).subset (fun _ ht => ht.1)

end GeneralizedEuler.Section5
