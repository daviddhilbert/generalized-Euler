module

public import Section5.UnaryDeformation
public import Section5.RelativeSchemeDescent
public import Section5.LiftBoundaryDimension

/-! A single unary preparation makes finitely many witness definitions
constant over the full history. Projection to the new leading term
is finite-to-one on those histories, including its zero fiber. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K)

theorem UnaryPreparation.finite_labels_over_lead {H : Type*} (P : UnaryPreparation O H)
    (offsets : (Set.range P.offset).Finite) (t : RV0 O) :
    {h ∈ Set.range P.label | P.lead h = t}.Finite := by
  obtain ⟨a,ha⟩ := rv_surjective O t
  apply ((offsets.image (a + ·)).image P.label).subset
  rintro h ⟨⟨x,rfl⟩,hx⟩
  have tested : rv O ((a + P.offset (P.label x)) - P.offset (P.label x)) = P.lead (P.label x) := by
    rw [add_sub_cancel_right,ha,hx]
  exact ⟨a + P.offset (P.label x),⟨_,⟨_,rfl⟩,rfl⟩,P.constant_label tested⟩

theorem UnaryPreparation.prepared_labels_finite_over_lead {C : Type*} (center : C → K) (cs : List C)
    (t : RV0 O) :
    let P := (UnaryPreparation.regularize (O := O)).prepare center cs
    {h ∈ Set.range P.label | P.lead h = t}.Finite := by
  classical
  intro P
  let C₀ : Finset K := insert 0 (cs.toFinset.image center)
  have wf (h : PreparationLabels O (RV0 O) cs.length) : P.offset h ∈ (↑C₀ : Set K) := by
    apply (UnaryPreparation.regularize (O := O)).prepare_offset_mem (center := center) (B := ↑C₀)
    · intro _
      exact Finset.mem_insert_self _ _
    · intro c hc
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem center (List.mem_toFinset.2 hc))
  exact P.finite_labels_over_lead O (C₀.finite_toSet.subset (fun _ ⟨h,eq⟩ => eq ▸ wf h)) t

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
  {E : Type*} [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

private def historyRVAssignment {I : Type} (t : I → RV0 O) : SortedAssignment X (RVVariables I)
  | .vf => PEmpty.elim
  | .rv => t

theorem unary_prepared_history_graph (cs : List (S.carrier .vf))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
    DefinableRelation 𝓜 S.carrier (fun (p : SortedAssignment X P)
      (q : SortedAssignment X (RVVariables (HistoryIndex cs.length))) =>
      T.label (p .vf 0) = decodeHistory O cs.length (q .rv)) := by
  intro T
  let U := RVVariables (HistoryIndex cs.length)
  let H := SumVariables (SumVariables P U) P
  let rename : (s : TCsort) → MixedVariables 2 (HistoryIndex cs.length) s → H s
    | .vf => fun i => if i = 0 then .inl (.inl 0) else .inr 0
    | .rv => fun i => .inl (.inr i)
  have g := (preparationGraph_definable O hO power S F minusOne hm hF cs).pullback_relabel rename
  unfold DefinableRelation
  convert definable_project_mixed g using 1
  ext a
  let p := a .vf (.inl 0)
  let q := decodeHistory O cs.length (a .rv ∘ Sum.inr)
  change T.label p = q ↔ ∃ w : SortedAssignment X P, T.map p = (w .vf 0,q)
  constructor
  · intro e
    exact ⟨fieldTupleAssignment (fun _ => (T.map p).1),Prod.ext rfl e⟩
  · rintro ⟨w,e⟩
    exact congrArg Prod.snd e

theorem unary_preparation_of_witness_schemes {J : Type*} [Finite J] (I : J → Type)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ j, RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (I j))
      (CenterTestAssignments S.carrier (I j)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : ∀ j, Set (SortedAssignment X (SumVariables P (RVVariables (I j)))))
    (defA : ∀ j, SortedDefinableOver 𝓜 S.carrier (A j)) :
    ∃ cs : List (S.carrier .vf),
      let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      let R (p : SortedAssignment X P) (q : SortedAssignment X (RVVariables (HistoryIndex cs.length))) :=
        T.label (p .vf 0) = decodeHistory O cs.length (q .rv)
      DefinableRelation 𝓜 S.carrier R ∧
      (∀ j p q, R p q → ∀ u, appendAssignments q u ∈ descendFiberScheme R (A j) ↔ appendAssignments p u ∈ A j) ∧
      (∀ t, {h ∈ Set.range T.label | T.lead h = t}.Finite) := by
  let B (j : J) : Set (K × (I j → RV0 O)) :=
    {v | appendAssignments (fieldTupleAssignment (fun _ => v.1)) (historyRVAssignment O v.2) ∈ A j}
  have defB (j : J) : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment X (MixedVariables 1 (I j)) | (a .vf 0,a .rv) ∈ B j} := by
    let rename : (s : TCsort) → SumVariables P (RVVariables (I j)) s → MixedVariables 1 (I j) s
      | .vf => Sum.elim id PEmpty.elim
      | .rv => Sum.elim Empty.elim id
    convert (defA j).pullback_relabel rename using 1
    ext a
    have eq : appendAssignments (fieldTupleAssignment (fun _ => a .vf 0)) (historyRVAssignment O (a .rv)) =
          (fun s => a s ∘ rename s) := by
      funext s i
      cases s with
      | vf =>
        rcases i with i | i
        · rw [Subsingleton.elim i 0]
          rfl
        · exact i.elim
      | rv =>
        rcases i with i | i
        · exact i.elim
        · rfl
    change _ ∈ A j ↔ _ ∈ A j
    rw [eq]
  obtain ⟨cs,_,const⟩ := unary_preparation_of_indexed_tests O hO power S I minusOne hm F hF sat immediate B defB
  refine ⟨cs,unary_prepared_history_graph O hO power S cs F minusOne hm hF,?_,
    UnaryPreparation.prepared_labels_finite_over_lead O Subtype.val cs⟩
  intro j p q hp u
  apply descendFiberScheme_at hp _ u
  intro p' h' v
  have e (w : SortedAssignment X P) : fieldTupleAssignment (fun _ => w .vf 0) = w :=
    fieldAssignment_ext (fun i => congrArg (w .vf) (Subsingleton.elim 0 i))
  have fv : historyRVAssignment O (v .rv) = v := by
    funext s i
    cases s
    · exact i.elim
    · rfl
  have row := const j (p .vf 0) (p' .vf 0) (v .rv) (hp.trans h'.symm)
  change appendAssignments (fieldTupleAssignment (fun _ => p .vf 0)) (historyRVAssignment O (v .rv)) ∈ A j ↔
    appendAssignments (fieldTupleAssignment (fun _ => p' .vf 0)) (historyRVAssignment O (v .rv)) ∈ A j at row
  simpa only [e,fv] using row

end GeneralizedEuler.Section5
