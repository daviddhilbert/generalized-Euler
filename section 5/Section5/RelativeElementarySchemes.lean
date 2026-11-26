module

public import Section5.RelativeRVLiftChoice
public import Section5.RelativeLabelDeletion
public import Section5.ZeroBlowupObject

/-! An actual elementary blowup yields a first-order validity scheme.
The deletion bound is chosen over the same generated base as the
original label bound. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type} {k : ℕ}

structure RelativeElementaryScheme (M : SortedStructure L E X) (S : SortedSubstructure M)
    (P : TCsort → Type) (k : ℕ) where
  arity : ℕ
  sourceBound : ℕ
  deletionBound : ℕ
  slot : Fin (k+1)
  tags : Set (SortedAssignment X (SumVariables P (RVVariables (Fin arity))))
  graph : Set (SortedAssignment X (SumVariables (SumVariables P (RVVariables (Fin arity))) (RVVariables (Fin (k+1)))))
  tagsDefinable : SortedDefinableOver M S.carrier tags
  graphDefinable : SortedDefinableOver M S.carrier graph

namespace RelativeElementaryScheme

variable (W : RelativeElementaryScheme M S P k) (zero : S.carrier .rv)

@[expose] def valid (p : SortedAssignment X P) : Prop :=
  RelativeRVWitness W.tags W.graph zero.val W.sourceBound p ∧
  RelativeRVWitness W.tags (relativeDeleteLabelGraph W.slot W.graph) zero.val W.deletionBound p

theorem valid_definable :
    SortedDefinableOver M S.carrier {p | W.valid zero p} :=
  (relativeRVWitness_definable W.tagsDefinable W.graphDefinable zero W.sourceBound).inter
    (relativeRVWitness_definable W.tagsDefinable (relativeDeleteLabelGraph_definable W.slot W.graphDefinable)
      zero W.deletionBound)

end RelativeElementaryScheme

theorem relative_elementary_scheme_of_object
    (p : SortedAssignment X P)
    (zero : S.carrier .rv) (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (B : RVObject M (M.termGenerated (namedTuple S p)) (k+1)) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → X .rv, {u ∈ Set.range B.label | u ∘ j.succAbove = t}.Finite)
    (sat : ∀ k, let T := M.termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes M (WithBase T.carrier (RVVariables (Fin k)))
        (BaseAssignments T.carrier (RVVariables (Fin k)))) :
    ∃ W : RelativeElementaryScheme M S P k, W.arity = B.arity ∧ W.slot = j ∧ W.valid zero p := by
  obtain ⟨D,G,defD,defG,matchD,matchG⟩ := relative_rv_labels_of_object p B
  let Z := zeroBlowupObject B j finiteDelete
  obtain ⟨b,hb⟩ := rvObject_uniform_label_bound B (sat (k+1))
  obtain ⟨c,hc⟩ := rvObject_uniform_label_bound Z (sat k)
  let W : RelativeElementaryScheme M S P k := ⟨B.arity,b,c,j,D,G,defD,defG⟩
  refine ⟨W,rfl,rfl,relativeRVWitness_of_labelRelation p B matchD matchG zero.val hzero b hb,?_⟩
  have deletion (a : SortedAssignment X (RVVariables (Fin B.arity))) (v : SortedAssignment X (RVVariables (Fin k))) :
      appendAssignments (appendAssignments p a) v ∈ relativeDeleteLabelGraph j G ↔ RVObject.LabelRelation Z a v := by
    rw [relativeDeleteLabelGraph_iff]
    constructor
    · rintro ⟨w,hw,eq⟩
      obtain ⟨ha,he⟩ := (matchG a w).1 hw
      exact ⟨ha,(congrArg (· ∘ j.succAbove) he).trans (congrFun eq .rv)⟩
    · rintro ⟨ha,eq⟩
      refine ⟨rvTupleAssignment (B.label ⟨a .rv,ha⟩), (matchG a _).2 ⟨ha,rfl⟩,?_⟩
      funext s i
      cases s
      · exact i.elim
      · exact congrFun eq i
  exact relativeRVWitness_of_labelRelation p Z matchD deletion zero.val hzero c hc

theorem uniform_relative_elementary_schemes
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (zero : S.carrier .rv) (D : Set (SortedAssignment X P)) (defD : SortedDefinableOver M S.carrier D)
    (cover : ∀ p ∈ D, ∃ W : RelativeElementaryScheme M S P k, W.valid zero p) :
    ∃ (C : Finset (RelativeElementaryScheme M S P k)) (pieces : {i // i ∈ C} → Set (SortedAssignment X P)),
      (∀ i, SortedDefinableOver M S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid zero p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D :=
  finite_definable_partition_of_cover sat D defD (fun i : RelativeElementaryScheme M S P k => {p | i.valid zero p})
    (fun i => i.valid_definable zero) cover

end GeneralizedEuler.Section5
