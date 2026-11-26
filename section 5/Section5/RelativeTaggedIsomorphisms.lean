module

public import Section5.RelativeFiberPartitions
public import Section5.RelativeRVRows

/-! Graded isomorphisms between finite relative families are given
by a matrix of definable graphs on their tag pairs. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P Q : TCsort → Type}

/-- The tag carrier of a homogeneous row. The structure map is
irrelevant when testing definable isomorphisms in its degree. -/
structure RelativeRVTags (M : SortedStructure L E X) (S : SortedSubstructure M) (P : TCsort → Type) where
  degree : ℕ
  arity : ℕ
  tags : Set (SortedAssignment X (SumVariables P (RVVariables (Fin arity))))
  definable : SortedDefinableOver M S.carrier tags

namespace RelativeRVTags

abbrev Vars (A : RelativeRVTags M S P) := RVVariables (Fin A.arity)

@[expose] def descend [Finite (P .vf)] [Finite (P .rv)] (A : RelativeRVTags M S P)
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) : RelativeRVTags M S Q :=
  ⟨A.degree,A.arity,descendFiberScheme H A.tags,descendFiberScheme_definable defH A.definable⟩

@[expose] def ofRow {h t k : ℕ} {I : RelativeRVIndex M S h t} (A : RelativeRVRow I k) :
    RelativeRVTags M S (RVVariables (Fin h)) :=
  ⟨k,A.arity,A.tags,A.tagsDefinable⟩

end RelativeRVTags

variable {I J : Type} (A : I → RelativeRVTags M S P) (B : J → RelativeRVTags M S P)

structure RelativeTaggedIsoScheme where
  source : ∀ i, J → Set (SortedAssignment X (SumVariables P (A i).Vars))
  target : ∀ j, I → Set (SortedAssignment X (SumVariables P (B j).Vars))
  graph : ∀ i j, Set (SortedAssignment X (SumVariables (SumVariables P (A i).Vars) (B j).Vars))
  sourceDefinable : ∀ i j, SortedDefinableOver M S.carrier (source i j)
  targetDefinable : ∀ j i, SortedDefinableOver M S.carrier (target j i)
  graphDefinable : ∀ i j, SortedDefinableOver M S.carrier (graph i j)

namespace RelativeTaggedIsoScheme

variable {A B} (W : RelativeTaggedIsoScheme A B)

@[expose] def valid (p : SortedAssignment X P) : Prop :=
  (∀ i, FiberPartitionScheme (A i).tags (W.source i) p) ∧
  (∀ j, FiberPartitionScheme (B j).tags (W.target j) p) ∧
  (∀ i j, FiberBijectionScheme (W.source i j) (W.target j i) (W.graph i j) p) ∧
  (∀ i j, (A i).degree ≠ (B j).degree → ∀ u, appendAssignments p u ∉ W.source i j)

theorem valid_definable [Finite I] [Finite J] : SortedDefinableOver M S.carrier {p | W.valid p} := by
  let pairs := {ij : I × J // (A ij.1).degree ≠ (B ij.2).degree}
  have left := SortedDefinableOver.iInter (fun i =>
    fiberPartitionScheme_definable (A i).definable (W.sourceDefinable i))
  have right := SortedDefinableOver.iInter (fun j =>
    fiberPartitionScheme_definable (B j).definable (W.targetDefinable j))
  have graph := SortedDefinableOver.iInter (fun ij : I × J =>
    fiberBijectionScheme_definable (W.sourceDefinable ij.1 ij.2) (W.targetDefinable ij.2 ij.1)
      (W.graphDefinable ij.1 ij.2))
  have deg := SortedDefinableOver.iInter (fun ij : pairs =>
    definable_forall_assignments (W.sourceDefinable ij.val.1 ij.val.2).compl)
  convert left.inter (right.inter (graph.inter deg)) using 1
  ext p
  simp only [valid,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_compl_iff,Prod.forall]
  constructor
  · rintro ⟨l,r,g,d⟩
    exact ⟨l,r,g,fun ij u => d ij.val.1 ij.val.2 ij.property u⟩
  · rintro ⟨l,r,g,d⟩
    exact ⟨l,r,g,fun i j ne u => d ⟨(i,j),ne⟩ u⟩

@[expose] def descend [Finite (P .vf)] [Finite (P .rv)]
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) :
    RelativeTaggedIsoScheme (fun i => (A i).descend defH) (fun j => (B j).descend defH) where
  source i j := descendFiberScheme H (W.source i j)
  target j i := descendFiberScheme H (W.target j i)
  graph i j := descendRelationScheme H (W.graph i j)
  sourceDefinable i j := descendFiberScheme_definable defH (W.sourceDefinable i j)
  targetDefinable j i := descendFiberScheme_definable defH (W.targetDefinable j i)
  graphDefinable i j := descendRelationScheme_definable defH (W.graphDefinable i j)

abbrev FiberConstant {U : TCsort → Type}
    (H : SortedAssignment X P → SortedAssignment X Q → Prop)
    (p : SortedAssignment X P) (q : SortedAssignment X Q)
    (D : Set (SortedAssignment X (SumVariables P U))) : Prop :=
  ∀ p', H p' q → ∀ u, appendAssignments p u ∈ D ↔ appendAssignments p' u ∈ D

theorem descend_valid [Finite (P .vf)] [Finite (P .rv)]
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) {p : SortedAssignment X P} {q : SortedAssignment X Q}
    (hp : H p q)
    (constA : ∀ i, FiberConstant H p q (A i).tags)
    (constB : ∀ j, FiberConstant H p q (B j).tags)
    (constSource : ∀ i j, FiberConstant H p q (W.source i j))
    (constTarget : ∀ j i, FiberConstant H p q (W.target j i))
    (constGraph : ∀ i j p', H p' q → ∀ u v,
      appendAssignments (appendAssignments p u) v ∈ W.graph i j ↔
      appendAssignments (appendAssignments p' u) v ∈ W.graph i j)
    (valid : W.valid p) :
    (W.descend defH).valid q := by
  refine ⟨fun i => (valid.1 i).descend hp (constA i) (constSource i),
    fun j => (valid.2.1 j).descend hp (constB j) (constTarget j),
    fun i j => fiberBijectionScheme_descends hp (constSource i j) (constTarget j i) (constGraph i j) (valid.2.2.1 i j),
    ?_⟩
  intro i j ne u
  exact fun h => valid.2.2.2 i j ne u ((descendFiberScheme_at hp (constSource i j) u).1 h)

end RelativeTaggedIsoScheme

end GeneralizedEuler.Section5
