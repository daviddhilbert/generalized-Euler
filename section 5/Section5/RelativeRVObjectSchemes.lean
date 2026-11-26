module

public import Section5.RelativeRVObjectRealization
public import Section5.RelativeTaggedIsomorphisms
public import Section5.RelativeElementarySchemes
import all Section4.Objects

/-! The tag carrier, structure graph, and finite bound of a homogeneous
RV object can be used as a single witness scheme. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P Q : TCsort → Type}
  {k h t : ℕ}

structure RelativeRVObjectScheme (M : SortedStructure L E X) (S : SortedSubstructure M)
    (P : TCsort → Type) where
  data : RelativeRVTags M S P
  graph : Set (SortedAssignment X (SumVariables (SumVariables P data.Vars) (RVVariables (Fin data.degree))))
  definable : SortedDefinableOver M S.carrier graph
  bound : ℕ

namespace RelativeRVObjectScheme

variable (W : RelativeRVObjectScheme M S P) (zero : S.carrier .rv)

@[expose] def valid (p : SortedAssignment X P) : Prop :=
  RelativeRVWitness W.data.tags W.graph zero.val W.bound p

theorem valid_definable : SortedDefinableOver M S.carrier {p | W.valid zero p} :=
  relativeRVWitness_definable W.data.definable W.definable zero W.bound

variable (hzero : zero.val = M.funMap .rvZero (fun j => j.elim0))

@[expose] def realize (p : SortedAssignment X P) (v : W.valid zero p) :
    RVObject M (M.termGenerated (namedTuple S p)) W.data.degree :=
  realizedRelativeRVObject (bound := W.bound) p W.data.definable W.definable
    (by simpa only [valid,hzero] using v)

@[expose] def descend [Finite (P .vf)] [Finite (P .rv)]
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) : RelativeRVObjectScheme M S Q where
  data := W.data.descend defH
  graph := descendRelationScheme H W.graph
  definable := descendRelationScheme_definable defH W.definable
  bound := W.bound

theorem descend_valid [Finite (P .vf)] [Finite (P .rv)]
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) {p : SortedAssignment X P} {q : SortedAssignment X Q}
    (hp : H p q) (constD : RelativeTaggedIsoScheme.FiberConstant H p q W.data.tags)
    (constG : ∀ p', H p' q → ∀ u v, appendAssignments (appendAssignments p u) v ∈ W.graph ↔
      appendAssignments (appendAssignments p' u) v ∈ W.graph)
    (v : W.valid zero p) : (W.descend defH).valid zero q :=
  relativeRVWitness_descends hp constD constG v

omit W in
@[expose] def row (A : RelativeRVObjectScheme M S (RVVariables (Fin h))) (I : RelativeRVIndex M S h t)
    (v : ∀ p ∈ I.labels, A.valid zero (rvTupleAssignment p)) : RelativeRVRow I A.data.degree where
  arity := A.data.arity
  tags := A.data.tags
  tagsDefinable := A.data.definable
  graph := A.graph
  graphDefinable := A.definable
  valid p hp := ⟨A.bound,hzero ▸ v p hp⟩

omit W zero hzero in
@[expose] def ofElementary (A : RelativeElementaryScheme M S P k) : RelativeRVObjectScheme M S P :=
  ⟨⟨k+1,A.arity,A.tags,A.tagsDefinable⟩,A.graph,A.graphDefinable,A.sourceBound⟩

omit W zero hzero in
@[expose] def ofElementaryLower (A : RelativeElementaryScheme M S P k) : RelativeRVObjectScheme M S P :=
  ⟨⟨k,A.arity,A.tags,A.tagsDefinable⟩,relativeDeleteLabelGraph A.slot A.graph,
    relativeDeleteLabelGraph_definable A.slot A.graphDefinable,A.deletionBound⟩

end RelativeRVObjectScheme

theorem relative_rv_object_scheme_of_actual (p : SortedAssignment X P)
    (zero : S.carrier .rv) (hzero : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (A : RVObject M (M.termGenerated (namedTuple S p)) k)
    (sat : let T := M.termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes M (WithBase T.carrier (RVVariables (Fin k)))
        (BaseAssignments T.carrier (RVVariables (Fin k)))) :
    ∃ (W : RelativeRVObjectScheme M S P) (v : W.valid zero p),
      objectClass M (M.termGenerated (namedTuple S p)) ⟨W.data.degree,W.realize zero hzero p v⟩ =
        objectClass M (M.termGenerated (namedTuple S p)) ⟨k,A⟩ := by
  obtain ⟨D,G,defD,defG,hD,hG⟩ := relative_rv_labels_of_object p A
  obtain ⟨b,hb⟩ := rvObject_uniform_label_bound A sat
  let W : RelativeRVObjectScheme M S P := ⟨⟨k,A.arity,D,defD⟩,G,defG,b⟩
  have v : W.valid zero p := relativeRVWitness_of_labelRelation p A hD hG zero.val hzero b hb
  refine ⟨W,v,scissors_sound M _ (.iso _ _ ?_)⟩
  have eq : (W.realize zero hzero p v).carrier = A.carrier := by
    ext a
    exact hD (rvTupleAssignment a)
  change RVDefinablyEquivalent M (M.termGenerated (namedTuple S p)).carrier (W.realize zero hzero p v).carrier A.carrier
  rw [eq]
  exact ⟨Equiv.refl _,definable_identity_label M _ A.definable⟩

section Canonical

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S₀.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def RelativeRVObjectScheme.ofElementaryUpper
    (A : RelativeElementaryScheme 𝓜 S₀ P k) : RelativeRVObjectScheme 𝓜 S₀ P :=
  ⟨⟨k+1,A.arity+1,relativePositiveTags O A.tags,relativePositiveTags_definable O neg A.tagsDefinable⟩,
    relativePositiveGraph O A.slot A.tags A.graph,
    relativePositiveGraph_definable O A.slot neg A.tagsDefinable A.graphDefinable,A.deletionBound⟩

theorem RelativeRVObjectScheme.ofElementaryUpper_valid
    (A : RelativeElementaryScheme 𝓜 S₀ P k) (zero : S₀.carrier .rv) (hz : zero.val = 0)
    (p : SortedAssignment (CanonicalSort O) P) (v : A.valid zero p) :
    (ofElementaryUpper O hO power S₀ neg A).valid zero p := by
  simpa only [RelativeElementaryScheme.valid,RelativeRVObjectScheme.valid,ofElementaryUpper,hz] using
    (relativePositiveGraph_valid O A.slot
      (show RelativeRVWitness A.tags A.graph 0 A.sourceBound p from hz ▸ v.1)
      (show RelativeRVWitness A.tags (relativeDeleteLabelGraph A.slot A.graph) 0 A.deletionBound p from hz ▸ v.2))

end Canonical

end GeneralizedEuler.Section5
