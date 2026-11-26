module

public import Section5.GluedRelativeBlowup
public import Section5.GluedRelativeIsomorphisms
import all Section4.Objects

/-! Label rows carry their fixed-base defining formulas and fiber
bounds. Their glued class is independent of the chosen realization. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {h t : ℕ}

structure RelativeRVIndex (M : SortedStructure L E X) (S : SortedSubstructure M) (h t : ℕ) where
  labels : Set (Fin h → X .rv)
  definable : isRVSet M S labels
  select : Fin t → Fin h
  active : ∀ p ∈ labels, ∀ i, p (select i) ≠ M.funMap .rvZero (fun j => j.elim0)
  finite : ∀ y, {p ∈ labels | p ∘ select = y}.Finite

structure RelativeRVRow (I : RelativeRVIndex M S h t) (k : ℕ) where
  arity : ℕ
  tags : Set (SortedAssignment X (SumVariables (RVVariables (Fin h)) (RVVariables (Fin arity))))
  tagsDefinable : SortedDefinableOver M S.carrier tags
  graph : Set (SortedAssignment X
    (SumVariables (SumVariables (RVVariables (Fin h)) (RVVariables (Fin arity))) (RVVariables (Fin k))))
  graphDefinable : SortedDefinableOver M S.carrier graph
  valid : ∀ p ∈ I.labels, ∃ b, RelativeRVWitness tags graph (M.funMap .rvZero (fun j => j.elim0)) b (rvTupleAssignment p)

namespace RelativeRVRow

variable {I : RelativeRVIndex M S h t} {k : ℕ} (A : RelativeRVRow I k)

private theorem global_object :
    ∃ W : RVObject M S (t+k), ∃ ea : W.arity = h+A.arity,
      (∀ x : Fin (h+A.arity) → X .rv, x ∘ Fin.cast ea ∈ W.carrier ↔ x ∈ gluedRVTags I.labels A.tags) ∧
      ∀ x : W.carrier,
        RVObject.labelGraphTuple (x.val ∘ Fin.cast ea.symm) (W.label x) ∈ gluedRVGraph I.select I.labels A.graph :=
  gluedRVObject_exists I.select I.definable A.tagsDefinable A.graphDefinable I.active I.finite A.valid

def object : RVObject M S (t+k) := (global_object A).choose

theorem object_carrier_equiv :
    RVDefinablyEquivalent M S.carrier A.object.carrier (gluedRVTags I.labels A.tags) := by
  obtain ⟨ea,car,_⟩ := (global_object A).choose_spec
  exact rv_cast_carrier_equiv A.object ea _ car

@[expose] def gluedClass : RVSemiring M S := objectClass M S ⟨_,A.object⟩

theorem gluedClass_eq_of_carrier_equiv (B : RelativeRVRow I k)
    (iso : RVDefinablyEquivalent M S.carrier (gluedRVTags I.labels A.tags) (gluedRVTags I.labels B.tags)) :
    A.gluedClass = B.gluedClass := by
  apply scissors_sound M S
  exact RVRelation.iso _ _ (A.object_carrier_equiv.trans (iso.trans B.object_carrier_equiv.symm))

theorem gluedClass_eq_of_fiber_isomorphism (B : RelativeRVRow I k)
    {G : Set (SortedAssignment X
      (SumVariables (SumVariables (RVVariables (Fin h)) (RVVariables (Fin A.arity))) (RVVariables (Fin B.arity))))}
    (defG : SortedDefinableOver M S.carrier G)
    (valid : ∀ p : SortedAssignment X (RVVariables (Fin h)), p .rv ∈ I.labels → FiberBijectionScheme A.tags B.tags G p) :
    A.gluedClass = B.gluedClass := by
  obtain ⟨e,he,_⟩ := gluedRVTags_equiv_of_fiber_schemes I.definable defG valid
  exact A.gluedClass_eq_of_carrier_equiv B ⟨e,he⟩


omit A in
abbrev DeletedBound (A : RelativeRVRow I (k+1)) (j : Fin (k+1)) : Prop :=
  ∀ (p : Fin h → X .rv), p ∈ I.labels →
    ∃ b, RelativeRVWitness A.tags (relativeDeleteLabelGraph j A.graph)
      (M.funMap .rvZero (fun i => i.elim0)) b (rvTupleAssignment p)

omit A in
@[expose] def lowerRow (A : RelativeRVRow I (k+1)) (j : Fin (k+1)) (hdel : A.DeletedBound j) : RelativeRVRow I k where
  arity := A.arity
  tags := A.tags
  tagsDefinable := A.tagsDefinable
  graph := relativeDeleteLabelGraph j A.graph
  graphDefinable := relativeDeleteLabelGraph_definable j A.graphDefinable
  valid := hdel

end RelativeRVRow

section Canonical

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S₀.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power

namespace RelativeRVRow

variable {I : RelativeRVIndex (X := CanonicalSort O) (canonicalStructure (L := L) O hO power) S₀ h t}
  {k : ℕ} (A : RelativeRVRow I (k+1)) (j : Fin (k+1))

@[expose] def upperRow (hdel : A.DeletedBound j) : RelativeRVRow I (k+1) where
  arity := A.arity + 1
  tags := relativePositiveTags O A.tags
  tagsDefinable := relativePositiveTags_definable O (S := S₀) neg A.tagsDefinable
  graph := relativePositiveGraph O j A.tags A.graph
  graphDefinable := relativePositiveGraph_definable O (S := S₀) j neg A.tagsDefinable A.graphDefinable
  valid := by
    intro p hp
    obtain ⟨_,hv⟩ := A.valid p hp
    obtain ⟨b,hd⟩ := hdel p hp
    exact ⟨b,relativePositiveGraph_valid O j hv hd⟩

theorem glued_row_blowup (hdel : A.DeletedBound j) (C : RelativeRVRow I (k+1))
    (posIso : RVDefinablyEquivalent 𝓜 S₀.carrier
      (gluedRVTags I.labels (relativePositiveTags O (P := RVVariables (Fin h)) (m := A.arity) A.tags))
      (gluedRVTags I.labels C.tags)) :
    ElementaryClassStep O hO power S₀ neg A.gluedClass
      ((A.lowerRow j hdel).gluedClass + C.gluedClass) := by
  have valid : ∀ p ∈ I.labels, ∃ a b, RelativeRVWitness A.tags A.graph 0 a (rvTupleAssignment p) ∧
      RelativeRVWitness A.tags (relativeDeleteLabelGraph j A.graph) 0 b (rvTupleAssignment p) := by
    intro p hp
    obtain ⟨a,ha⟩ := A.valid p hp
    obtain ⟨b,hb⟩ := hdel p hp
    exact ⟨a,b,ha,hb⟩
  obtain ⟨W,Z,N,hW,hZ,hN,step⟩ := glued_relative_elementary_step O hO power S₀ neg j I.select
    I.definable A.tagsDefinable A.graphDefinable I.active I.finite valid
  let B := A.lowerRow j hdel
  have eW : objectClass 𝓜 S₀ ⟨_,W⟩ = A.gluedClass :=
    scissors_sound 𝓜 S₀ (.iso _ _ (hW.trans A.object_carrier_equiv.symm))
  have eZ : objectClass 𝓜 S₀ ⟨_,Z⟩ = B.gluedClass :=
    scissors_sound 𝓜 S₀ (.iso _ _ (hZ.trans B.object_carrier_equiv.symm))
  have eN : objectClass 𝓜 S₀ ⟨_,N⟩ = C.gluedClass :=
    scissors_sound 𝓜 S₀ (.iso _ _ (hN.trans (posIso.trans C.object_carrier_equiv.symm)))
  rwa [eW,eZ,eN] at step

end RelativeRVRow

end Canonical

end GeneralizedEuler.Section5
