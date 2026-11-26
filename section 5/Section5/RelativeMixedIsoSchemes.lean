module

public import Section5.MixedTaggedGraphCuts
public import Section5.RelativeFiberPartitions
public import Section5.GeneratedParameterSchemes

/-! A named matrix of mixed isomorphisms records the source and target
cuts over one retained parameter tuple. Its validity has a first-order test. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}

structure RelativeMixedCarrier (M : SortedStructure L E X) (S : SortedSubstructure M) (P : TCsort → Type) where
  vars : TCsort → Type
  [finiteVars : ∀ s, Finite (vars s)]
  carrier : Set (SortedAssignment X (SumVariables P vars))
  definable : SortedDefinableOver M S.carrier carrier

attribute [instance] RelativeMixedCarrier.finiteVars

variable {I J : Type} (A : I → RelativeMixedCarrier M S P) (B : J → RelativeMixedCarrier M S P)

@[expose] def RelativeMixedCarrier.fibers [Finite I] (p : SortedAssignment X P) :
    MixedTaggedFamily M (M.termGenerated (namedTuple S p)) where
  Tag := I
  coordinates i := (A i).vars
  piece i := {x | appendAssignments p x ∈ (A i).carrier}
  definable i := definable_scheme_at_fiber p _ (A i).definable

structure RelativeMixedIsoScheme where
  source : ∀ i, J → Set (SortedAssignment X (SumVariables P (A i).vars))
  target : ∀ j, I → Set (SortedAssignment X (SumVariables P (B j).vars))
  graph : ∀ i j, Set (SortedAssignment X (SumVariables (SumVariables P (A i).vars) (B j).vars))
  sourceDefinable : ∀ i j, SortedDefinableOver M S.carrier (source i j)
  targetDefinable : ∀ j i, SortedDefinableOver M S.carrier (target j i)
  graphDefinable : ∀ i j, SortedDefinableOver M S.carrier (graph i j)

namespace RelativeMixedIsoScheme

variable {A B} (W : RelativeMixedIsoScheme A B)

@[expose] def valid (p : SortedAssignment X P) : Prop :=
  (∀ i, FiberPartitionScheme (A i).carrier (W.source i) p) ∧
  (∀ j, FiberPartitionScheme (B j).carrier (W.target j) p) ∧
  (∀ i j, FiberBijectionScheme (W.source i j) (W.target j i) (W.graph i j) p)

theorem valid_definable [Finite I] [Finite J] :
    SortedDefinableOver M S.carrier {p | W.valid p} := by
  have left := SortedDefinableOver.iInter (fun i =>
    fiberPartitionScheme_definable (A i).definable (W.sourceDefinable i))
  have right := SortedDefinableOver.iInter (fun j =>
    fiberPartitionScheme_definable (B j).definable (W.targetDefinable j))
  have graph := SortedDefinableOver.iInter (fun ij : I × J =>
    fiberBijectionScheme_definable (W.sourceDefinable ij.1 ij.2) (W.targetDefinable ij.2 ij.1)
      (W.graphDefinable ij.1 ij.2))
  convert left.inter (right.inter graph) using 1
  ext p
  simp only [valid,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Prod.forall]

theorem exists_of_fiber_iso [Finite I] [Finite J] (p : SortedAssignment X P)
    (iso : (RelativeMixedCarrier.fibers A p).Iso (RelativeMixedCarrier.fibers B p)) :
    ∃ C : RelativeMixedIsoScheme A B, C.valid p := by
  classical
  let U := RelativeMixedCarrier.fibers A p
  let V := RelativeMixedCarrier.fibers B p
  obtain ⟨f,df⟩ := iso
  choose left defLeft leftAt using fun i j =>
    definable_fiber_as_scheme p _ (U.sourceCut_definable V f df i j)
  choose right defRight rightAt using fun j i =>
    definable_fiber_as_scheme p _ (U.targetCut_definable V f df i j)
  let iso (i : U.Tag) (j : V.Tag) := Classical.choice (U.cuts_iso V f df i j)
  choose G defG atG using fun i j =>
    definable_relation_fiber_as_scheme p _ (iso i j).definable
  let C : RelativeMixedIsoScheme A B :=
    ⟨left,right,G,defLeft,defRight,defG⟩
  refine ⟨C,?_,?_,?_⟩
  · intro i
    obtain ⟨disj,cover⟩ := U.sourceCut_partition V f i
    refine ⟨fun u => ?_,fun j k ne u h => Set.disjoint_left.1 (disj ne) ((leftAt i j u).1 h.1) ((leftAt i k u).1 h.2)⟩
    change u ∈ U.piece i ↔ ∃ j, appendAssignments p u ∈ left i j
    have hu := congrArg (fun T : Set (SortedAssignment X (U.coordinates i)) => u ∈ T) cover
    exact hu.symm.to_iff.trans (Set.mem_iUnion.trans (exists_congr (fun j => (leftAt i j u).symm)))
  · intro j
    obtain ⟨disj,cover⟩ := U.targetCut_partition V f j
    refine ⟨fun v => ?_,fun i k ne v h => Set.disjoint_left.1 (disj ne) ((rightAt j i v).1 h.1) ((rightAt j k v).1 h.2)⟩
    change v ∈ V.piece j ↔ ∃ i, appendAssignments p v ∈ right j i
    have hv := congrArg (fun T : Set (SortedAssignment X (V.coordinates j)) => v ∈ T) cover
    exact hv.symm.to_iff.trans (Set.mem_iUnion.trans (exists_congr (fun i => (rightAt j i v).symm)))
  · intro i j
    let P₀ := {u | appendAssignments p u ∈ left i j}
    let Q₀ := {v | appendAssignments p v ∈ right j i}
    let e : P₀ ≃ Q₀ := (Equiv.subtypeEquivRight (leftAt i j)).trans
      ((iso i j).equiv.trans (Equiv.subtypeEquivRight (rightAt j i)).symm)
    apply fiberBijectionScheme_of_equiv p e
    intro x y
    exact (atG i j x y).trans ⟨fun ⟨h,eq⟩ => ⟨(leftAt i j x).2 h,eq⟩,
      fun ⟨h,eq⟩ => ⟨(leftAt i j x).1 h,eq⟩⟩

end RelativeMixedIsoScheme

end GeneralizedEuler.Section5
