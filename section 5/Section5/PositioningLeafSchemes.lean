module

public import Section5.PositioningLeafConditions

/-! A single RV label records which leaf contains a point in the
domain. Definable validity tests let compactness choose finitely
many such label schemes over the original parameter set. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

structure PositioningLeafScheme {L : Language} {E : Type*} {X : TCsort → Type z}
    (M : SortedStructure L E X) (S : SortedSubstructure M) (P : TCsort → Type) where
  arity : ℕ
  leaves : Set (SortedAssignment X (SumVariables (SumVariables P (RVVariables (Fin arity))) (MixedVariables 1 Empty)))
  definable : SortedDefinableOver M S.carrier leaves

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {P : TCsort → Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty
local notation "PV" => SumVariables P U
local notation "PVV" => SumVariables PV U

namespace PositioningLeafScheme

variable (W : PositioningLeafScheme (canonicalStructure (L := L) O hO power) S P)

local notation "R" => RVVariables (Fin W.arity)
local notation "Q" => SumVariables P R

@[expose] def graphLift
    (G : Set (SortedAssignment Z PVV)) : Set (SortedAssignment Z (SumVariables (SumVariables Q U) U)) :=
  {a | (fun s => a s ∘
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)) Sum.inr) ∈ G}

theorem graphLift_definable {G : Set (SortedAssignment Z PVV)}
    (g : SortedDefinableOver 𝓜 S.carrier G) : SortedDefinableOver 𝓜 S.carrier (W.graphLift O hO power S G) :=
  g.pullback_relabel _

@[expose] def valid
    (D : Set (SortedAssignment Z PV)) (G : Set (SortedAssignment Z PVV)) (p : SortedAssignment Z P) : Prop :=
  (∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔
    ∃ r : SortedAssignment Z R, appendAssignments (appendAssignments p r) a ∈ W.leaves) ∧
  (∀ (a : fieldAssignment 1 Z) (r s : SortedAssignment Z R),
    appendAssignments (appendAssignments p r) a ∈ W.leaves →
    appendAssignments (appendAssignments p s) a ∈ W.leaves → r = s) ∧
  ∀ r : SortedAssignment Z R, positioningLeafValid O W.leaves (W.graphLift O hO power S G) (appendAssignments p r)

theorem valid_definable
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {D : Set (SortedAssignment Z PV)} {G : Set (SortedAssignment Z PVV)}
    (d : SortedDefinableOver 𝓜 S.carrier D) (g : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier {p | W.valid O hO power S D G p} := by
  let transpose (s : TCsort) : SumVariables Q U s → SumVariables PV R s :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  let C := {a : SortedAssignment Z (SumVariables PV R) | (fun s => a s ∘ transpose s) ∈ W.leaves}
  have dc : SortedDefinableOver 𝓜 S.carrier C := W.definable.pullback_relabel transpose
  have cover := definable_forall_iff_exists D C d dc
  have unique := definable_fiberwise_functional C dc
  have leaves := definable_forall_assignments
    (positioningLeafValid_definable O hO power S F minusOne hm hF W.definable (W.graphLift_definable O hO power S g))
  convert cover.inter (unique.inter leaves) using 1
  ext p
  have eq (a : fieldAssignment 1 Z) (r : SortedAssignment Z R) :
      (fun s => appendAssignments (appendAssignments p a) r s ∘ transpose s) =
      appendAssignments (appendAssignments p r) a := by
    funext s i
    rcases i with (i | i) | i <;> rfl
  simp only [valid,Set.mem_inter_iff,Set.mem_ofPred_eq,C,eq]

end PositioningLeafScheme

theorem uniform_positioning_leaf_schemes
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (A : Set (SortedAssignment Z P)) (a : SortedDefinableOver 𝓜 S.carrier A)
    (D : Set (SortedAssignment Z PV)) (G : Set (SortedAssignment Z PVV))
    (d : SortedDefinableOver 𝓜 S.carrier D) (g : SortedDefinableOver 𝓜 S.carrier G)
    (pointwise : ∀ p ∈ A, ∃ W : PositioningLeafScheme 𝓜 S P, W.valid O hO power S D G p) :
    ∃ (C : Finset (PositioningLeafScheme 𝓜 S P)) (parts : C → Set (SortedAssignment Z P)),
      (∀ i, SortedDefinableOver 𝓜 S.carrier (parts i)) ∧
      (∀ i p, p ∈ parts i → i.val.valid O hO power S D G p) ∧
      Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧ (⋃ i, parts i) = A :=
  finite_definable_partition_of_cover sat A a (fun (i : PositioningLeafScheme 𝓜 S P) => {p | i.valid O hO power S D G p})
    (fun i => i.valid_definable O hO power S F minusOne hm hF d g) pointwise

end GeneralizedEuler.Section5
