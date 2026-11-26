module

public import Section5.RecordedFieldLabels
public import Section5.RVLabelFunctions
public import Section5.MixedFiniteFamilies

/-! A finite definable partition can be recorded by RV indicators.
The old mixed tuple is still recovered by dropping the indicators. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  {n k q : ℕ} {I : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

open scoped Classical in
@[expose] def fieldPartitionCode (D : Fin q → MixedCarrier Z n I) (a : SortedAssignment Z (MixedVariables n I)) :
    Fin q → RV0 O :=
  fun i => if a ∈ D i then 1 else 0

theorem fieldPartitionCode_graph (D : Fin q → MixedCarrier Z n I)
    (defD : ∀ i, SortedDefinableOver 𝓜 S.carrier (D i)) :
    DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment Z (MixedVariables n I)) (r : SortedAssignment Z (RVVariables (Fin q))) =>
        fieldPartitionCode D a = r .rv) := by
  classical
  let U := MixedVariables n I
  let R := RVVariables (Fin q)
  let W := SumVariables U R
  let defMark (i : Fin q) := (defD i).pullback_relabel (fun s => (Sum.inl : U s → W s))
  let defOne (i : Fin q) := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inr i) rvOneTerm
  let defZero (i : Fin q) := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inr i) rvZeroTerm
  have test := SortedDefinableOver.iInter (fun i => ((defMark i).inter (defOne i)).union ((defMark i).compl.inter (defZero i)))
  unfold DefinableRelation
  convert test using 1
  ext w
  let a : SortedAssignment Z U := fun s => w s ∘ Sum.inl
  let r : SortedAssignment Z R := fun s => w s ∘ Sum.inr
  have z : (rvZeroTerm : SortedTerm L E (WithBase S.carrier W) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (w s)) = 0 := realize_rvZeroTerm O hO power _
  have o : (rvOneTerm : SortedTerm L E (WithBase S.carrier W) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (w s)) = 1 := rfl
  simp only [Set.mem_iInter,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
  change fieldPartitionCode D a = r .rv ↔ ∀ i : Fin q,
    (a ∈ D i ∧ r .rv i = (rvOneTerm : SortedTerm L E (WithBase S.carrier W) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (w s))) ∨
    (a ∉ D i ∧ r .rv i = (rvZeroTerm : SortedTerm L E (WithBase S.carrier W) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (w s)))
  rw [o,z]
  refine ⟨?_,?_⟩
  · intro eq i
    have h := congrFun eq i
    by_cases m : a ∈ D i
    · exact Or.inl ⟨m,by simpa only [fieldPartitionCode,ite_eq_left m] using h.symm⟩
    · exact Or.inr ⟨m,by simpa only [fieldPartitionCode,ite_eq_right m] using h.symm⟩
  · intro tests
    funext i
    rcases tests i with ⟨m,h⟩ | ⟨m,h⟩
    · simpa only [fieldPartitionCode,ite_eq_left m] using h.symm
    · simpa only [fieldPartitionCode,ite_eq_right m] using h.symm

@[expose] def fieldPartitionTag (i : Fin q) : Set (Fin q ⊕ I → RV0 O) :=
  {r | r (.inl i) = 1 ∧ ∀ j ≠ i, r (.inl j) = 0}

theorem fieldPartitionTag_definable (i : Fin q) : isRVSet 𝓜 S (fieldPartitionTag (I := I) (O := O) i) := by
  let R := RVVariables (Fin q ⊕ I)
  let one := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := R) .rv (.inl i) rvOneTerm
  let other := SortedDefinableOver.iInter (fun j : {j : Fin q // j ≠ i} =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := R) .rv (.inl j.val) rvZeroTerm)
  unfold isRVSet
  convert one.inter other using 1
  ext r
  have o : (rvOneTerm : SortedTerm L E (WithBase S.carrier R) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (r s)) = 1 := rfl
  have z : (rvZeroTerm : SortedTerm L E (WithBase S.carrier R) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (r s)) = 0 := realize_rvZeroTerm O hO power _
  simp only [Set.mem_iInter,Set.mem_inter_iff,Subtype.forall]
  change (r .rv (.inl i) = 1 ∧ ∀ j ≠ i, r .rv (.inl j) = 0) ↔
    (r .rv (.inl i) = (rvOneTerm : SortedTerm L E (WithBase S.carrier R) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (r s)) ∧
    ∀ j ≠ i, r .rv (.inl j) = (rvZeroTerm : SortedTerm L E (WithBase S.carrier R) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (r s)))
  rw [o,z]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem fieldPartitionTag_disjoint :
    Pairwise (fun i j : Fin q => Disjoint (fieldPartitionTag (I := I) (O := O) i) (fieldPartitionTag j)) := by
  intro i j ne
  apply Set.disjoint_left.2
  intro r hi hj
  exact WithZero.coe_ne_zero (a := (1 : RV O)) ((hi.1).symm.trans (hj.2 i ne))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem fieldPartitionTag_code_iff (D : Fin q → MixedCarrier Z n I)
    (disj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (a : SortedAssignment Z (MixedVariables n I)) (r : Fin q ⊕ I → RV0 O)
    (code : r ∘ Sum.inl = fieldPartitionCode D a) (i : Fin q) :
    r ∈ fieldPartitionTag i ↔ a ∈ D i := by
  classical
  have nz : (1 : RV0 O) ≠ 0 := WithZero.coe_ne_zero (a := (1 : RV O))
  constructor
  · intro hr
    by_contra notMem
    have e := congrFun code i
    exact nz (hr.1.symm.trans (e.trans (ite_eq_right notMem)))
  · intro m
    refine ⟨(congrFun code i).trans (ite_eq_left m),?_⟩
    intro j ne
    have outside : a ∉ D j := fun inJ => Set.disjoint_left.1 (disj ne) inJ m
    exact (congrFun code j).trans (ite_eq_right outside)

end GeneralizedEuler.Section5
