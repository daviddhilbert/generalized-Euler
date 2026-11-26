module

public import Section5.TerminalTagPartitions
public import Section5.ArbitraryContractionOrders

/-! Contraction order comparisons glue over a finite partition of
the original tags. Each part may use its own preparations. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

section Generic

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

theorem RetainedFieldFamily.restrictTags_permuteVF
    (A : RetainedFieldFamily M S n k) (p : Equiv.Perm (Fin n))
    (D : Set (A.tags → RV0 O)) (d : isRVSet M S D) :
    (A.restrictTags D d).permuteVF p = (A.permuteVF p).restrictTags D d := by
  have carriers : ((A.restrictTags D d).permuteVF p).carrier = ((A.permuteVF p).restrictTags D d).carrier := by
    ext a
    rfl
  unfold RetainedFieldFamily.restrictTags RetainedFieldFamily.permuteVF at carriers ⊢
  congr

end Generic

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)
  {n k l a b : ℕ} {I : Type} [Fintype I]

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem contraction_comparison_of_tag_partition
    (A : RetainedFieldFamily 𝓜 S n k) (p : Equiv.Perm (Fin n))
    (D : I → Set (A.tags → RV0 O)) (defD : ∀ i, isRVSet 𝓜 S (D i))
    (disj : Pairwise (fun i j => Disjoint (D i) (D j))) (cover : ∀ x, ∃ i, x ∈ D i)
    (localComparison : ∀ i (B C : RetainedFieldFamily 𝓜 S 0 l)
      (ib : Fin a ≃ B.tags) (ic : Fin b ≃ C.tags),
      HeadContractionRun (A.restrictTags (D i) (defD i)) B →
      HeadContractionRun ((A.restrictTags (D i) (defD i)).permuteVF p) C →
      terminalCommonBlowup S neg B C ib ic)
    {U V : RetainedFieldFamily 𝓜 S 0 l} (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags)
    (left : HeadContractionRun A U) (right : HeadContractionRun (A.permuteVF p) V) :
    terminalCommonBlowup S neg U V idx idy := by
  obtain ⟨readU,u⟩ := left.restrictRuns
  obtain ⟨readV,v⟩ := right.restrictRuns
  let traceU (i : I) : Set (U.tags → RV0 O) := {t | t ∘ readU ∈ D i}
  let traceV (i : I) : Set (V.tags → RV0 O) := {t | t ∘ readV ∈ D i}
  have defU (i : I) : isRVSet 𝓜 S (traceU i) := isRVSet_precomp readU (defD i)
  have defV (i : I) : isRVSet 𝓜 S (traceV i) := isRVSet_precomp readV (defD i)
  have du : Pairwise (fun i j => Disjoint (traceU i) (traceU j)) := by
    intro i j h
    exact Set.disjoint_left.2 (fun _ ht hs => Set.disjoint_left.1 (disj h) ht hs)
  have dv : Pairwise (fun i j => Disjoint (traceV i) (traceV j)) := by
    intro i j h
    exact Set.disjoint_left.2 (fun _ ht hs => Set.disjoint_left.1 (disj h) ht hs)
  let P (i : I) := U.restrictTags (traceU i) (defU i)
  let Q (i : I) := V.restrictTags (traceV i) (defV i)
  have each (i : I) : terminalCommonBlowup S neg (P i) (Q i) idx idy := by
    apply localComparison i (P i) (Q i) idx idy (u (D i) (defD i))
    rw [A.restrictTags_permuteVF]
    exact v (D i) (defD i)
  have sumU := U.terminalGradedClass_tag_partition idx (baseRVZero S) rfl traceU defU du (fun t _ => cover (t ∘ readU))
  have sumV := V.terminalGradedClass_tag_partition idy (baseRVZero S) rfl traceV defV dv (fun t _ => cover (t ∘ readV))
  unfold terminalCommonBlowup at each ⊢
  rw [sumU,sumV]
  let proj := (gradedBlowupCongruence O hO power S neg).mk'
  apply Quotient.exact (s := (gradedBlowupCongruence O hO power S neg).toSetoid)
  change proj (∑ i, (P i).terminalGradedClass idx (baseRVZero S) rfl) =
    proj (∑ i, (Q i).terminalGradedClass idy (baseRVZero S) rfl)
  rw [map_sum,map_sum]
  exact Finset.sum_congr rfl (fun i _ => Quotient.sound (each i))

end GeneralizedEuler.Section5
