module

public import Section5.FieldCutAnnotations
public import Section5.TerminalTagPartitions
public import Section5.RelativelyUnaryContractions
public import Section5.StandardHeadContractions

/-! The class modulo common blowups is additive over an arbitrary
finite definable partition of a field family. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n k l a b q : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

theorem contraction_runs_commonBlowup_of_field_fixed
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k}
    (f : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier})
    (fix : ∀ a, (f.equiv a).val .vf = a.val .vf)
    (keep : ∀ a, (f.equiv a).val .rv ∘ B.select = a.val .rv ∘ A.select)
    {U V : RetainedFieldFamily 𝓜 S 0 l} (iu : Fin a ≃ U.tags) (iv : Fin b ≃ V.tags)
    (u : HeadContractionRun A U) (v : HeadContractionRun B V) :
    terminalCommonBlowup S neg U V iu iv := by
  cases u with
  | next H rH =>
    cases v with
    | next J rJ =>
      let : Finite H.target.tags := H.target.finiteTags
      let : Finite J.target.tags := J.target.finiteTags
      let ia : Fin (Nat.card H.target.tags) ≃ H.target.tags := (Finite.equivFin _).symm
      let ib : Fin (Nat.card J.target.tags) ≃ J.target.tags := (Finite.equivFin _).symm
      exact relativelyUnary_contraction_runs_commonBlowup S neg hyp H J ia ib rH rJ iu iv f
        (fun a => congrArg (· ∘ Fin.succ) (fix a)) keep

theorem contraction_class_partition
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S (n+1) k)
    (D : Fin q → MixedCarrier Z (n+1) A.tags) (d : ∀ i, SortedDefinableOver 𝓜 S.carrier (D i))
    (sub : ∀ i, D i ⊆ {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier})
    (disj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (cover : ∀ a : SortedAssignment Z (MixedVariables (n+1) A.tags), mixedTuple a ∈ A.carrier → ∃ i, a ∈ D i)
    {U : RetainedFieldFamily 𝓜 S 0 l} (iu : Fin a ≃ U.tags) (u : HeadContractionRun A U)
    (V : Fin q → RetainedFieldFamily 𝓜 S 0 l) (v : ∀ i, HeadContractionRun (A.cutCarrier (D i) (d i) (sub i)) (V i))
    (b : Fin q → ℕ) (iv : ∀ i, Fin (b i) ≃ (V i).tags) :
    ((Q).mk') (U.terminalGradedClass iu (baseRVZero S) rfl) =
      ∑ i, ((Q).mk') ((V i).terminalGradedClass (iv i) (baseRVZero S) rfl) := by
  obtain ⟨B,Bcut,defB,disjB,coverB,⟨e,fix,keep⟩,localIso⟩ := field_cut_annotation A D d sub disj cover
  have count := u.selected_count
  subst l
  have heads (m j : ℕ) (C : RetainedFieldFamily 𝓜 S (m+1) j) : Nonempty (HeadContractionData C) :=
    head_contraction_data_exists hO power S head.minusOne head.minusOne_realizes head.fieldTerms head.fieldTerms_realize
      C (head.saturated m C.tags C.finiteTags) (head.immediate m)
  obtain ⟨W,w⟩ := HeadContractionRun.exists_run heads B
  let : Finite W.tags := W.finiteTags
  let iw : Fin (Nat.card W.tags) ≃ W.tags := (Finite.equivFin _).symm
  obtain ⟨read,source,runs⟩ := w.restrictRuns_with_source
  let T (i : Fin q) : Set (W.tags → RV0 O) := {t | t ∘ read ∈ Bcut i}
  let defT (i : Fin q) : isRVSet 𝓜 S (T i) := isRVSet_precomp read (defB i)
  let R (i : Fin q) := W.restrictTags (T i) (defT i)
  have all (t : W.tags → RV0 O) (ht : (Fin.elim0,t) ∈ W.carrier) : ∃ i, t ∈ T i := by
    obtain ⟨b,hb⟩ := source t ht
    exact coverB b (t ∘ read) hb
  have disjoint : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j ne
    exact Set.disjoint_left.2 (fun _ ht hs => Set.disjoint_left.1 (disjB ne) ht hs)
  have a := contraction_runs_commonBlowup_of_field_fixed S neg hyp e fix keep iu iw u w
  have part := W.terminalGradedClass_tag_partition iw (baseRVZero S) rfl T defT disjoint all
  have each (i : Fin q) : terminalCommonBlowup S neg (V i) (R i) (iv i) iw := by
    obtain ⟨fi,vi,ti⟩ := localIso i
    exact contraction_runs_commonBlowup_of_field_fixed S neg hyp fi vi ti (U := V i) (V := R i) (iv i) iw (v i) (runs (Bcut i) (defB i))
  have first : ((Q).mk') (U.terminalGradedClass iu (baseRVZero S) rfl) =
      ((Q).mk') (W.terminalGradedClass iw (baseRVZero S) rfl) := Quotient.sound a
  have middle : ((Q).mk') (W.terminalGradedClass iw (baseRVZero S) rfl) =
      ∑ i, ((Q).mk') ((R i).terminalGradedClass iw (baseRVZero S) rfl) := by
    rw [part,map_sum]
  have last (i : Fin q) : ((Q).mk') ((R i).terminalGradedClass iw (baseRVZero S) rfl) =
      ((Q).mk') ((V i).terminalGradedClass (iv i) (baseRVZero S) rfl) :=
    (Quotient.sound (each i)).symm
  exact first.trans (middle.trans (Finset.sum_congr rfl (fun i _ => last i)))

end GeneralizedEuler.Section5
