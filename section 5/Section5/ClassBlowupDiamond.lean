module

public import Section5.MarkedBlowupLocus
import all Section4.Objects

/-! The one-step diamond on positive graded classes. The initial class
equality supplies a definable isomorphism across all tags and degrees. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (hneg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cls" => objectClass 𝓜 S
local notation "p" => residuePointClass O hO power S
local notation "q" => multiplierClass O hO power S hneg
local notation "step" => ElementaryClassStep O hO power S hneg

private theorem lower_classes_match {k l : ℕ} (A : RVObject 𝓜 S k) (B : RVObject 𝓜 S l)
    (iso : RVDefinablyEquivalent 𝓜 S.carrier A.carrier B.carrier)
    (degree : A.carrier.Nonempty → k = l) :
    cls ⟨k,A⟩ = cls ⟨l,B⟩ := by
  by_cases h : A.carrier.Nonempty
  · cases degree h
    exact scissors_sound 𝓜 S (RVRelation.iso _ _ iso)
  · have emptyA := Set.not_nonempty_iff_eq_empty.1 h
    have emptyB : B.carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro y hy
      let x := iso.choose.symm ⟨y,hy⟩
      exact h ⟨x.val,x.property⟩
    exact (scissors_sound 𝓜 S (RVRelation.zero A emptyA)).trans
      (scissors_sound 𝓜 S (RVRelation.zero B emptyB)).symm

/-- Two elementary steps with the same initial graded class have a
common refinement with one further elementary step on each side.
The step is the identity when its exclusive locus is empty. -/
theorem elementaryClassStep_diamond {a b c : RVSemiring 𝓜 S}
    (hab : step a b) (hac : step a c) : ∃ d, step b d ∧ step c d := by
  classical
  rcases hab with e | ⟨W,P,ha,hb⟩
  · subst b
    exact ⟨c,hac,Or.inl rfl⟩
  rcases hac with e | ⟨Z,Q,ha',hc⟩
  · subst c
    exact ⟨b,Or.inl rfl,Or.inr ⟨W,P,ha,hb⟩⟩
  obtain ⟨m,A,hP⟩ := positive_class_represented 𝓜 S P
  obtain ⟨n,B,hQ⟩ := positive_class_represented 𝓜 S Q
  let U := markBlowupLocus O hO power S W A
  let V := markBlowupLocus O hO power S Z B
  have initial : ∑ i, cls (U i) = ∑ j, cls (V j) := by
    rw [markBlowupLocus_class O hO power S W A,markBlowupLocus_class O hO power S Z B,← hP,← hQ]
    exact ha.symm.trans ha'
  obtain ⟨e,degree,graph⟩ := equal_graded_classes_tagged_iso 𝓜 S U V initial
  let back := RVFamily.inverse_graph _ _ e graph
  let left (i : Option (Fin m)) (j : Option (Fin n)) :=
    cls ⟨(U i).1,sourceCutObject U V e graph i j⟩
  let right (j : Option (Fin n)) (i : Option (Fin m)) :=
    cls ⟨(V j).1,sourceCutObject V U e.symm back j i⟩
  have matchCut (i) (j) : left i j = right j i :=
    sourceCutObject_match U V e graph degree i j
  let lo (j : Option (Fin n)) : GradedObject 𝓜 S :=
    ⟨W.1,markedCenterPiece O hO power S W A V e graph j⟩
  let ro (i : Option (Fin m)) : GradedObject 𝓜 S :=
    ⟨Z.1,markedCenterPiece O hO power S Z B U e.symm back i⟩
  have raiseLeft (j) : left none j = cls (lo j) * p :=
    markedCenterPiece_raised_class O hO power S W A V e graph j
  have raiseRight (i) : right none i = cls (ro i) * p :=
    markedCenterPiece_raised_class O hO power S Z B U e.symm back i
  obtain ⟨D,hD⟩ := markedCenter_union_class O hO power S W A V e graph
    (⟨Option.some,Option.some_injective _⟩ : Fin n ↪ Option (Fin n))
  obtain ⟨C,hC⟩ := markedCenter_union_class O hO power S Z B U e.symm back
    (⟨Option.some,Option.some_injective _⟩ : Fin m ↪ Option (Fin m))
  let Wonly : GradedObject 𝓜 S := ⟨W.1,D⟩
  let Zonly : GradedObject 𝓜 S := ⟨Z.1,C⟩
  change cls Wonly = ∑ j : Fin n, cls (lo (some j)) at hD
  change cls Zonly = ∑ i : Fin m, cls (ro (some i)) at hC
  have sumW : cls W = cls (lo none) + cls Wonly := by
    rw [markedCenterPiece_sum O hO power S W A V e graph,Fintype.sum_option]
    exact congrArg (cls (lo none) + ·) hD.symm
  have sumZ : cls Z = cls (ro none) + cls Zonly := by
    rw [markedCenterPiece_sum O hO power S Z B U e.symm back,Fintype.sum_option]
    exact congrArg (cls (ro none) + ·) hC.symm
  have overlap : cls (lo none) = cls (ro none) := by
    apply lower_classes_match O hO power S (lo none).2 (ro none).2
    · exact sourceGraphCut_equivalent _ _ e none none (graph none none)
    · rintro ⟨x,u,_,h⟩
      have eq := degree ⟨none,u⟩
      rw [h] at eq
      exact Nat.add_right_cancel (show Z.1+1 = W.1+1 from eq).symm
  have centers : cls W + cls Zonly = cls Z + cls Wonly := by
    rw [sumW,sumZ,overlap]
    ac_rfl
  let out := ∑ i : Fin m, ∑ j : Fin n, left (some i) (some j)
  have out' : (∑ j : Fin n, ∑ i : Fin m, right (some j) (some i)) = out := by
    unfold out
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (matchCut _ _).symm
  have leftRest : P = cls Zonly * p + out := by
    rw [hP]
    calc
      (∑ i, cls (A i)) = ∑ i : Fin m, (left (some i) none + ∑ j : Fin n, left (some i) (some j)) := by
        apply Finset.sum_congr rfl
        intro i _
        change cls (U (some i)) = _
        unfold left
        simpa only [Fintype.sum_option] using sourceCutObject_sum U V e graph (some i)
      _ = (∑ i : Fin m, cls (ro (some i)) * p) + out := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i _ => (matchCut (some i) none).trans (raiseRight (some i))
      _ = _ := by rw [← Finset.sum_mul,← hC]
  have rightRest : Q = cls Wonly * p + out := by
    rw [hQ]
    calc
      (∑ j, cls (B j)) = ∑ j : Fin n, (right (some j) none + ∑ i : Fin m, right (some j) (some i)) := by
        apply Finset.sum_congr rfl
        intro j _
        change cls (V (some j)) = _
        unfold right
        simpa only [Fintype.sum_option] using sourceCutObject_sum V U e.symm back (some j)
      _ = (∑ j : Fin n, cls (lo (some j)) * p) + out := by
        rw [Finset.sum_add_distrib,out']
        congr 1
        exact Finset.sum_congr rfl fun j _ => (matchCut none (some j)).symm.trans (raiseLeft (some j))
      _ = _ := by rw [← Finset.sum_mul,← hD]
  let d := (cls W + cls Zonly) * (1+q) + out
  refine ⟨d,Or.inr ⟨Zonly,cls W*(1+q)+out,?_,?_⟩,
    Or.inr ⟨Wonly,cls Z*(1+q)+out,?_,?_⟩⟩
  · rw [hb,leftRest]
    ac_rfl
  · unfold d
    rw [add_mul]
    ac_rfl
  · rw [hc,rightRest]
    ac_rfl
  · unfold d
    rw [centers,add_mul]
    ac_rfl

theorem graded_blowup_exact_grid {a b c : RVSemiring 𝓜 S} {m n : ℕ}
    (hab : BlowupSteps step m a b) (hac : BlowupSteps step n a c) :
    ∃ d, BlowupSteps step n b d ∧ BlowupSteps step m c d :=
  blowup_exact_grid step (elementaryClassStep_diamond O hO power S hneg) hab hac

end GeneralizedEuler.Section5
