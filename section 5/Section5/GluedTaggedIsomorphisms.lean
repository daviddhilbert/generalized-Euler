module

public import Section5.GluedRowPartitions
public import Section5.RelativeTaggedIsomorphisms

/-! A matrix of fiber isomorphisms gives equality of the sums of
glued graded classes. The retained RV indices are kept throughout. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h t : ℕ} {D : RelativeRVIndex M S h t}

theorem RelativeRVRow.gluedClass_eq_of_degree_and_carrier_equiv
    {k l : ℕ} (A : RelativeRVRow D k) (B : RelativeRVRow D l)
    (eq : k = l)
    (iso : RVDefinablyEquivalent M S.carrier (gluedRVTags D.labels A.tags) (gluedRVTags D.labels B.tags)) :
    A.gluedClass = B.gluedClass := by
  subst l
  exact A.gluedClass_eq_of_carrier_equiv B iso

theorem RelativeTaggedIsoScheme.gluedClass_sum_eq {I J : Type} [Fintype I] [Fintype J]
    {k : I → ℕ} {l : J → ℕ}
    (A : ∀ i, RelativeRVRow D (k i)) (B : ∀ j, RelativeRVRow D (l j))
    (W : RelativeTaggedIsoScheme (fun i => RelativeRVTags.ofRow (A i)) (fun j => RelativeRVTags.ofRow (B j)))
    (valid : ∀ p ∈ D.labels, W.valid (rvTupleAssignment p)) :
    (∑ i, (A i).gluedClass) = ∑ j, (B j).gluedClass := by
  let C (i : I) (j : J) := (A i).restrictRow (W.source i j) (W.sourceDefinable i j)
  let T (j : J) (i : I) := (B j).restrictRow (W.target j i) (W.targetDefinable j i)
  have matchRows (i : I) (j : J) : (C i j).gluedClass = (T j i).gluedClass := by
    by_cases eq : k i = l j
    · apply (C i j).gluedClass_eq_of_degree_and_carrier_equiv (T j i) eq
      have vb (p : SortedAssignment X (RVVariables (Fin h))) (hp : p .rv ∈ D.labels) :
          FiberBijectionScheme (C i j).tags (T j i).tags (W.graph i j) p := by
        have eta : rvTupleAssignment (p .rv) = p := by
          funext s u
          cases s
          · exact u.elim
          · rfl
        have test : W.valid p := eta ▸ valid (p .rv) hp
        have sSub (u : SortedAssignment X (RVVariables (Fin (A i).arity))) :
            appendAssignments p u ∈ (C i j).tags ↔ appendAssignments p u ∈ W.source i j :=
          ⟨And.right,fun hu => ⟨((test.1 i).1 u).2 ⟨j,hu⟩,hu⟩⟩
        have tSub (u : SortedAssignment X (RVVariables (Fin (B j).arity))) :
            appendAssignments p u ∈ (T j i).tags ↔ appendAssignments p u ∈ W.target j i :=
          ⟨And.right,fun hu => ⟨((test.2.1 j).1 u).2 ⟨i,hu⟩,hu⟩⟩
        let bij := test.2.2.1 i j
        exact ⟨fun u => (sSub u).trans (bij.1 u),fun u => (tSub u).trans (bij.2.1 u),bij.2.2⟩
      obtain ⟨e,he,_⟩ := gluedRVTags_equiv_of_fiber_schemes D.definable (W.graphDefinable i j) vb
      exact ⟨e,he⟩
    · have sourceEmpty p hp u := (valid p hp).2.2.2 i j eq u
      rw [(C i j).gluedClass_eq_zero_of_empty (fun p hp u h => sourceEmpty p hp u h.2),
        (T j i).gluedClass_eq_zero_of_empty]
      intro p hp u hu
      obtain ⟨x,hx⟩ := ((valid p hp).2.2.1 i j).2.1 u |>.1 hu.2
      exact sourceEmpty p hp x (((valid p hp).2.2.1 i j).1 x |>.2 ⟨u,hx⟩)
  calc
    (∑ i, (A i).gluedClass) = ∑ i, ∑ j, (C i j).gluedClass :=
      Finset.sum_congr rfl fun i _ => (A i).gluedClass_partition (W.source i) (W.sourceDefinable i)
        (fun p hp => (valid p hp).1 i)
    _ = ∑ j, ∑ i, (C i j).gluedClass := Finset.sum_comm
    _ = ∑ j, ∑ i, (T j i).gluedClass := Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun i _ => matchRows i j
    _ = ∑ j, (B j).gluedClass :=
      Finset.sum_congr rfl fun j _ => ((B j).gluedClass_partition (W.target j) (W.targetDefinable j)
        (fun p hp => (valid p hp).2.1 j)).symm

end GeneralizedEuler.Section5
