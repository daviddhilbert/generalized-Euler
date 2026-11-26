module

public import Section5.TagRestrictedContractions
public import Section5.UnaryTerminalSupports
public import Section5.GradedClassCuts
import all Section4.Objects

/-! A finite partition of the retained tags partitions each selected
zero pattern. Consequently it gives an exact class sum at the end
of every contraction run. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k a : ℕ} {I : Type} [Fintype I]

theorem RetainedFieldFamily.terminalGradedClass_tag_partition
    (B : RetainedFieldFamily M S 0 k) (idx : Fin a ≃ B.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (D : I → Set (B.tags → RV0 O)) (defD : ∀ i, isRVSet M S (D i))
    (disj : Pairwise fun i j => Disjoint (D i) (D j))
    (cover : ∀ t, (Fin.elim0,t) ∈ B.carrier → ∃ i, t ∈ D i) :
    B.terminalGradedClass idx zero hz =
      ∑ i, (B.restrictTags (D i) (defD i)).terminalGradedClass idx zero hz := by
  let R (i : I) := B.restrictTags (D i) (defD i)
  let V (s : Finset (Fin k)) := B.terminalGradedPiece idx s zero hz
  let W (s : Finset (Fin k)) (i : I) := (R i).terminalGradedPiece idx s zero hz
  have each (s : Finset (Fin k)) : objectClass M S (V s) = ∑ i, objectClass M S (W s i) := by
    have mem (i : I) (q : Fin a → RV0 O) : q ∈ (W s i).2.carrier ↔
        q ∈ (V s).2.carrier ∧ q ∘ idx.symm ∈ D i := by
      refine ((R i).terminalGradedPiece_mem idx s zero hz q).trans
        (Iff.trans ?_ (and_congr_left' (B.terminalGradedPiece_mem idx s zero hz q).symm))
      change (((Fin.elim0,q ∘ idx.symm) ∈ B.carrier ∧ q ∘ idx.symm ∈ D i) ∧
          (∀ j, q (B.terminalSelect idx j) ≠ zero.val ↔ j ∈ s)) ↔
        (((Fin.elim0,q ∘ idx.symm) ∈ B.carrier ∧
          (∀ j, q (B.terminalSelect idx j) ≠ zero.val ↔ j ∈ s)) ∧ q ∘ idx.symm ∈ D i)
      exact ⟨fun ⟨⟨a,b⟩,c⟩ => ⟨⟨a,c⟩,b⟩,fun ⟨⟨a,c⟩,b⟩ => ⟨⟨a,b⟩,c⟩⟩
    let P (i : I) := (W s i).2.carrier
    have defP (i : I) : isRVSet M S (P i) := (W s i).2.definable
    have sub (i : I) : P i ⊆ (V s).2.carrier := fun t h => ((mem i t).1 h).1
    have dj : Pairwise fun i j => Disjoint (P i) (P j) := by
      intro i j ne
      apply Set.disjoint_left.2
      intro q hi hj
      exact Set.disjoint_left.1 (disj ne) ((mem i q).1 hi).2 ((mem j q).1 hj).2
    have cv : (⋃ i, P i) = (V s).2.carrier := by
      ext q
      constructor
      · intro h
        obtain ⟨i,hi⟩ := Set.mem_iUnion.1 h
        exact sub i hi
      · intro h
        obtain ⟨i,hi⟩ := cover (q ∘ idx.symm) ((B.terminalGradedPiece_mem idx s zero hz q).1 h).1
        exact Set.mem_iUnion.2 ⟨i,(mem i q).2 ⟨h,hi⟩⟩
    refine (restrictTags_partition (V s).2 P defP sub dj cv).trans (Finset.sum_congr rfl (fun i _ => ?_))
    apply scissors_sound M S
    exact RVRelation.iso _ _ ⟨Equiv.refl _,definable_identity_label M S (defP i)⟩
  calc
    _ = ∑ s : Finset (Fin k), ∑ i, objectClass M S (W s i) :=
      Finset.sum_congr rfl (fun s _ => each s)
    _ = ∑ i, ∑ s : Finset (Fin k), objectClass M S (W s i) := Finset.sum_comm
    _ = _ := rfl

end GeneralizedEuler.Section5
