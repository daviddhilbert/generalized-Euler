module

public import Section5.UniformRelativeMixedIsomorphisms
public import Section5.GradedLiftTotalBijections
public import Section5.PresentedFieldPartitions

/-! A fiberwise tagged mixed isomorphism over the generated bases
preserves the sum of the VF classes of the total spaces. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P U : TCsort → Type}
  {I J : Type} [Fintype I] [Fintype J] [TopologicalSpace (X .vf)]

omit [Fintype I] [Fintype J] [TopologicalSpace (X .vf)] in
theorem fiberPartitionScheme_total
    {D : Set (SortedAssignment X P)} {R : Set (SortedAssignment X (SumVariables P U))}
    {C : I → Set (SortedAssignment X (SumVariables P U))}
    (valid : ∀ p ∈ D, FiberPartitionScheme R C p) :
    (∀ i, onlyOver D (C i) ⊆ onlyOver D R) ∧
    Pairwise (fun i j => Disjoint (onlyOver D (C i)) (onlyOver D (C j))) ∧
    (⋃ i, onlyOver D (C i)) = onlyOver D R := by
  have split (a : SortedAssignment X (SumVariables P U)) :
      appendAssignments (fun s => a s ∘ Sum.inl) (fun s => a s ∘ Sum.inr) = a := by
    funext s i
    cases i <;> rfl
  have union (a : SortedAssignment X (SumVariables P U)) (hp : (fun s => a s ∘ Sum.inl) ∈ D) :
      a ∈ R ↔ ∃ i, a ∈ C i := by
    have h := (valid _ hp).1 (fun s => a s ∘ Sum.inr)
    rwa [split] at h
  have sub (i : I) : onlyOver D (C i) ⊆ onlyOver D R :=
    fun a h => ⟨(union a h.2).2 ⟨i,h.1⟩,h.2⟩
  refine ⟨sub,?_,?_⟩
  · intro i j ne
    apply Set.disjoint_left.2
    intro a ha hb
    have h := (valid _ ha.2).2 i j ne (fun s => a s ∘ Sum.inr)
    rw [split] at h
    exact h ⟨ha.1,hb.1⟩
  · ext a
    rw [Set.mem_iUnion]
    exact ⟨fun ⟨i,h⟩ => sub i h,fun h =>
      let ⟨i,hi⟩ := (union a h.2).1 h.1
      ⟨i,hi,h.2⟩⟩

theorem equal_relative_total_classes_of_scheme
    [Finite (P .vf)] [Finite (P .rv)]
    (D : Set (SortedAssignment X P)) (d : SortedDefinableOver M S.carrier D)
    {A : I → RelativeMixedCarrier M S P} {B : J → RelativeMixedCarrier M S P}
    (W : RelativeMixedIsoScheme A B) (valid : ∀ p ∈ D, W.valid p)
    (U₀ : I → VFObject M S) (V₀ : J → VFObject M S)
    (a : ∀ i, MixedDefinablyEquivalent M S (onlyOver D (A i).carrier) (U₀ i).2.carrier)
    (b : ∀ j, MixedDefinablyEquivalent M S (onlyOver D (B j).carrier) (V₀ j).2.carrier) :
    (∑ i, fieldClass M S (U₀ i)) = ∑ j, fieldClass M S (V₀ j) := by
  classical
  have left (i : I) := fiberPartitionScheme_total (fun p hp => (valid p hp).1 i)
  have right (j : J) := fiberPartitionScheme_total (fun p hp => (valid p hp).2.1 j)
  have rows (i : I) := fieldClass_eq_sum_of_presented_partition (U₀ i) (a i)
    (fun j => onlyOver D (W.source i j)) (fun j => onlyOver_definable d (W.sourceDefinable i j))
    (left i).1 (left i).2.1 (left i).2.2
  have cols (j : J) := fieldClass_eq_sum_of_presented_partition (V₀ j) (b j)
    (fun i => onlyOver D (W.target j i)) (fun i => onlyOver_definable d (W.targetDefinable j i))
    (right j).1 (right j).2.1 (right j).2.2
  choose L₀ iL cL using rows
  choose R₀ iR cR using cols
  have h (i : I) (j : J) : fieldClass M S (L₀ i j) = fieldClass M S (R₀ j i) := by
    obtain ⟨e,_,de⟩ := total_bijection_of_scheme_over D d (W.source i j) (W.target j i)
      (W.graphDefinable i j) (fun p hp => (valid p hp).2.2 i j)
    exact fieldClass_of_iso M S (A := L₀ i j) (B := R₀ j i)
      ((iL i j).symm.trans (MixedDefinablyEquivalent.trans ⟨e,de⟩ (iR j i)))
  calc
    _ = ∑ i, ∑ j, fieldClass M S (L₀ i j) := Finset.sum_congr rfl (fun i _ => cL i)
    _ = ∑ i, ∑ j, fieldClass M S (R₀ j i) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))
    _ = ∑ j, ∑ i, fieldClass M S (R₀ j i) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (cR j).symm)

theorem equal_relative_total_classes_of_fiber_iso
    [Finite (P .vf)] [Finite (P .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (D : Set (SortedAssignment X P)) (d : SortedDefinableOver M S.carrier D)
    (A : I → RelativeMixedCarrier M S P) (B : J → RelativeMixedCarrier M S P)
    (fiberIso : ∀ p ∈ D, (RelativeMixedCarrier.fibers A p).Iso (RelativeMixedCarrier.fibers B p))
    (U₀ : I → VFObject M S) (V₀ : J → VFObject M S)
    (a : ∀ i, MixedDefinablyEquivalent M S (onlyOver D (A i).carrier) (U₀ i).2.carrier)
    (b : ∀ j, MixedDefinablyEquivalent M S (onlyOver D (B j).carrier) (V₀ j).2.carrier) :
    (∑ i, fieldClass M S (U₀ i)) = ∑ j, fieldClass M S (V₀ j) := by
  obtain ⟨W,valid⟩ := uniform_relative_mixed_iso_scheme A B sat D d fiberIso
  exact equal_relative_total_classes_of_scheme D d W valid U₀ V₀ a b

end GeneralizedEuler.Section5
