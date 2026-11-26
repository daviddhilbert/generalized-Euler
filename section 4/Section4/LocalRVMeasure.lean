module

public import Section4.PositiveObjectCover
public import Section4.CombinePartitions
import all Section4.RestrictedBijections
import all Section4.FixedBasePartitions

/-! Finite positive presentations extend an additive invariant to arbitrary
RV carriers in a fixed degree. Common refinement occurs on the original
carrier, so it also compares presentations coming from different labels. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*}
  (M : SortedStructure L F Z) (S : SortedSubstructure M) (P : Z .rv → Prop)

def GoodRVSet {I : Type} (D : Set (I → Z .rv)) := isRVSet M S D ∧ ∀ x ∈ D, ∀ i, P (x i)

structure LocalRVMeasure (k : ℕ) (T : Type*) [AddCommMonoid T] where
  weight : ∀ (D : Set (Fin k → Z .rv)), GoodRVSet M S P D → T
  cut : ∀ {I : Type} [Fintype I] D (hd : GoodRVSet M S P D) (A : I → Set (Fin k → Z .rv))
    (ha : ∀ i, GoodRVSet M S P (A i)), Pairwise (fun i j => Disjoint (A i) (A j)) → (⋃ i, A i) = D →
      weight D hd = ∑ i, weight (A i) (ha i)
  iso : ∀ D E (hd : GoodRVSet M S P D) (he : GoodRVSet M S P E), RVDefinablyEquivalent M S.carrier D E →
    weight D hd = weight E he

namespace LocalRVMeasure
variable {M S P} {k : ℕ} {T : Type*} [AddCommMonoid T] (μ : LocalRVMeasure M S P k T)
  {H : Type} [Finite H] {D : Set (H → Z .rv)}

structure Cell (M : SortedStructure L F Z) (S : SortedSubstructure M) (P : Z .rv → Prop) (k : ℕ) (H : Type) where
  carrier : Set (H → Z .rv)
  measurable : isRVSet M S carrier
  model : Set (Fin k → Z .rv)
  good : GoodRVSet M S P model
  identifies : RVDefinablyEquivalent M S.carrier carrier model

def assigned (D : Set (H → Z .rv)) (t : T) : Prop :=
  ∃ (n : ℕ) (p : Fin n → Cell M S P k H), Pairwise (fun i j => Disjoint (p i).carrier (p j).carrier) ∧
    (⋃ i, (p i).carrier) = D ∧ (∑ i, μ.weight (p i).model (p i).good) = t

theorem cut_cell {I : Type} [Fintype I] (c : Cell M S P k H) (A : I → Set (H → Z .rv))
    (ha : ∀ i, isRVSet M S (A i)) (disj : Pairwise (fun i j => Disjoint (A i) (A j))) (cover : (⋃ i, A i) = c.carrier) :
    ∃ p : I → Cell M S P k H, (∀ i, (p i).carrier = A i) ∧ μ.weight c.model c.good = ∑ i, μ.weight (p i).model (p i).good := by
  obtain ⟨e,he⟩ := c.identifies.symm
  let B i := rvPreimage e (A i)
  have sub i : A i ⊆ c.carrier := by rw [← cover]; exact Set.subset_iUnion A i
  have part i := restricted_rvGraph (M := M) (S := S) e he (A i) (ha i) (sub i)
  have pos i : GoodRVSet M S P (B i) := ⟨(part i).1,by
    rintro _ ⟨x,rfl,_⟩ j; exact c.good.2 _ x.property j⟩
  obtain ⟨d,u⟩ := rvPreimage_partition e A disj cover
  exact ⟨fun i => ⟨A i,ha i,B i,pos i,(part i).2.symm⟩,fun _ => rfl,μ.cut _ c.good B pos d u⟩

theorem compare {n l} (a : Fin n → Cell M S P k H) (b : Fin l → Cell M S P k H)
    (da : Pairwise (fun i j => Disjoint (a i).carrier (a j).carrier))
    (db : Pairwise (fun i j => Disjoint (b i).carrier (b j).carrier))
    (same : (⋃ i, (a i).carrier) = ⋃ j, (b j).carrier) :
    (∑ i, μ.weight (a i).model (a i).good) = ∑ j, μ.weight (b j).model (b j).good := by
  let cells i j := (a i).carrier ∩ (b j).carrier
  have hd i j : isRVSet M S (cells i j) := (a i).measurable.inter (b j).measurable
  have row i : (⋃ j, cells i j) = (a i).carrier := by
    rw [show (⋃ j, cells i j) = (a i).carrier ∩ ⋃ j, (b j).carrier from (Set.inter_iUnion _ _).symm,← same]
    exact Set.inter_eq_left.mpr (Set.subset_iUnion (fun i => (a i).carrier) i)
  have col j : (⋃ i, cells i j) = (b j).carrier := by
    rw [show (⋃ i, cells i j) = (⋃ i, (a i).carrier) ∩ (b j).carrier from Set.iUnion_inter _ _ |>.symm,same]
    exact Set.inter_eq_right.mpr (Set.subset_iUnion (fun j => (b j).carrier) j)
  choose r rc re using fun i => μ.cut_cell (a i) (cells i) (hd i)
    (fun _ _ ne => (db ne).mono Set.inter_subset_right Set.inter_subset_right) (row i)
  choose c cc ce using fun j => μ.cut_cell (b j) (fun i => cells i j) (fun i => hd i j)
    (fun _ _ ne => (da ne).mono Set.inter_subset_left Set.inter_subset_left) (col j)
  have matchCell i j := (rc i j).trans (cc j i).symm
  have equal i j : μ.weight (r i j).model (r i j).good = μ.weight (c j i).model (c j i).good := by
    apply μ.iso
    have h := (r i j).identifies.symm
    rw [matchCell i j] at h
    exact h.trans (c j i).identifies
  simp_rw [re,ce,equal]
  exact Finset.sum_comm

theorem unique {x y : T} (hx : μ.assigned D x) (hy : μ.assigned D y) : x = y := by
  obtain ⟨_,a,da,ca,rfl⟩ := hx
  obtain ⟨_,b,db,cb,rfl⟩ := hy
  exact μ.compare a b da db (ca.trans cb.symm)

omit [Finite H] in
theorem transfer {J : Type} [Finite J] {E : Set (J → Z .rv)} (h : RVDefinablyEquivalent M S.carrier D E)
    {t : T} (ht : μ.assigned E t) : μ.assigned D t := by
  obtain ⟨f,hf⟩ := h
  obtain ⟨l,a,d,c,eq⟩ := ht
  let A i := (a i).carrier
  have sub i : A i ⊆ E := by rw [← c]; exact Set.subset_iUnion A i
  have each i := restricted_rvGraph (M := M) (S := S) f hf (A i) (a i).measurable (sub i)
  obtain ⟨disj,cov⟩ := rvPreimage_partition f A d c
  exact ⟨l,fun i => ⟨_,(each i).1,(a i).model,(a i).good,(each i).2.trans (a i).identifies⟩,disj,cov,eq⟩

omit [Finite H] in
theorem assigned_partition {I : Type} [Fintype I] (B : I → Set (H → Z .rv)) (w : I → T)
    (disj : Pairwise (fun i j => Disjoint (B i) (B j))) (cover : (⋃ i, B i) = D)
    (parts : ∀ i, μ.assigned (B i) (w i)) : μ.assigned D (∑ i, w i) := by
  rw [← cover]
  exact combine_partitions (Cell.carrier (M := M) (S := S) (P := P) (k := k) (H := H))
    (fun c => μ.weight c.model c.good) B disj w parts

theorem assigned_model (E : Set (Fin k → Z .rv)) (he : GoodRVSet M S P E) : μ.assigned E (μ.weight E he) := by
  let c : Cell M S P k (Fin k) := ⟨E,he.1,E,he,⟨Equiv.refl _,definable_identity_label M S he.1⟩⟩
  exact ⟨1,fun _ => c,fun i j ne => (ne (Subsingleton.elim i j)).elim,Set.iUnion_const _,by simp [c]⟩

omit [Finite H] in
theorem assigned_empty : μ.assigned (∅ : Set (H → Z .rv)) 0 := by
  refine ⟨0,Fin.elim0,fun i => i.elim0,by simp,by simp⟩

end LocalRVMeasure
end GeneralizedEuler.Section4
