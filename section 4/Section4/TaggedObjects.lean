module

public import Section4.WholeFiberRelation
public import Section4.FixedBasePartitions
public import Mathlib.Order.PiLex
import all Section2.RVDefinableEquivalence
import all Section4.FiniteScissors
import all Section4.Objects

/-! Turn each finite-to-one structure map into finitely many injective
maps, using a definable order on tuples and counting in its fibers. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  {M : SortedStructure L E Z} {S : SortedSubstructure M} {k : ℕ}

theorem many_iff_ncard {X : Type*} (D : Set X) (hd : D.Finite) (n : ℕ) :
    (∃ f : Fin n → X, Function.Injective f ∧ ∀ i, f i ∈ D) ↔ n ≤ D.ncard := by
  classical
  let := hd.fintype
  rw [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  constructor
  · rintro ⟨f,inj,h⟩
    let a : Fin n ↪ D := ⟨fun i => ⟨f i,h i⟩,fun _ _ he => inj (congrArg Subtype.val he)⟩
    simpa using Fintype.card_le_of_injective a a.injective
  · intro h
    let a := (Fin.castLEEmb h).trans (Fintype.equivFin D).symm.toEmbedding
    exact ⟨fun i => (a i).val,Subtype.val_injective.comp a.injective,fun i => (a i).property⟩

namespace RVObject
variable (U : RVObject M S k)

def fiberSet (y : Fin k → Z .rv) : Set (Fin U.arity → Z .rv) :=
  {x | ∃ a : U.carrier, a.val = x ∧ U.label a = y}

theorem finite_fiberSet (y) : (U.fiberSet y).Finite := by
  apply ((U.finiteFibers y).image Subtype.val).subset
  rintro x ⟨a,ha,he⟩; exact ⟨a,he,ha⟩

theorem fiberSet_graph :
    isRVSet M S {t : Fin k ⊕ Fin U.arity → Z .rv | t ∘ Sum.inr ∈ U.fiberSet (t ∘ Sum.inl)} := by
  let D := {t : Fin U.arity ⊕ Fin k → Z .rv | ∃ a : U.carrier, a.val = t ∘ Sum.inl ∧ U.label a = t ∘ Sum.inr}
  have hD : isRVSet M S D := U.graph
  exact isRVSet_precomp Sum.swap hD

/-- Countable saturation gives the uniform bound for this particular
definable finite-to-one map. -/
theorem uniform_fiber_bound
    (sat : ∀ D : ℕ → Set (Fin k → Z .rv), (∀ i, isRVSet M S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) : ∃ N, ∀ y, (U.fiberSet y).ncard ≤ N := by
  classical
  let D (n : ℕ) := {y | n ≤ (U.fiberSet y).ncard}
  have hd (n) : isRVSet M S (D n) := by
    convert definable_many_witnesses S (fun y x => x ∈ U.fiberSet y) U.fiberSet_graph n using 2
    ext y; exact (many_iff_ncard _ (U.finite_fiberSet y) n).symm
  by_contra! h
  obtain ⟨y,hy⟩ := sat D hd (fun _ _ h _ hz => h.trans hz) (fun i => by
    obtain ⟨y,hy⟩ := h i; exact ⟨y,hy.le⟩)
  exact Nat.not_succ_le_self _ (hy ((U.fiberSet y).ncard + 1))

variable (lt : (Fin U.arity → Z .rv) → (Fin U.arity → Z .rv) → Prop)
def predecessors (x : Fin U.arity → Z .rv) :=
  {z | lt z x ∧ ∃ y, z ∈ U.fiberSet y ∧ x ∈ U.fiberSet y}

theorem predecessors_eq (x : U.carrier) :
    U.predecessors lt x.val = {z ∈ U.fiberSet (U.label x) | lt z x.val} := by
  ext z; constructor
  · rintro ⟨hlt,y,hz,a,ea,ey⟩
    have e : a = x := Subtype.ext ea
    exact ⟨e ▸ ey ▸ hz,hlt⟩
  · rintro ⟨hz,hlt⟩; exact ⟨hlt,_,hz,x,rfl,rfl⟩

theorem finite_predecessors (x) : (U.predecessors lt x).Finite := by
  by_cases hx : x ∈ U.carrier
  · let a : U.carrier := ⟨x,hx⟩
    rw [show x = a.val from rfl,U.predecessors_eq lt a]
    exact (U.finite_fiberSet _).subset fun _ h => h.1
  · have e : U.predecessors lt x = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
      rintro z ⟨_,y,_,a,ha,_⟩; exact hx (ha ▸ a.property))
    rw [e]; exact Set.finite_empty

theorem definable_predecessors
    (hlt : isRVSet M S {t : Fin U.arity ⊕ Fin U.arity → Z .rv | lt (t ∘ Sum.inr) (t ∘ Sum.inl)}) :
    isRVSet M S {t : Fin U.arity ⊕ Fin U.arity → Z .rv | t ∘ Sum.inr ∈ U.predecessors lt (t ∘ Sum.inl)} := by
  let right : Fin k ⊕ Fin U.arity → (Fin U.arity ⊕ Fin U.arity) ⊕ Fin k :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  let left : Fin k ⊕ Fin U.arity → (Fin U.arity ⊕ Fin U.arity) ⊕ Fin k :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)
  exact isRVSet_inter hlt (isRVSet_project (isRVSet_inter (isRVSet_precomp right U.fiberSet_graph)
    (isRVSet_precomp left U.fiberSet_graph)))

abbrev tagPiece (i : ℕ) : Set (Fin U.arity → Z .rv) := {x ∈ U.carrier | (U.predecessors lt x).ncard = i}

theorem tagPiece_definable
    (hlt : isRVSet M S {t : Fin U.arity ⊕ Fin U.arity → Z .rv | lt (t ∘ Sum.inr) (t ∘ Sum.inl)})
    (i : ℕ) : isRVSet M S (U.tagPiece lt i) := by
  have bound (n) : isRVSet M S {x | n ≤ (U.predecessors lt x).ncard} := by
    convert definable_many_witnesses S (fun x z => z ∈ U.predecessors lt x)
      (U.definable_predecessors lt hlt) n using 2
    ext x; exact (many_iff_ncard _ (U.finite_predecessors lt x) n).symm
  have test := (bound i).inter (bound (i+1)).compl
  unfold isRVSet
  convert U.definable.inter test using 1
  ext x; simp only [tagPiece,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff]
  change (x .rv ∈ U.carrier ∧ (U.predecessors lt (x .rv)).ncard = i) ↔
    x .rv ∈ U.carrier ∧ i ≤ (U.predecessors lt (x .rv)).ncard ∧ ¬ i+1 ≤ (U.predecessors lt (x .rv)).ncard
  exact and_congr_right fun _ => ⟨fun e => ⟨e.ge,by rw [e]; exact Nat.not_succ_le_self _⟩,
    fun h => le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge h.2)) h.1⟩

theorem tagPiece_injective (transitive : ∀ {x y z}, lt x y → lt y z → lt x z) (irrefl : ∀ x, ¬lt x x)
    (total : ∀ x y, x ≠ y → lt x y ∨ lt y x) (i : ℕ) :
    Function.Injective (fun a : U.tagPiece lt i => U.label ⟨a.val,a.property.1⟩) := by
  intro a b eq
  have strict (x y : U.carrier) (same : U.label x = U.label y) (h : lt x.val y.val) :
      (U.predecessors lt x.val).ncard < (U.predecessors lt y.val).ncard := by
    apply Set.ncard_lt_ncard _ (U.finite_predecessors lt _)
    rw [U.predecessors_eq lt x,U.predecessors_eq lt y,same]
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨fun _ hz => ⟨hz.1,transitive hz.2 h⟩,fun sameSet => ?_⟩
    have mem : x.val ∈ {z ∈ U.fiberSet (U.label y) | lt z y.val} := ⟨⟨x,rfl,same⟩,h⟩
    exact irrefl _ (show x.val ∈ {z ∈ U.fiberSet (U.label y) | lt z x.val} from sameSet.symm ▸ mem).2
  apply Subtype.ext; by_contra ne
  rcases total _ _ ne with h | h
  · exact (a.property.2.trans b.property.2.symm).not_lt (strict ⟨_,a.property.1⟩ ⟨_,b.property.1⟩ eq h)
  · exact (b.property.2.trans a.property.2.symm).not_lt (strict ⟨_,b.property.1⟩ ⟨_,a.property.1⟩ eq.symm h)

/-- Replace an injective label by its image as an identity-labelled object
in the same degree. The defining graph already lives over the old base. -/
def labelImage (U : RVObject M S k) : RVObject M S k where
  arity := k
  carrier := Set.range U.label
  definable := definable_range_of_rvGraph U.label U.graph
  label := Subtype.val
  graph := definable_identity_label M S (definable_range_of_rvGraph U.label U.graph)
  nonzero := by rintro ⟨_,x,rfl⟩; exact U.nonzero x
  finiteFibers := fun y => (Set.finite_singleton y).preimage Subtype.val_injective.injOn

theorem labelImage_class (inj : Function.Injective U.label) :
    objectClass M S ⟨k,U⟩ = objectClass M S ⟨k,U.labelImage⟩ := by
  apply scissors_sound M S
  apply RVRelation.iso
  exact ⟨Equiv.ofInjective U.label inj,U.graph⟩

theorem tag_partition
    (sat : ∀ D : ℕ → Set (Fin k → Z .rv), (∀ i, isRVSet M S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    ∃ N : ℕ, Pairwise (fun i j : Fin N => Disjoint (U.tagPiece lt i.val) (U.tagPiece lt j.val)) ∧
      (⋃ i : Fin N, U.tagPiece lt i.val) = U.carrier := by
  obtain ⟨N,hN⟩ := U.uniform_fiber_bound sat
  let A (i : Fin (N+1)) := U.tagPiece lt i.val
  have sub (i) : A i ⊆ U.carrier := fun _ h => h.1
  have cover : ⋃ i, A i = U.carrier := by
    ext x; rw [Set.mem_iUnion]; constructor
    · rintro ⟨i,h⟩; exact sub i h
    · intro hx
      let t : U.carrier := ⟨x,hx⟩
      have small : U.predecessors lt x ⊆ U.fiberSet (U.label t) := by
        rw [show x = t.val from rfl,U.predecessors_eq lt t]; exact fun _ h => h.1
      have le := (Set.ncard_le_ncard small (U.finite_fiberSet _)).trans (hN _)
      exact ⟨⟨_,Nat.lt_succ_of_le le⟩,hx,rfl⟩
  have disj : Pairwise (fun i j => Disjoint (A i) (A j)) := fun _ _ h =>
    Set.disjoint_left.mpr fun _ a b => h (Fin.ext (a.2.symm.trans b.2))
  exact ⟨N+1,disj,cover⟩

theorem tagged_presentation (transitive : ∀ {x y z}, lt x y → lt y z → lt x z) (irrefl : ∀ x, ¬lt x x)
    (total : ∀ x y, x ≠ y → lt x y ∨ lt y x)
    (hlt : isRVSet M S {t : Fin U.arity ⊕ Fin U.arity → Z .rv | lt (t ∘ Sum.inr) (t ∘ Sum.inl)})
    (sat : ∀ D : ℕ → Set (Fin k → Z .rv), (∀ i, isRVSet M S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    ∃ (N : ℕ) (V : Fin N → RVObject M S k), (∀ i, (V i).arity = k) ∧
      (∀ i, ∃ h : (V i).arity = k, ∀ x : (V i).carrier, (V i).label x = fun j => x.val (Fin.cast h.symm j)) ∧
      objectClass M S ⟨k,U⟩ = ∑ i, objectClass M S ⟨k,V i⟩ := by
  obtain ⟨N,disj,cover⟩ := U.tag_partition lt sat
  let A (i : Fin N) := U.tagPiece lt i.val
  have sub (i) : A i ⊆ U.carrier := fun _ h => h.1
  let R (i : Fin N) := U.restrict (sub i) (U.tagPiece_definable lt hlt i.val)
  refine ⟨N,fun i => (R i).labelImage,fun _ => rfl,fun _ => ⟨rfl,fun _ => rfl⟩,?_⟩
  apply (objectClass_partition U A (fun i => U.tagPiece_definable lt hlt i.val) disj cover).trans
  exact Finset.sum_congr rfl fun i _ => (R i).labelImage_class (U.tagPiece_injective lt transitive irrefl total i.val)

end RVObject
end GeneralizedEuler.Section4
