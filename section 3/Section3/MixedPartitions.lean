module

public import Section3.DiscMapPartitions
public import Section2.SortedDefinability
import all Section2.SortedSyntax

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

abbrev MixedVars (m : ℕ) : TCsort → Type
  | .vf => Unit
  | .rv => Fin m

abbrev MixedGraphVars (m n : ℕ) := AddSortedVar (AddRVBlock (MixedVars m) n) .vf

variable {X : TCsort → Type*} {L : Language} {E : Type*} {m n : ℕ}

abbrev mixedInput (v : ∀ s, MixedGraphVars m n s → X s) : X .vf × (Fin m → X .rv) :=
  (v .vf (.inl ()), fun i => v .rv (.inl (.inl i)))

abbrev mixedOutput (v : ∀ s, MixedGraphVars m n s → X s) : X .vf × (Fin n → X .rv) :=
  (v .vf (.inr ⟨rfl⟩), fun i => v .rv (.inl (.inr i)))

/-- Corollary 3.24 with fixed-base definability of its source pieces.
Both tests may depend on both auxiliary tuples. Projecting the
intersection with the graph removes every newly bound coordinate. -/
theorem definable_mixed_discToDisc_partition {I J : Type*} [Finite I] [Finite J]
    (M : SortedStructure L E X) (S : ∀ s, Set (X s)) [Field (X .vf)] (O : ValuationSubring (X .vf))
    [DenselyOrdered O.ValueGroup]
    (A : Set (X .vf × (Fin m → X .rv))) (B : Set (X .vf × (Fin n → X .rv)))
    (f : X .vf × (Fin m → X .rv) → X .vf × (Fin n → X .rv))
    (g : X .vf × (Fin n → X .rv) → X .vf × (Fin m → X .rv))
    (bij : BijOn f A B) (inv : InvOn g f A B)
    (graph : SortedDefinableOver M S {v : ∀ s, MixedGraphVars m n s → X s | mixedInput v ∈ A ∧ f (mixedInput v) = mixedOutput v})
    (leftIndex : X .vf × (Fin m → X .rv) → (Fin n → X .rv) → I)
    (rightIndex : X .vf × (Fin n → X .rv) → (Fin m → X .rv) → J)
    (dLeft : ∀ i, SortedDefinableOver M S {v : ∀ s, MixedGraphVars m n s → X s | leftIndex (mixedInput v) (mixedOutput v).2 = i})
    (dRight : ∀ j, SortedDefinableOver M S {v : ∀ s, MixedGraphVars m n s → X s | rightIndex (mixedOutput v) (mixedInput v).2 = j})
    (forward : ∀ t s i c r, r ≠ 0 → openDisc O c r ⊆
      {x | (x,t) ∈ A ∧ (f (x,t)).2 = s ∧ leftIndex (x,t) s = i} →
      IsPointOrOpen O ((fun x => (f (x,t)).1) '' openDisc O c r))
    (back : ∀ s t j c r, r ≠ 0 → openDisc O c r ⊆
      {y | (y,s) ∈ B ∧ (g (y,s)).2 = t ∧ rightIndex (y,s) t = j} →
      IsPointOrOpen O ((fun y => (g (y,s)).1) '' openDisc O c r)) :
    ∃ C : I × J → Set (X .vf × (Fin m → X .rv)), (∀ a ∈ A, ∃! i, a ∈ C i) ∧
      (∀ i, C i ⊆ A ∧ SortedDefinableOver M S {v : ∀ s, MixedVars m s → X s | (v .vf (),v .rv) ∈ C i}) ∧
      ∀ i t s, let D := {x | (x,t) ∈ C i ∧ (f (x,t)).2 = s}
        let F := fun x => (f (x,t)).1
        DiscToDiscOn O D (F '' D) F (fun y => (g (y,s)).1) := by
  let li a := leftIndex a (f a).2
  let ri b := rightIndex b (g b).2
  let C (i : I × J) := {a ∈ A | li a = i.1 ∧ ri (f a) = i.2}
  obtain ⟨one,discs⟩ := mixed_discToDisc_partition O A B f g bij inv li ri
    (fun t s i c r hr inc => forward t s i c r hr (fun x hx => by
      obtain ⟨ha,hs,hi⟩ := inc hx
      exact ⟨ha,hs,hs ▸ hi⟩))
    (fun s t j c r hr inc => back s t j c r hr (fun y hy => by
      obtain ⟨hb,ht,hj⟩ := inc hy
      exact ⟨hb,ht,ht ▸ hj⟩))
  refine ⟨C,one,fun i => ⟨fun _ ha => ha.1,?_⟩,discs⟩
  have d := ((graph.inter ((dLeft i.1).inter (dRight i.2))).project_one .vf).project_rv_block
  convert d using 1
  ext v
  let a := (v .vf (),v .rv)
  change (a ∈ A ∧ li a = i.1 ∧ ri (f a) = i.2) ↔ ∃ s y,
    (a ∈ A ∧ f a = (y,s)) ∧ leftIndex a s = i.1 ∧ rightIndex (y,s) a.2 = i.2
  constructor
  · rintro ⟨ha,hl,hr⟩
    exact ⟨(f a).2,(f a).1,⟨ha,rfl⟩,hl,by simpa only [ri,inv.1 ha] using hr⟩
  · rintro ⟨s,y,⟨ha,eqn⟩,hl,hr⟩
    refine ⟨ha,by simpa [li,eqn] using hl,?_⟩
    change rightIndex (f a) (g (f a)).2 = i.2
    rw [inv.1 ha,eqn]; exact hr

end GeneralizedEuler.Section3
