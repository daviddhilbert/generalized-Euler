module

public import Section5.DefinableBijectionSchemes

/-! Given fixed-base schemes for fiber isomorphisms, choose a finite
definable partition of the base and glue their graphs. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U V : TCsort → Type}

theorem uniform_fiber_bijection_schemes [Finite (U .vf)] [Finite (U .rv)]
    [Finite (V .vf)] [Finite (V .rv)] {I : Type*}
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (D : Set (SortedAssignment X P)) (A : Set (SortedAssignment X (SumVariables P U)))
    (B : I → Set (SortedAssignment X (SumVariables P V)))
    (G : I → Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (hD : SortedDefinableOver M S.carrier D) (ha : SortedDefinableOver M S.carrier A)
    (hb : ∀ i, SortedDefinableOver M S.carrier (B i))
    (hg : ∀ i, SortedDefinableOver M S.carrier (G i))
    (cover : ∀ p ∈ D, ∃ i, FiberBijectionScheme A (B i) (G i) p) :
    ∃ (B' : Set (SortedAssignment X (SumVariables P V)))
      (G' : Set (SortedAssignment X (SumVariables (SumVariables P U) V))),
      SortedDefinableOver M S.carrier B' ∧ SortedDefinableOver M S.carrier G' ∧
      ∀ p ∈ D, FiberBijectionScheme A B' G' p ∧ ∃ i,
        (∀ v, appendAssignments p v ∈ B' ↔ appendAssignments p v ∈ B i) ∧
        (∀ u v, appendAssignments (appendAssignments p u) v ∈ G' ↔
          appendAssignments (appendAssignments p u) v ∈ G i) := by
  let good (i : I) := {p ∈ D | FiberBijectionScheme A (B i) (G i) p}
  have hdGood (i : I) : SortedDefinableOver M S.carrier (good i) :=
    hD.inter (fiberBijectionScheme_definable ha (hb i) (hg i))
  obtain ⟨F,hF⟩ := finite_definable_cover sat D hD good hdGood (fun p hp => by
    obtain ⟨i,hi⟩ := cover p hp
    exact ⟨i,hp,hi⟩)
  let J := {i : I // i ∈ F}
  obtain ⟨pieces,hdPieces,hsub,hdisj,hunion⟩ :=
    disjoint_definable_subcover (fun i : J => good i.val) (fun i => hdGood i.val)
  let target (i : J) := (B i.val) ∩ {v | (fun s => v s ∘ Sum.inl) ∈ pieces i}
  let graph (i : J) := (G i.val) ∩ {x | (fun s => x s ∘ Sum.inl ∘ Sum.inl) ∈ pieces i}
  let B' := ⋃ i : J, target i
  let G' := ⋃ i : J, graph i
  have ht (i : J) : SortedDefinableOver M S.carrier (target i) :=
    (hb i.val).inter ((hdPieces i).pullback_relabel (fun _ => Sum.inl))
  have hh (i : J) : SortedDefinableOver M S.carrier (graph i) :=
    (hg i.val).inter ((hdPieces i).pullback_relabel (fun _ => Sum.inl ∘ Sum.inl))
  refine ⟨B',G',SortedDefinableOver.iUnion ht,SortedDefinableOver.iUnion hh,?_⟩
  intro p hp
  obtain ⟨i,hi,hg⟩ := hF p hp
  have hcover : p ∈ ⋃ i : J, pieces i := by
    rw [hunion]
    exact Set.mem_iUnion.2 ⟨⟨i,hi⟩,hg⟩
  obtain ⟨j,hj⟩ := Set.mem_iUnion.1 hcover
  have uniq (k : J) (hk : p ∈ pieces k) : k = j := by
    by_contra ne
    exact Set.disjoint_left.1 (hdisj ne) hk hj
  have bEq v : appendAssignments p v ∈ B' ↔ appendAssignments p v ∈ B j.val := by
    constructor
    · intro h
      obtain ⟨k,hk,hp'⟩ := Set.mem_iUnion.1 h
      rw [uniq k hp'] at hk
      exact hk
    · intro h
      exact Set.mem_iUnion.2 ⟨j,h,hj⟩
  have gEq u v : appendAssignments (appendAssignments p u) v ∈ G' ↔
      appendAssignments (appendAssignments p u) v ∈ G j.val := by
    constructor
    · intro h
      obtain ⟨k,hk,hp'⟩ := Set.mem_iUnion.1 h
      rw [uniq k hp'] at hk
      exact hk
    · intro h
      exact Set.mem_iUnion.2 ⟨j,h,hj⟩
  refine ⟨?_,j.val,bEq,gEq⟩
  simpa only [FiberBijectionScheme,bEq,gEq] using (hsub j hj).2

end GeneralizedEuler.Section5
