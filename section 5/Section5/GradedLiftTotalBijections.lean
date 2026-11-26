module

public import Section5.UniformGradedLiftPresentations
public import Section5.UniformGeneratedBijections

/-! The selected relative lift schemes give a disjoint partition of
the original total space, with a definable lift bijection on each part. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P U V : TCsort → Type}

@[expose] def onlyOver (D : Set (SortedAssignment X P))
    (A : Set (SortedAssignment X (SumVariables P U))) : Set (SortedAssignment X (SumVariables P U)) :=
  {a ∈ A | (fun s => a s ∘ Sum.inl) ∈ D}

theorem onlyOver_definable {D : Set (SortedAssignment X P)} {A : Set (SortedAssignment X (SumVariables P U))}
    (defD : SortedDefinableOver M S.carrier D) (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier (onlyOver D A) :=
  defA.inter (defD.pullback_relabel (fun _ => Sum.inl))

theorem onlyOver_fiber_iff {D : Set (SortedAssignment X P)} {p : SortedAssignment X P} (hp : p ∈ D)
    {A : Set (SortedAssignment X (SumVariables P U))} (u : SortedAssignment X U) :
    appendAssignments p u ∈ onlyOver D A ↔ appendAssignments p u ∈ A := by
  change (appendAssignments p u ∈ A ∧ p ∈ D) ↔ appendAssignments p u ∈ A
  exact ⟨And.left,fun h => ⟨h,hp⟩⟩

theorem total_bijection_of_scheme_over [Finite (P .vf)] [Finite (P .rv)]
    (D : Set (SortedAssignment X P)) (defD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (B : Set (SortedAssignment X (SumVariables P V)))
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defG : SortedDefinableOver M S.carrier G)
    (valid : ∀ p ∈ D, FiberBijectionScheme A B G p) :
    ∃ e : onlyOver D A ≃ onlyOver D B,
      (∀ a : onlyOver D A, (fun s => (e a).val s ∘ Sum.inl) = (fun s => a.val s ∘ Sum.inl)) ∧
      DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ onlyOver D A, (e ⟨a,h⟩).val = b) := by
  apply total_bijection_of_fiber_scheme D defD (onlyOver D A) (onlyOver D B) G defG
    (fun _ h => h.2) (fun _ h => h.2)
  intro p
  simpa only [FiberBijectionScheme,onlyOver_fiber_iff p.property] using valid p.val p.property

theorem uniform_graded_lift_total_bijections [Finite (P .vf)] [Finite (P .rv)]
    (D : Set (SortedAssignment X P)) (A : Set (SortedAssignment X (SumVariables P U)))
    (zero : S.carrier .rv) (C : Finset (RelativeGradedLiftScheme M S P U))
    (pieces : {i // i ∈ C} → Set (SortedAssignment X P))
    (defPieces : ∀ i, SortedDefinableOver M S.carrier (pieces i))
    (valid : ∀ i p, p ∈ pieces i → i.val.valid zero A p)
    (disj : Pairwise (fun i j => Disjoint (pieces i) (pieces j))) (cover : (⋃ i, pieces i) = D) :
    let I := Σ i : {i // i ∈ C}, Fin i.val.count
    let L (i : I) := onlyOver (pieces i.1) (i.1.val.source i.2)
    let R (i : I) := onlyOver (pieces i.1) (relativeRVLift (M := M) (i.1.val.object i.2).labelGraph)
    Pairwise (fun i j => Disjoint (L i) (L j)) ∧ (⋃ i, L i) = onlyOver D A ∧
    ∀ i : I, SortedDefinableOver M S.carrier (L i) ∧ SortedDefinableOver M S.carrier (R i) ∧
      ∃ e : L i ≃ R i, (∀ a : L i, (fun s => (e a).val s ∘ Sum.inl) = (fun s => a.val s ∘ Sum.inl)) ∧
        DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ L i, (e ⟨a,h⟩).val = b) := by
  intro I L R
  have split (x : SortedAssignment X (SumVariables P U)) :
      appendAssignments (fun s => x s ∘ Sum.inl) (fun s => x s ∘ Sum.inr) = x := by
    funext s j
    cases j <;> rfl
  refine ⟨?_,?_,?_⟩
  · intro i j ne
    apply Set.disjoint_left.2
    intro x hi hj
    by_cases base : i.1 = j.1
    · rcases i with ⟨i,ii⟩
      rcases j with ⟨j,jj⟩
      change i = j at base
      subst j
      have diff : ii ≠ jj := fun h => ne (h ▸ rfl)
      let p : SortedAssignment X P := fun s => x s ∘ Sum.inl
      let u : SortedAssignment X U := fun s => x s ∘ Sum.inr
      have vm := (valid i p hi.2).2.1 ii jj diff u
      rw [show appendAssignments p u = x from split x] at vm
      exact vm ⟨hi.1,hj.1⟩
    · exact Set.disjoint_left.1 (disj base) hi.2 hj.2
  · ext x
    let p : SortedAssignment X P := fun s => x s ∘ Sum.inl
    let u : SortedAssignment X U := fun s => x s ∘ Sum.inr
    have eq : appendAssignments p u = x := split x
    constructor
    · intro h
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 h
      have hp : p ∈ pieces i.1 := hi.2
      have cov := (valid i.1 p hp).1 u
      rw [eq] at cov
      exact ⟨cov.2 ⟨i.2,hi.1⟩,cover ▸ Set.mem_iUnion.2 ⟨i.1,hp⟩⟩
    · rintro ⟨hx,hp⟩
      have pIn : p ∈ ⋃ i, pieces i := cover.symm ▸ hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 pIn
      have cov := (valid i p hi).1 u
      rw [eq] at cov
      obtain ⟨j,hj⟩ := cov.1 hx
      exact Set.mem_iUnion.2 ⟨⟨i,j⟩,hj,hi⟩
  · intro i
    let W := i.1.val.object i.2
    refine ⟨onlyOver_definable (defPieces i.1) (i.1.val.sourceDefinable i.2),
      onlyOver_definable (defPieces i.1) (relativeRVLift_definable W.labelDefinable),?_⟩
    exact total_bijection_of_scheme_over (pieces i.1) (defPieces i.1) (i.1.val.source i.2)
      (relativeRVLift (M := M) W.labelGraph) W.liftGraphDefinable (fun p hp => ((valid i.1 p hp).2.2 i.2).2)

end GeneralizedEuler.Section5
