module

public import Section5.DefinableCovers
public import Section5.LabelProjection

/-! The injective coordinate projection pieces in Lemma 5.12. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ}

/-- Points whose projected fibers in the given set are singletons. -/
@[expose] def projectionUnique (p : Fin k → Fin n) (B : Set (labelAssignment n X)) :
    Set (labelAssignment n X) :=
  {x ∈ B | ∀ y ∈ B, projectLabels p y = projectLabels p x → y = x}

theorem projectionUnique_injOn (p : Fin k → Fin n) (B : Set (labelAssignment n X)) :
    Set.InjOn (projectLabels p) (projectionUnique p B) := by
  intro x hx y hy he
  exact hy.2 x hx.1 he

theorem projectionUnique_definable (p : Fin k → Fin n)
    {B : Set (labelAssignment n X)} (hB : SortedDefinableOver M S.carrier B) :
    SortedDefinableOver M S.carrier (projectionUnique p B) := by
  classical
  have proj := projectLabels_definable (M := M) (S := S) p
  have same : DefinableRelation M S.carrier
      (fun a b : labelAssignment n X => projectLabels p a = projectLabels p b) :=
    (proj.comp proj.transpose).congr (by
      intro a b
      exact ⟨fun ⟨_,ha,hb⟩ => ha.trans hb.symm, fun he => ⟨_,he,rfl⟩⟩)
  have diag := DefinableRelation.diagonal (M := M) (A := S.carrier) (U := RVVariables (Fin n))
  have rel : DefinableRelation M S.carrier
      (fun a b : labelAssignment n X => projectLabels p a = projectLabels p b ∧ a ≠ b) :=
    SortedDefinableOver.inter same (SortedDefinableOver.compl diag)
  have hBad := rel.image hB
  convert hB.inter hBad.compl using 1
  ext a
  change a ∈ B ∧ (∀ y ∈ B, projectLabels p y = projectLabels p a → y = a) ↔
    a ∈ B ∧ ¬ ∃ y ∈ B, projectLabels p y = projectLabels p a ∧ y ≠ a
  simp only [not_exists,not_and,not_not]

/-- Compactness turns the pointwise defining data from exchange into a
finite partition. Each part has an injective projection on its selected
coordinates, and all definitions use the original base. -/
theorem definable_injective_projection_partition
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (RVVariables (Fin n)))
      (BaseAssignments S.carrier (RVVariables (Fin n))))
    (A : Set (labelAssignment n X)) (hA : SortedDefinableOver M S.carrier A)
    (pointwise : ∀ x ∈ A, ∃ (p : Fin k ↪ Fin n) (B : Set (labelAssignment n X)),
      SortedDefinableOver M S.carrier B ∧ x ∈ projectionUnique p B) :
    ∃ (N : ℕ) (P : Fin N → Set (labelAssignment n X)) (proj : Fin N → (Fin k ↪ Fin n)),
      (∀ j, SortedDefinableOver M S.carrier (P j)) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = A ∧
      ∀ j, Set.InjOn (projectLabels (proj j)) (P j) := by
  classical
  let I := (Fin k ↪ Fin n) × {B : Set (labelAssignment n X) // SortedDefinableOver M S.carrier B}
  let D (i : I) := A ∩ projectionUnique i.1 i.2.val
  have hD (i : I) : SortedDefinableOver M S.carrier (D i) :=
    hA.inter (projectionUnique_definable i.1 i.2.property)
  obtain ⟨C,hC⟩ := finite_definable_cover sat A hA D hD (by
    intro x hx
    obtain ⟨p,B,hB,he⟩ := pointwise x hx
    exact ⟨⟨p,⟨B,hB⟩⟩,hx,he⟩)
  have eq : (⋃ i : C, D i.val) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hx
      exact hi.1
    · intro hx
      obtain ⟨i,hi,he⟩ := hC x hx
      exact Set.mem_iUnion.2 ⟨⟨i,hi⟩,he⟩
  obtain ⟨P,hP,hSub,hDisj,hUnion⟩ := disjoint_definable_subcover (fun i : C => D i.val)
    (fun i => hD i.val)
  let e := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C,P ∘ e,fun j => (e j).val.1,
    fun j => hP (e j),fun i j hij => hDisj (e.injective.ne hij),?_,?_⟩
  · rw [← eq, ← hUnion]
    exact e.surjective.iUnion_comp P
  · intro j
    exact (projectionUnique_injOn _ _).mono ((hSub (e j)).trans Set.inter_subset_right)

end GeneralizedEuler.Section5
