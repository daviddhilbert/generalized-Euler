module

public import Section5.DefinableProjection

/-! Composition and transport of two-sorted graphs over one fixed base. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {A : ∀ s, Set (X s)} {U V W : TCsort → Type}

/-- Both tuples are free variables. The base occurs only in the
definability predicate. -/
@[expose] def DefinableRelation
    (M : SortedStructure L E X) (A : ∀ s, Set (X s))
    (R : SortedAssignment X U → SortedAssignment X V → Prop) : Prop :=
  SortedDefinableOver M A
    {a : SortedAssignment X (SumVariables U V) |
      R (fun s => a s ∘ Sum.inl) (fun s => a s ∘ Sum.inr)}

namespace DefinableRelation

theorem congr {R S : SortedAssignment X U → SortedAssignment X V → Prop}
    (hR : DefinableRelation M A R) (h : ∀ x y, R x y ↔ S x y) :
    DefinableRelation M A S := by
  unfold DefinableRelation at hR ⊢
  exact (Set.ext fun _ => h _ _) ▸ hR

theorem diagonal [Finite (U .vf)] [Finite (U .rv)] :
    DefinableRelation M A (fun x y : SortedAssignment X U => x = y) := by
  let V := SumVariables U U
  have hVF := SortedDefinableOver.iInter (fun i : U .vf =>
    SortedDefinableOver.coordinate_eq (M := M) (A := A) (Var := V) .vf (.inl i) (.inr i))
  have hRV := SortedDefinableOver.iInter (fun i : U .rv =>
    SortedDefinableOver.coordinate_eq (M := M) (A := A) (Var := V) .rv (.inl i) (.inr i))
  unfold DefinableRelation
  convert hVF.inter hRV using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    exact ⟨fun i => congrFun (congrFun h .vf) i, fun i => congrFun (congrFun h .rv) i⟩
  · rintro ⟨hv,hr⟩
    funext s i
    cases s
    · exact hv i
    · exact hr i

theorem transpose {R : SortedAssignment X U → SortedAssignment X V → Prop}
    (hR : DefinableRelation M A R) :
    DefinableRelation M A (fun y x => R x y) := by
  unfold DefinableRelation at hR ⊢
  exact hR.pullback_relabel (fun _ => Sum.swap)

theorem comp [Finite (V .vf)] [Finite (V .rv)]
    {R : SortedAssignment X U → SortedAssignment X V → Prop}
    {S : SortedAssignment X V → SortedAssignment X W → Prop}
    (hR : DefinableRelation M A R) (hS : DefinableRelation M A S) :
    DefinableRelation M A (fun x z => ∃ y, R x y ∧ S y z) := by
  let left (s : TCsort) : SumVariables U V s → SumVariables (SumVariables U W) V s :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let right (s : TCsort) : SumVariables V W s → SumVariables (SumVariables U W) V s :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  unfold DefinableRelation at hR hS ⊢
  have hh := (hR.pullback_relabel left).inter (hS.pullback_relabel right)
  exact definable_project_mixed hh

/-- Transport a family of tests by a definable graph. This also tracks
the image of a partial graph when the transformation is only defined
on the earlier preparation's image. -/
theorem transport [Finite (U .vf)] [Finite (U .rv)]
    {R : SortedAssignment X U → SortedAssignment X V → Prop}
    {G : SortedAssignment X U → SortedAssignment X W → Prop}
    (hR : DefinableRelation M A R) (hG : DefinableRelation M A G) :
    DefinableRelation M A (fun y t => ∃ x, R x y ∧ G x t) :=
  hR.transpose.comp hG

theorem image [Finite (U .vf)] [Finite (U .rv)]
    {R : SortedAssignment X U → SortedAssignment X V → Prop}
    {D : Set (SortedAssignment X U)}
    (hR : DefinableRelation M A R) (hD : SortedDefinableOver M A D) :
    SortedDefinableOver M A {y | ∃ x ∈ D, R x y} := by
  unfold DefinableRelation at hR
  have hleft := hR.pullback_relabel (fun s => (Sum.swap : SumVariables U V s → SumVariables V U s))
  have hright := hD.pullback_relabel (fun s => (Sum.inr : U s → SumVariables V U s))
  exact definable_project_mixed (hright.inter hleft)

end DefinableRelation

end GeneralizedEuler.Section5
