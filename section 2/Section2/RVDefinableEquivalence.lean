module

public import Section2.RVReduct

/-! Definable RV graphs, composition, inverses, and images. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X} {A : ∀ s, Set (X s)}
  {I J K : Type a}
  {D : Set (I → X .rv)} {B : Set (J → X .rv)} {C : Set (K → X .rv)}

@[expose]
def rvGraph (f : D → J → X .rv) : Set (∀ s, RVVariables (I ⊕ J) s → X s) :=
  {a | ∃ x : D, x.val = a .rv ∘ Sum.inl ∧ f x = a .rv ∘ Sum.inr}

/-- The range of an RV graph is definable over the graph's parameters. -/
theorem definable_range_of_rvGraph [Finite I] (f : D → J → X .rv)
    (hf : SortedDefinableOver M A (rvGraph f)) :
    SortedDefinableOver M A {a : ∀ s, RVVariables J s → X s | a .rv ∈ Set.range f} := by
  let rename : ∀ s, RVVariables (I ⊕ J) s → AddRVCoordinates (RVVariables J) I s
    | .vf => fun i => i.elim
    | .rv => Sum.swap
  have h := SortedDefinableOver.project_rv_coordinates (hf.pullback_relabel rename)
  convert h using 1
  ext a
  change (∃ x : D, f x = a .rv) ↔ ∃ y : I → X .rv, ∃ x : D, x.val = y ∧ f x = a .rv
  exact ⟨fun ⟨x, hx⟩ => ⟨x.val, x, rfl, hx⟩, fun ⟨_, x, _, hx⟩ => ⟨x, hx⟩⟩

/-- Reversing a definable bijection of RV sets preserves definability
over the same base. -/
theorem definable_rvGraph_inverse (e : D ≃ B)
    (he : SortedDefinableOver M A (rvGraph (fun x => (e x).val))) :
    SortedDefinableOver M A (rvGraph (fun y => (e.symm y).val)) := by
  let rename : ∀ s, RVVariables (I ⊕ J) s → RVVariables (J ⊕ I) s
    | .vf => fun i => i.elim
    | .rv => Sum.swap
  convert he.pullback_relabel rename using 1
  ext a
  change (∃ y : B, y.val = a .rv ∘ Sum.inl ∧ (e.symm y).val = a .rv ∘ Sum.inr) ↔
    ∃ x : D, x.val = a .rv ∘ Sum.inr ∧ (e x).val = a .rv ∘ Sum.inl
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨e.symm y, hxy, (congrArg Subtype.val (e.apply_symm_apply y)).trans hy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨e x, hxy, (congrArg Subtype.val (e.symm_apply_apply x)).trans hx⟩

/-- Composition of definable RV maps quantifies over the finite
intermediate tuple. -/
theorem definable_rvGraph_comp [Finite J] (f : D → B) (g : B → C)
    (hf : SortedDefinableOver M A (rvGraph (fun x => (f x).val)))
    (hg : SortedDefinableOver M A (rvGraph (fun y => (g y).val))) :
    SortedDefinableOver M A (rvGraph (fun x => (g (f x)).val)) := by
  let rename₁ : ∀ s, RVVariables (I ⊕ J) s → AddRVCoordinates (RVVariables (I ⊕ K)) J s
    | .vf => fun i => i.elim
    | .rv => Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let rename₂ : ∀ s, RVVariables (J ⊕ K) s → AddRVCoordinates (RVVariables (I ⊕ K)) J s
    | .vf => fun i => i.elim
    | .rv => Sum.elim Sum.inr (fun i => .inl (.inr i))
  have h := SortedDefinableOver.project_rv_coordinates
    ((hf.pullback_relabel rename₁).inter (hg.pullback_relabel rename₂))
  convert h using 1
  ext a
  change (∃ x : D, x.val = a .rv ∘ Sum.inl ∧ (g (f x)).val = a .rv ∘ Sum.inr) ↔
    ∃ y : J → X .rv, (∃ x : D, x.val = a .rv ∘ Sum.inl ∧ (f x).val = y) ∧
      (∃ z : B, z.val = y ∧ (g z).val = a .rv ∘ Sum.inr)
  constructor
  · rintro ⟨x, hx, hgx⟩
    exact ⟨(f x).val, ⟨x, hx, rfl⟩, ⟨f x, rfl, hgx⟩⟩
  · rintro ⟨y, ⟨x, hx, hfx⟩, ⟨z, hz, hgz⟩⟩
    have he : f x = z := Subtype.ext (hfx.trans hz.symm)
    exact ⟨x, hx, he.symm ▸ hgz⟩

/-- Definable equivalence of two RV sets over the specified parameters. -/
@[expose]
def RVDefinablyEquivalent (M : SortedStructure L E X) (A : ∀ s, Set (X s))
    (D : Set (I → X .rv)) (B : Set (J → X .rv)) : Prop :=
  ∃ e : D ≃ B, SortedDefinableOver M A (rvGraph (fun x => (e x).val))

namespace RVDefinablyEquivalent

theorem symm (h : RVDefinablyEquivalent M A D B) : RVDefinablyEquivalent M A B D := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, definable_rvGraph_inverse e he⟩

theorem trans [Finite J] (h₁ : RVDefinablyEquivalent M A D B)
    (h₂ : RVDefinablyEquivalent M A B C) : RVDefinablyEquivalent M A D C := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨f, hf⟩ := h₂
  exact ⟨e.trans f, definable_rvGraph_comp e f he hf⟩

/-- Definable equivalence is invariant under definable normalizations of
the source and target. -/
theorem iff_of_normalizations {H : Type a} {D' : Set (H → X .rv)}
    [Finite I] [Finite J] [Finite H] [Finite K]
    (hD : RVDefinablyEquivalent M A D D') (hB : RVDefinablyEquivalent M A B C) :
    RVDefinablyEquivalent M A D B ↔ RVDefinablyEquivalent M A D' C :=
  ⟨fun h => (hD.symm.trans h).trans hB, fun h => (hD.trans h).trans hB.symm⟩

end RVDefinablyEquivalent

end GeneralizedEuler.Section2
