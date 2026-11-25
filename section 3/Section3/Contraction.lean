module

public import Section2.DiscCodes
public import Mathlib.Data.Set.Finite.Basic

public section

namespace GeneralizedEuler.Section3

variable {X Y U V : Type*}

/-- Definition 3.25. Working with the image avoids including unrepresented labels. -/
def rvInterior (p : X → U) (A : Set X) : Set U :=
  {u | u ∈ p '' A ∧ ∀ x, p x = u → x ∈ A}

@[expose]
def rvBoundary (p : X → U) (A : Set X) : Set U :=
  {u | u ∈ p '' A ∧ ∃ x, p x = u ∧ x ∉ A}

theorem image_eq_interior_union_boundary (p : X → U) (A : Set X) :
    p '' A = rvInterior p A ∪ rvBoundary p A := by
  ext u
  constructor
  · intro hu
    by_cases h : ∀ x, p x = u → x ∈ A
    · exact Or.inl ⟨hu, h⟩
    · push Not at h
      exact Or.inr ⟨hu, h⟩
  · exact fun h => h.elim And.left And.left

theorem rvBoundary_eq_empty_iff (p : X → U) (A : Set X) :
    rvBoundary p A = ∅ ↔ p ⁻¹' (p '' A) = A := by
  constructor
  · intro he
    apply Set.Subset.antisymm _ (Set.subset_preimage_image _ _)
    intro x hx
    by_contra h
    have : p x ∈ rvBoundary p A := ⟨hx, x, rfl, h⟩
    simp [he] at this
  · intro he
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro u ⟨hu, x, rfl, hx⟩
    exact hx (he ▸ (show x ∈ p ⁻¹' (p '' A) from hu))

/-- The range version of Definition 3.27 handles a partial domain by taking
its subtype for X. It applies unchanged to residue and valuation. -/
def Contractible (p : X → U) (q : Y → V) (f : X → Y) : Prop :=
  ∀ x y, p x = p y → q (f x) = q (f y)

theorem contractible_iff_unique_contraction (p : X → U) (q : Y → V) (f : X → Y) :
    Contractible p q f ↔ ∃! g : Set.range p → Set.range (q ∘ f),
      ∀ x, (g ⟨p x, x, rfl⟩).val = q (f x) := by
  constructor
  · intro hf
    let g (u : Set.range p) : Set.range (q ∘ f) :=
      ⟨q (f u.property.choose), u.property.choose, rfl⟩
    have hg (x : X) : (g ⟨p x, x, rfl⟩).val = q (f x) :=
      hf _ x (Set.mem_range_self x (f := p)).choose_spec
    refine ⟨g, hg, ?_⟩
    intro k hk
    funext ⟨u, x, hx⟩
    subst u
    exact Subtype.ext ((hk x).trans (hg x).symm)
  · rintro ⟨g, hg, _⟩ x y h
    exact (hg x).symm.trans ((congrArg (fun u => (g u).val) (Subtype.ext h)).trans (hg y))

/-- A family of splitting witnesses, including the first applicable member
of a finite definable list, gives one set with exactly the bad labels as boundary. -/
theorem boundary_of_selected_splits (p : X → U) (bad : Set U) (test : U → Set X)
    (hs : ∀ u ∈ bad, (∃ x ∈ test u, p x = u) ∧ (∃ x ∉ test u, p x = u)) :
    rvBoundary p {x | p x ∈ bad ∧ x ∈ test (p x)} = bad := by
  ext u
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, _⟩
    exact hx.1
  · intro hu
    obtain ⟨⟨x, hx, hxu⟩, y, hy, hyu⟩ := hs u hu
    exact ⟨⟨x, by simpa [hxu] using And.intro hu hx, hxu⟩,
      y, hyu, by simpa [hyu, hu] using hy⟩

/-- Last-coordinate finiteness in the interior of the exceptional set in 3.31.
The same representative a works for every last-coordinate label. -/
theorem finite_interior_fiber (p : X → U) (q : Y → V) (bad : X → Set V)
    (hq : Function.Surjective q) (a : X) (hf : (bad a).Finite) :
    {v | (p a, v) ∈ rvInterior (Prod.map p q) {z | q z.2 ∈ bad z.1}}.Finite := by
  apply hf.subset
  intro v hv
  obtain ⟨y, rfl⟩ := hq v
  exact hv.2 (a, y) rfl

end GeneralizedEuler.Section3
