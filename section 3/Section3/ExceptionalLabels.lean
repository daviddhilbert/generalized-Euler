module

public import Section3.Contraction
public import Section2.Dimension
public import Mathlib.Topology.Homeomorph.Lemmas

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {R : Type*} [TopologicalSpace R] {n : ℕ}

/-- In full arity the coordinate map is just a permutation. This version
of the dimension test also works for the empty exceptional locus in arity zero. -/
theorem has_full_projection_iff (A : Set (Fin n → R)) :
    HasInteriorProjection (k := n) A ↔ (interior A).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    let e := Equiv.ofBijective p ((Finite.injective_iff_bijective).mp p.injective)
    let h := (Homeomorph.piCongrLeft (Y := fun _ : Fin n => R) e).symm
    have he : coordinateProjection (X := R) p = h := by
      funext x i
      rfl
    rw [he, ← h.image_interior] at hp
    exact hp.of_image
  · intro h
    refine ⟨Function.Embedding.refl _, ?_⟩
    change (interior (id '' A)).Nonempty
    simpa using h

theorem projectionDimension_lt_of_empty_interior (hn : 0 < n) {A : Set (Fin n → R)}
    (hA : interior A = ∅) : projectionDimension A < n := by
  apply Nat.lt_of_le_of_lt _ (Nat.sub_lt hn Nat.zero_lt_one)
  apply projectionDimension_le_iff.mpr
  intro m p hm
  have he : m.val = n := by omega
  revert p
  rw [he]
  intro p hi
  have h := (has_full_projection_iff A).mp ⟨p, hi⟩
  simp [hA] at h

/-- The extra zero-coordinate hyperplanes of 3.28 form a closed locus
whose complement is open dense. Adding them preserves empty interior. -/
theorem empty_interior_with_zero_coordinates [Zero R] [T1Space R]
    (hnz : Dense ({0}ᶜ : Set R)) {A : Set (Fin n → R)} (hA : interior A = ∅) :
    interior ({x : Fin n → R | ∃ i, x i = 0} ∪ A) = ∅ := by
  let V := Set.pi (Set.univ : Set (Fin n)) (fun _ => ({0}ᶜ : Set R))
  have hd : Dense V := dense_pi _ (fun _ _ => hnz)
  have ho : IsOpen V := isOpen_set_pi finite_univ (fun _ _ => isOpen_compl_singleton)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hy, hyv⟩ := hd.inter_open_nonempty _ isOpen_interior ⟨x, hx⟩
  have hsub : interior ({x : Fin n → R | ∃ i, x i = 0} ∪ A) ∩ V ⊆ A := by
    intro z hz
    rcases interior_subset hz.1 with ⟨i, hi⟩ | ha
    · exact ((hz.2 i (mem_univ i)) hi).elim
    · exact ha
  have h := interior_maximal hsub (isOpen_interior.inter ho) ⟨hy, hyv⟩
  simp [hA] at h

/-- Contraction outside the exceptional labels of 3.28, including zero
coordinates. Boundary dimension is needed for the single selected set only. -/
theorem almost_contractible [Zero R] [T1Space R] {X Y V : Type*}
    (p : X → Fin n → R) (q : Y → V) (f : X → Y) (hn : 0 < n)
    (hnz : Dense ({0}ᶜ : Set R))
    (bad : Set (Fin n → R)) (test : (Fin n → R) → Set X)
    (hs : ∀ u ∈ bad, (∃ x ∈ test u, p x = u) ∧ (∃ x ∉ test u, p x = u))
    (hdet : ∀ x y, p x = p y → (∀ i, p x i ≠ 0) → q (f x) ≠ q (f y) → p x ∈ bad)
    (hboundary : interior (rvBoundary p {x | p x ∈ bad ∧ x ∈ test (p x)}) = ∅) :
    ∃ U : Set (Fin n → R), projectionDimension U < n ∧
      (∀ u, (∃ i, u i = 0) → u ∈ U) ∧
      Contractible (fun x : {x // p x ∉ U} => p x) q (fun x => f x) := by
  rw [boundary_of_selected_splits p bad test hs] at hboundary
  let U := {u : Fin n → R | ∃ i, u i = 0} ∪ bad
  refine ⟨U, projectionDimension_lt_of_empty_interior hn
    (empty_interior_with_zero_coordinates hnz hboundary), fun _ h => Or.inl h, ?_⟩
  intro x y h
  by_contra he
  exact x.property (Or.inr (hdet x y h (fun i hi => x.property (Or.inl ⟨i, hi⟩)) he))

/-- With no VF coordinates every function on the input tuple is constant. -/
theorem zero_arity_contractible {K R Y V : Type*} (p : (Fin 0 → K) → R) (q : Y → V)
    (f : (Fin 0 → K) → Y) : Contractible p q f :=
  fun x y _ => congrArg (q ∘ f) (Subsingleton.elim x y)

end GeneralizedEuler.Section3
