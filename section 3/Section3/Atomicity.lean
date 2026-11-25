module

public import Section2.SortedDefinability

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder

variable {X Y I : Type*}

/-- Definition 3.10 relative to the specified family of definable sets.
The same definition applies when a disc code or a value is named. -/
structure GeneratesType (D : Set (Set X)) (A : Set X) : Prop where
  nonempty : A.Nonempty
  uniform : ∀ B ∈ D, ∀ x ∈ A, ∀ y ∈ A, x ∈ B ↔ y ∈ B

@[expose]
def AtomicOver (D : Set (Set X)) (A : Set X) : Prop := A ∈ D ∧ GeneratesType D A

theorem generatesType_iff (D : Set (Set X)) (A : Set X) :
    GeneratesType D A ↔ A.Nonempty ∧ ∀ B ∈ D, A ⊆ B ∨ Disjoint A B := by
  constructor
  · intro h
    refine ⟨h.nonempty, fun B hB => ?_⟩
    by_cases hne : (A ∩ B).Nonempty
    · obtain ⟨x, hx, hb⟩ := hne
      exact Or.inl (fun y hy => (h.uniform B hB x hx y hy).mp hb)
    · exact Or.inr (Set.disjoint_left.mpr (fun _ hx hb => hne ⟨_, hx, hb⟩))
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun B hb x hx y hy => ?_⟩
    rcases h B hb with hsub | hdis
    · exact iff_of_true (hsub hx) (hsub hy)
    · exact iff_of_false (Set.disjoint_left.mp hdis hx) (Set.disjoint_left.mp hdis hy)

/-- The largest generator containing x is the set of realizations of its complete type. -/
def typeLocus (D : Set (Set X)) (x : X) : Set X :=
  {y | ∀ B ∈ D, x ∈ B ↔ y ∈ B}

theorem typeLocus_generates (D : Set (Set X)) (x : X) : GeneratesType D (typeLocus D x) :=
  ⟨⟨x, fun _ _ => Iff.rfl⟩, fun B hb _ hy _ hz => (hy B hb).symm.trans (hz B hb)⟩

theorem AtomicOver.eq_typeLocus {D : Set (Set X)} {A : Set X} (h : AtomicOver D A)
    {x : X} (hx : x ∈ A) : A = typeLocus D x := by
  ext y
  exact ⟨fun hy B hB => h.2.uniform B hB x hx y hy, fun hy => (hy A h.1).mp hx⟩

theorem GeneratesType.image {D : Set (Set X)} {F : Set (Set Y)} {A : Set X}
    (ha : GeneratesType D A) (f : X → Y) (hf : ∀ B ∈ F, f ⁻¹' B ∈ D) :
    GeneratesType F (f '' A) := by
  refine ⟨ha.nonempty.image f, ?_⟩
  rintro B hb _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact ha.uniform _ (hf B hb) x hx y hy

/-- The canonical-code argument in 3.12. A definable point in the image
makes its preimage the entire atom. -/
theorem GeneratesType.constant_code {D : Set (Set X)} {A : Set X}
    (h : GeneratesType D A) (code : X → Y) {v : Y} (hv : v ∈ code '' A)
    (hdef : code ⁻¹' {v} ∈ D) : ∀ x ∈ A, code x = v := by
  obtain ⟨a, ha, rfl⟩ := hv
  exact fun x hx => (h.uniform _ hdef a ha x hx).mp rfl

/-- Substituting a code recovered from the point on A, as in 3.22. -/
theorem GeneratesType.of_same_traces {D F : Set (Set X)} {A : Set X}
    (h : GeneratesType D A) (ht : ∀ B ∈ F, ∃ C ∈ D, ∀ x ∈ A, x ∈ B ↔ x ∈ C) :
    GeneratesType F A := by
  refine ⟨h.nonempty, ?_⟩
  intro B hb x hx y hy
  obtain ⟨C, hc, he⟩ := ht B hb
  exact (he x hx).trans ((h.uniform C hc x hx y hy).trans (he y hy).symm)

/-- Section 3's ordinary two-sorted parameter convention as an instance
of Definition 3.10 on assignments. -/
abbrev SortedAtomicOver {L : Language} {E : Type*} {Z : TCsort → Type*}
    {M : SortedStructure L E Z} (S : SortedSubstructure M) {Var : TCsort → Type*}
    (A : Set (∀ s, Var s → Z s)) := AtomicOver (SortedDefinableOver M S.carrier) A

/-- An automorphism fixing each parameter and taking x to y preserves
every test over that base, including tests with quantifiers (3.15). -/
theorem generatesType_of_automorphisms {L : Language} {E : Type*} {Z : TCsort → Type*}
    (M : SortedStructure L E Z) (P : ∀ s, Set (Z s)) {Var : TCsort → Type*}
    {A : Set (∀ s, Var s → Z s)} (hne : A.Nonempty)
    (hm : ∀ x ∈ A, ∀ y ∈ A, ∃ e : SortedIsomorphism M M,
      (∀ s p, p ∈ P s → e.toEmbedding s p = p) ∧ (∀ s i, e.toEmbedding s (x s i) = y s i)) :
    GeneratesType (SortedDefinableOver M P) A := by
  refine ⟨hne, ?_⟩
  rintro B ⟨φ, hφ⟩ x hx y hy
  obtain ⟨e, hbase, htuple⟩ := hm x hx y hy
  have he : e.toSortedEmbedding.mapAssignment (fun s => Sum.elim Subtype.val (x s)) =
      (fun s => Sum.elim (Subtype.val (p := (· ∈ P s))) (y s)) := by
    funext s i
    rw [SortedEmbedding.mapAssignment_apply]
    cases i with
    | inl p => exact hbase s p.val p.property
    | inr j => exact htuple s j
  have h := e.realize_iff φ (fun s => Sum.elim Subtype.val (x s))
  rw [he] at h
  exact (hφ x).trans (h.symm.trans (hφ y).symm)

/-- The rectangular slicing step of 3.13. A first-coordinate slice and a
last-coordinate slice meet at their common tuple. -/
theorem constant_on_rectangle_of_constant_slices {A : Set X} {B : Set Y}
    (f : X → Y → I) (hrows : ∀ x ∈ A, ∀ y ∈ B, ∀ z ∈ B, f x y = f x z)
    (hcols : ∀ y ∈ B, ∀ x ∈ A, ∀ z ∈ A, f x y = f z y) :
    ∀ x ∈ A, ∀ y ∈ B, ∀ z ∈ A, ∀ w ∈ B, f x y = f z w :=
  fun x hx y hy z hz w hw => (hrows x hx y hy w hw).trans (hcols w hw x hx z hz)

end GeneralizedEuler.Section3
