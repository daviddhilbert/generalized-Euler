module

public import Section3.PiecewiseFunctions
public import Section3.Monotonicity
public import Section2.DefinableCharts
import all Section2.SortedSyntax
import all Section3.DefinablePartitions

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {L : Language} {E : Type*} {X V : TCsort → Type*} {S : ∀ s, Set (X s)} {M : SortedStructure L E X}

abbrev sortedInput (v : ∀ s, AddSortedVar V .vf s → X s) (s : TCsort) (i : V s) := v s (.inl i)
abbrev sortedFieldGraph (f : (∀ s, V s → X s) → X .vf) :=
  {v : ∀ s, AddSortedVar V .vf s → X s | v .vf (.inr ⟨rfl⟩) = f (sortedInput v)}

/-- Fixed-base definability of the partition in 3.3. Agreement is the
projection of the intersection of the two graphs. Removing the earlier
agreements in index order gives disjoint cells over the same base. -/
theorem definable_first_field_choice {m : ℕ} (f : (∀ s, V s → X s) → X .vf)
    (g : Fin m → (∀ s, V s → X s) → X .vf) (df : SortedDefinableOver M S (sortedFieldGraph f))
    (dg : ∀ i, SortedDefinableOver M S (sortedFieldGraph (g i))) (cover : ∀ x, ∃ i, f x = g i x) :
    (∀ i, SortedDefinableOver M S (firstChoicePiece f g i)) ∧ ∀ x, ∃! i, x ∈ firstChoicePiece f g i := by
  classical
  have agree (i : Fin m) : SortedDefinableOver M S {x | f x = g i x} := by
    convert (df.inter (dg i)).project_one .vf using 1
    ext x
    change f x = g i x ↔ ∃ y, y = f x ∧ y = g i x
    exact ⟨fun h => ⟨_,rfl,h⟩,fun ⟨_,a,b⟩ => a.symm.trans b⟩
  refine ⟨fun i => ?_,firstChoice_partition _ _ cover⟩
  have earlier := SortedDefinableOver.iInter (fun j : {j : Fin m // j < i} => (agree j.val).compl)
  convert (agree i).inter earlier using 1
  ext x
  simp only [firstChoicePiece,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff,Subtype.forall]

abbrev UnaryTagVars : TCsort → Type
  | .vf => Unit
  | .rv => Fin 2

/-- The graph of the RV pair used in Corollary 3.5 is definable over
the base of the partition. The tags can be taken from the positive
natural RV numerals. -/
theorem definable_constant_or_injective_tags [LinearOrder (X .vf)] {m : ℕ} (A : Set (X .vf))
    (f : X .vf → X .vf) (B : Fin m → Set (X .vf)) (cover : ∀ x ∈ A, ∃! i, x ∈ B i)
    (sub : ∀ i, B i ⊆ A) (defB : ∀ i, SortedDefinableOver M S {v : ∀ s, UnaryTagVars s → X s | v .vf () ∈ B i})
    (mono : ∀ i, MonotonePiece f (B i)) (tags : Fin m ↪ X .rv × X .rv)
    (names : ∀ i, (tags i).1 ∈ S .rv ∧ (tags i).2 ∈ S .rv) :
    ∃ π : A → X .rv × X .rv,
      SortedDefinableOver M S {v : ∀ s, UnaryTagVars s → X s |
        ∃ a : A, a.val = v .vf () ∧ π a = (v .rv 0,v .rv 1)} ∧
      ∀ t, let fiber := {x : X .vf | ∃ h : x ∈ A, π ⟨x,h⟩ = t}
        (∀ x ∈ fiber, ∀ y ∈ fiber, f x = f y) ∨ InjOn f fiber := by
  classical
  let part (a : A) := (cover a.val a.property).choose
  have iffMem (i) (x : X .vf) : x ∈ B i ↔ ∃ h : x ∈ A, part ⟨x,h⟩ = i := by
    constructor
    · intro hx
      have ha := sub i hx
      exact ⟨ha,((cover x ha).choose_spec.2 i hx).symm⟩
    · rintro ⟨ha,rfl⟩; exact (cover x ha).choose_spec.1
  refine ⟨fun a => tags (part a),?_,fun t => constant_or_injective_tag_fibers tags f A part (fun i => ?_) t⟩
  · let cell (i : Fin m) := {v : ∀ s, UnaryTagVars s → X s |
      v .vf () ∈ B i ∧ v .rv 0 = (tags i).1 ∧ v .rv 1 = (tags i).2}
    have defCell (i) : SortedDefinableOver M S (cell i) := (defB i).inter
      ((SortedDefinableOver.coordinate_eq_parameter (M := M) (Var := UnaryTagVars) .rv (0 : Fin 2) ⟨_,(names i).1⟩).inter
       (SortedDefinableOver.coordinate_eq_parameter (M := M) (Var := UnaryTagVars) .rv (1 : Fin 2) ⟨_,(names i).2⟩))
    convert SortedDefinableOver.iUnion defCell using 1
    ext v
    rw [mem_iUnion]
    constructor
    · rintro ⟨a,ha,hπ⟩
      exact ⟨part a,ha ▸ (cover a.val a.property).choose_spec.1,(congrArg Prod.fst hπ).symm,(congrArg Prod.snd hπ).symm⟩
    · rintro ⟨i,h,h0,h1⟩
      obtain ⟨ha,hp⟩ := (iffMem i _).mp h
      exact ⟨⟨_,ha⟩,rfl,by change tags (part _) = _; rw [hp]; exact Prod.ext h0.symm h1.symm⟩
  · convert mono i using 1; ext x; exact (iffMem i x).symm

/-- The several-output form of 3.7 on an arbitrary partial domain,
including the empty tuple of field coordinates. -/
theorem finite_tuple_image_of_coordinate_images {K U : Type*} {n : ℕ} (A : Set U) (f : U → Fin n → K)
    (coord : ∀ i, ((fun u => f u i) '' A).Finite) : (f '' A).Finite :=
  (Set.Finite.pi coord).subset (by rintro _ ⟨x,hx,rfl⟩ i _; exact ⟨x,hx,rfl⟩)

end GeneralizedEuler.Section3
