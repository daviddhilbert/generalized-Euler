module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn
public import Section2.SortedModelTheory

/-! Directed unions in the iteration of the one-generator lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2.SortedSubstructure

open FirstOrder

universe u v w z z'

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z} {Y : TCsort → Type z'}
  {M : SortedStructure L E X} {N : SortedStructure L E Y}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

private theorem exists_stage_for_args
    (S : I → SortedSubstructure M) (hS : ∀ s, Monotone fun i => (S i).carrier s)
    {ss : List TCsort} (xs : SortedArgs X ss)
    (hx : ∀ j, ∃ i, xs j ∈ (S i).carrier (ss.get j)) :
    ∃ i, ∀ j, xs j ∈ (S i).carrier (ss.get j) := by
  choose k hk using hx
  obtain ⟨i, hi⟩ := (Set.finite_range k).bddAbove
  exact ⟨i, fun j => hS _ (hi (Set.mem_range_self j)) (hk j)⟩

/-- A finite tuple in the union lies in a common stage, so the union
is a substructure. -/
@[expose]
def directedUnion (S : I → SortedSubstructure M)
    (hS : ∀ s, Monotone fun i => (S i).carrier s) : SortedSubstructure M where
  carrier s := ⋃ i, (S i).carrier s
  closed f xs hx := by
    obtain ⟨i, hi⟩ := exists_stage_for_args S hS xs (fun j => Set.mem_iUnion.mp (hx j))
    exact Set.mem_iUnion.mpr ⟨i, (S i).closed f xs hi⟩

variable (S : I → SortedSubstructure M) (hS : ∀ s, Monotone fun i => (S i).carrier s)
  (e : ∀ i, SortedEmbedding (S i).structureOn N)
  (he : ∀ {i j} (hij : i ≤ j) (s : TCsort) (x : (S i).carrier s),
    (e i).toEmbedding s x = (e j).toEmbedding s ⟨x.val, hS s hij x.property⟩)

private def unionEval (s : TCsort) (x : (directedUnion S hS).carrier s) : Y s :=
  let h := Set.mem_iUnion.mp x.property
  (e h.choose).toEmbedding s ⟨x.val, h.choose_spec⟩

include he in
private theorem unionEval_eq_at_stage (s : TCsort) (x : (directedUnion S hS).carrier s)
    (i : I) (hi : x.val ∈ (S i).carrier s) :
    unionEval S hS e s x = (e i).toEmbedding s ⟨x.val, hi⟩ := by
  let h := Set.mem_iUnion.mp x.property
  obtain ⟨j, hj, hi'⟩ := exists_ge_ge h.choose i
  exact (he hj s ⟨x.val, h.choose_spec⟩).trans (he hi' s ⟨x.val, hi⟩).symm

/-- Compatible sorted embeddings glue on a directed union. -/
def directedUnionEmbedding : SortedEmbedding (directedUnion S hS).structureOn N where
  toEmbedding s := ⟨unionEval S hS e s, by
    intro x y hxy
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp x.property
    obtain ⟨j, hy⟩ := Set.mem_iUnion.mp y.property
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    rw [unionEval_eq_at_stage S hS e he s x k (hS s hik hx),
      unionEval_eq_at_stage S hS e he s y k (hS s hjk hy)] at hxy
    exact Subtype.ext (congrArg (fun z : (S k).carrier s => z.val)
      ((e k).toEmbedding s |>.injective hxy))⟩
  map_fun := by
    intro ss s f xs
    obtain ⟨i, hi⟩ := exists_stage_for_args S hS (fun j => (xs j).val)
      (fun j => Set.mem_iUnion.mp (xs j).property)
    let xs' : SortedArgs (fun s => (S i).carrier s) ss := fun j => ⟨(xs j).val, hi j⟩
    have hargs : (fun j => unionEval S hS e (ss.get j) (xs j)) =
        fun j => (e i).toEmbedding _ (xs' j) :=
      funext fun j => unionEval_eq_at_stage S hS e he _ (xs j) i (hi j)
    change unionEval S hS e s ((directedUnion S hS).structureOn.funMap f xs) =
      N.funMap f (fun j => unionEval S hS e _ (xs j))
    rw [hargs, unionEval_eq_at_stage S hS e he s _ i ((S i).closed f _ hi)]
    exact (e i).map_fun f xs'
  map_rel := by
    intro ss r xs
    obtain ⟨i, hi⟩ := exists_stage_for_args S hS (fun j => (xs j).val)
      (fun j => Set.mem_iUnion.mp (xs j).property)
    let xs' : SortedArgs (fun s => (S i).carrier s) ss := fun j => ⟨(xs j).val, hi j⟩
    have hargs : (fun j => unionEval S hS e (ss.get j) (xs j)) =
        fun j => (e i).toEmbedding _ (xs' j) :=
      funext fun j => unionEval_eq_at_stage S hS e he _ (xs j) i (hi j)
    change N.relMap r (fun j => unionEval S hS e _ (xs j)) ↔
      (directedUnion S hS).structureOn.relMap r xs
    rw [hargs]
    exact (e i).map_rel r xs'

theorem directedUnionEmbedding_apply_at_stage (i : I) (s : TCsort) (x : (S i).carrier s) :
    (directedUnionEmbedding S hS e he).toEmbedding s
      ⟨x.val, Set.mem_iUnion.mpr ⟨i, x.property⟩⟩ = (e i).toEmbedding s x :=
  unionEval_eq_at_stage S hS e he s _ i x.property

/-- A constant RV sort at all stages stays fixed in the union. -/
theorem directedUnion_rv_eq {R : Set (X .rv)}
    (hR : ∀ i, (S i).carrier .rv = R) : (directedUnion S hS).carrier .rv = R := by
  change (⋃ i, (S i).carrier .rv) = R
  simp only [hR, Set.iUnion_const]

end GeneralizedEuler.Section2.SortedSubstructure

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z z'

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z} {Y : TCsort → Type z'}
  (M : SortedStructure L E X) (N : SortedStructure L E Y) (R : Set (X .rv))

/-- A partial embedding whose source RV sort is fixed throughout a lift. -/
structure FixedRVLift where
  source : SortedSubstructure M
  rv_eq : source.carrier .rv = R
  embedding : SortedEmbedding source.structureOn N

namespace FixedRVLift

variable {M N R}

/-- Inclusion of sources together with agreement of the embeddings. -/
def Extends (A B : FixedRVLift M N R) : Prop :=
  ∃ h : ∀ s, A.source.carrier s ⊆ B.source.carrier s,
    ∀ s (x : A.source.carrier s),
      A.embedding.toEmbedding s x = B.embedding.toEmbedding s ⟨x.val, h s x.property⟩

instance : Preorder (FixedRVLift M N R) where
  le := Extends
  le_refl A := by
    unfold Extends
    exact ⟨fun _ _ h => h, fun _ _ => rfl⟩
  le_trans _ _ _ hAB hBC := by
    obtain ⟨hAB, heAB⟩ := hAB
    obtain ⟨hBC, heBC⟩ := hBC
    exact ⟨fun s => (hAB s).trans (hBC s),
      fun s x => (heAB s x).trans (heBC s ⟨x.val, hAB s x.property⟩)⟩

theorem le_iff_extends (A B : FixedRVLift M N R) : A ≤ B ↔ Extends A B := by rfl

private theorem bddAbove_of_chain (c : Set (FixedRVLift M N R))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) : BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hc.directedOn i.val i.property j.val j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  let S (i : c) := i.val.source
  have hS (s : TCsort) : Monotone fun i => (S i).carrier s :=
    fun _ _ h => ((le_iff_extends _ _).mp h).choose s
  let e (i : c) := i.val.embedding
  have he {i j : c} (h : i ≤ j) (s : TCsort) (x : (S i).carrier s) :
      (e i).toEmbedding s x = (e j).toEmbedding s ⟨x.val, hS s h x.property⟩ :=
    ((le_iff_extends _ _).mp h).choose_spec s x
  let B : FixedRVLift M N R :=
    ⟨SortedSubstructure.directedUnion S hS,
      SortedSubstructure.directedUnion_rv_eq S hS (fun i => i.val.rv_eq),
      SortedSubstructure.directedUnionEmbedding S hS e he⟩
  refine ⟨B, fun A hA => (le_iff_extends A B).mpr ⟨?_, ?_⟩⟩
  · exact fun _ _ hx => Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩
  · exact fun s x => (SortedSubstructure.directedUnionEmbedding_apply_at_stage
      S hS e he ⟨A, hA⟩ s x).symm

private theorem exists_maximal_extension (A : FixedRVLift M N R) :
    ∃ B : FixedRVLift M N R, A ≤ B ∧ IsMax B :=
  zorn_le_nonempty_Ici₀ A (by
    intro c _ hc a ha
    exact bddAbove_of_chain c hc ⟨a, ha⟩) A le_rfl

/-- A one-field-element extension property yields a compatible extension
to all field elements without changing the named RV sort. -/
theorem exists_fullVF (A : FixedRVLift M N R)
    (hstep : ∀ B : FixedRVLift M N R, A ≤ B → ∀ x : X .vf,
      ∃ C : FixedRVLift M N R, B ≤ C ∧ x ∈ C.source.carrier .vf) :
    ∃ B : FixedRVLift M N R, A ≤ B ∧ B.source.carrier .vf = Set.univ := by
  obtain ⟨B, hAB, hmax⟩ := exists_maximal_extension A
  refine ⟨B, hAB, Set.eq_univ_of_forall ?_⟩
  intro x
  obtain ⟨C, hBC, hx⟩ := hstep B hAB x
  exact ((le_iff_extends C B).mp (hmax hBC)).choose .vf hx

/-- Iteration of the common-lift step supplies all the required field
representatives in Lemma 2.20 while keeping the RV map fixed. -/
theorem exists_cover_by_representatives (A : FixedRVLift M N R)
    (rvOf : X .vf → X .rv) (D : Set (X .rv))
    (hstep : ∀ B : FixedRVLift M N R, A ≤ B → ∀ t ∈ D,
      t ∉ rvOf '' B.source.carrier .vf →
      ∃ C : FixedRVLift M N R, B ≤ C ∧ t ∈ rvOf '' C.source.carrier .vf) :
    ∃ B : FixedRVLift M N R, A ≤ B ∧ D ⊆ rvOf '' B.source.carrier .vf := by
  obtain ⟨B, hAB, hmax⟩ := exists_maximal_extension A
  refine ⟨B, hAB, fun t ht => ?_⟩
  by_contra htB
  obtain ⟨C, hBC, x, hx, rfl⟩ := hstep B hAB t ht htB
  exact htB ⟨x, ((le_iff_extends C B).mp (hmax hBC)).choose .vf hx, rfl⟩

end FixedRVLift

end GeneralizedEuler.Section2
