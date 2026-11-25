module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn
public import Section2.GeneratedSubstructure

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

universe u v w z z' a

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
@[expose]
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

theorem le_of_compatible {A B : FixedRVLift M N R}
    (h : ∀ s, A.source.carrier s ⊆ B.source.carrier s)
    (he : ∀ s (x : A.source.carrier s),
      A.embedding.toEmbedding s x = B.embedding.toEmbedding s ⟨x.val, h s x.property⟩) :
    A ≤ B := ⟨h, he⟩

section DirectedUnion

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → FixedRVLift M N R) (hA : Monotone A)

include hA

omit [IsDirectedOrder I] [Nonempty I] in
private theorem liftCarrierMonotone (s : TCsort) : Monotone (fun i => (A i).source.carrier s) :=
  fun _ _ hij => ((le_iff_extends _ _).mp (hA hij)).choose s

omit [IsDirectedOrder I] [Nonempty I] in
private theorem liftEmbeddingCompatible {i j : I} (hij : i ≤ j) (s : TCsort)
    (x : (A i).source.carrier s) :
    (A i).embedding.toEmbedding s x =
      (A j).embedding.toEmbedding s ⟨x.val, liftCarrierMonotone A hA s hij x.property⟩ :=
  ((le_iff_extends _ _).mp (hA hij)).choose_spec s x

/-- Compatible partial lifts with a fixed RV sort glue along a directed
family. The field domain is the union of the field domains. -/
def directedUnion : FixedRVLift M N R :=
  ⟨SortedSubstructure.directedUnion (fun i => (A i).source) (liftCarrierMonotone A hA),
    SortedSubstructure.directedUnion_rv_eq (fun i => (A i).source) (liftCarrierMonotone A hA)
      (fun i => (A i).rv_eq),
    SortedSubstructure.directedUnionEmbedding (fun i => (A i).source) (liftCarrierMonotone A hA)
      (fun i => (A i).embedding) (liftEmbeddingCompatible A hA)⟩

theorem directedUnion_carrier (s : TCsort) :
    (directedUnion A hA).source.carrier s = ⋃ i, (A i).source.carrier s := by rfl

theorem le_directedUnion (i : I) : A i ≤ directedUnion A hA := by
  apply le_of_compatible (fun _ _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
  intro s x
  exact (SortedSubstructure.directedUnionEmbedding_apply_at_stage (fun i => (A i).source)
    (liftCarrierMonotone A hA) (fun i => (A i).embedding) (liftEmbeddingCompatible A hA) i s x).symm

end DirectedUnion

private theorem bddAbove_of_chain (c : Set (FixedRVLift M N R))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) : BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hc.directedOn i.val i.property j.val j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  let A : c → FixedRVLift M N R := Subtype.val
  have hA : Monotone A := fun _ _ h => h
  exact ⟨directedUnion A hA, fun x hx => le_directedUnion A hA ⟨x, hx⟩⟩

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

/-- With both extension properties, the same maximal lift contains every
source field point and reaches every target field point. -/
theorem exists_fullVF_and_surjectiveVF (A : FixedRVLift M N R)
    (hforth : ∀ B : FixedRVLift M N R, A ≤ B → ∀ x : X .vf,
      ∃ C : FixedRVLift M N R, B ≤ C ∧ x ∈ C.source.carrier .vf)
    (hback : ∀ B : FixedRVLift M N R, A ≤ B → ∀ y : Y .vf,
      ∃ C : FixedRVLift M N R, B ≤ C ∧ ∃ x, C.embedding.toEmbedding .vf x = y) :
    ∃ B : FixedRVLift M N R, A ≤ B ∧ B.source.carrier .vf = Set.univ ∧
      Function.Surjective (B.embedding.toEmbedding .vf) := by
  obtain ⟨B, hAB, hmax⟩ := exists_maximal_extension A
  refine ⟨B, hAB, Set.eq_univ_of_forall ?_, ?_⟩
  · intro x
    obtain ⟨C, hBC, hx⟩ := hforth B hAB x
    exact ((le_iff_extends C B).mp (hmax hBC)).choose .vf hx
  · intro y
    obtain ⟨C, hBC, x, hx⟩ := hback B hAB y
    obtain ⟨hm, he⟩ := (le_iff_extends C B).mp (hmax hBC)
    exact ⟨⟨x.val, hm .vf x.property⟩, (he .vf x).symm.trans hx⟩

/-- A full field lift that is surjective on VF and fixes RV on the
initial domain gives an automorphism fixing RV pointwise. -/
theorem exists_immediate_automorphism_of_fullVF {A : FixedRVLift M M Set.univ}
    (hidentity : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val)
    (B : FixedRVLift M M Set.univ) (hAB : A ≤ B) (hvf : B.source.carrier .vf = Set.univ)
    (hsVF : Function.Surjective (B.embedding.toEmbedding .vf)) :
    ∃ e : SortedIsomorphism M M,
      (∀ s (x : A.source.carrier s), e.toEmbedding s x.val = A.embedding.toEmbedding s x) ∧
      ∀ t : X .rv, e.toEmbedding .rv t = t := by
  obtain ⟨hmem, hagree⟩ := (le_iff_extends A B).mp hAB
  have hfull (s : TCsort) (x : X s) : x ∈ B.source.carrier s := by
    cases s with
    | vf => rw [hvf]; exact Set.mem_univ x
    | rv => rw [B.rv_eq]; exact Set.mem_univ x
  let lift (s : TCsort) (x : X s) : B.source.carrier s := ⟨x, hfull s x⟩
  have hfix (t : X .rv) : B.embedding.toEmbedding .rv (lift .rv t) = t := by
    let x : A.source.carrier .rv := ⟨t, by rw [A.rv_eq]; exact Set.mem_univ t⟩
    exact (hagree .rv x).symm.trans (hidentity x)
  let e : SortedIsomorphism M M :=
    { toEmbedding := fun s => ⟨fun x => B.embedding.toEmbedding s (lift s x),
        fun x y h => congrArg (fun b : B.source.carrier s => b.val)
          ((B.embedding.toEmbedding s).injective h)⟩
      map_fun := fun f xs => B.embedding.map_fun f (fun i => lift _ (xs i))
      map_rel := fun r xs => B.embedding.map_rel r (fun i => lift _ (xs i))
      surjective := by
        intro s y
        cases s with
        | vf =>
          obtain ⟨x, hx⟩ := hsVF y
          exact ⟨x.val, hx⟩
        | rv => exact ⟨y, hfix y⟩ }
  exact ⟨e, fun s x => (hagree s x).symm, hfix⟩

/-- The back-and-forth part of Lemma 2.20. Once the initial map is the
identity on all RV and the two field extension properties hold, it extends
to a sorted automorphism that still fixes RV pointwise. -/
theorem exists_immediate_automorphism {A : FixedRVLift M M Set.univ}
    (hidentity : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val)
    (hforth : ∀ B : FixedRVLift M M Set.univ, A ≤ B → ∀ x : X .vf,
      ∃ C : FixedRVLift M M Set.univ, B ≤ C ∧ x ∈ C.source.carrier .vf)
    (hback : ∀ B : FixedRVLift M M Set.univ, A ≤ B → ∀ y : X .vf,
      ∃ C : FixedRVLift M M Set.univ, B ≤ C ∧ ∃ x, C.embedding.toEmbedding .vf x = y) :
    ∃ e : SortedIsomorphism M M,
      (∀ s (x : A.source.carrier s), e.toEmbedding s x.val = A.embedding.toEmbedding s x) ∧
      ∀ t : X .rv, e.toEmbedding .rv t = t := by
  obtain ⟨B, hAB, hvf, hsVF⟩ := exists_fullVF_and_surjectiveVF A hforth hback
  exact exists_immediate_automorphism_of_fullVF hidentity B hAB hvf hsVF

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

/-- Adding representatives of all the named RV elements gives the
VF-generated enlargement used in Theorem 2.16. -/
theorem exists_vfGenerated_extension (A : FixedRVLift M N R)
    (hstep : ∀ B : FixedRVLift M N R, A ≤ B → ∀ t ∈ R,
      t ∉ M.rvMap '' B.source.carrier .vf →
      ∃ C : FixedRVLift M N R, B ≤ C ∧ t ∈ M.rvMap '' C.source.carrier .vf) :
    ∃ B : FixedRVLift M N R, A ≤ B ∧ B.source.structureOn.IsVFGenerated := by
  obtain ⟨B, hAB, hcover⟩ := exists_cover_by_representatives A M.rvMap R hstep
  refine ⟨B, hAB, ?_⟩
  intro t
  have hs : B.source.carrier .rv ⊆ R := le_of_eq B.rv_eq
  have ht : t.val ∈ R := hs t.property
  obtain ⟨x, hx, hrv⟩ := hcover ht
  let p : B.source.carrier .vf := ⟨x, hx⟩
  refine ⟨p, Subtype.ext ?_⟩
  have h := B.source.inclusion.map_rv p
  rw [SortedSubstructure.inclusion_apply, SortedSubstructure.inclusion_apply] at h
  exact h.trans hrv

/-- It suffices to test partial elementarity after adding field
representatives of the old RV sort. -/
theorem realize_iff_of_vfGenerated_extension (A : FixedRVLift M N R)
    (hstep : ∀ B : FixedRVLift M N R, A ≤ B → ∀ t ∈ R,
      t ∉ M.rvMap '' B.source.carrier .vf →
      ∃ C : FixedRVLift M N R, B ≤ C ∧ t ∈ M.rvMap '' C.source.carrier .vf)
    (hgen : ∀ B : FixedRVLift M N R, A ≤ B → B.source.structureOn.IsVFGenerated →
      ∀ {Var : TCsort → Type a} (ψ : SortedFormula L E Var) (x : ∀ s, Var s → B.source.carrier s),
        ψ.realize M (fun s i => (x s i).val) ↔
          ψ.realize N (fun s i => B.embedding.toEmbedding s (x s i)))
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) (x : ∀ s, Var s → A.source.carrier s) :
    φ.realize M (fun s i => (x s i).val) ↔ φ.realize N (fun s i => A.embedding.toEmbedding s (x s i)) := by
  obtain ⟨B, hAB, hB⟩ := exists_vfGenerated_extension A hstep
  obtain ⟨hm, he⟩ := (le_iff_extends A B).mp hAB
  let xs (s : TCsort) (i : Var s) : B.source.carrier s := ⟨(x s i).val, hm s (x s i).property⟩
  have ht : (fun s i => B.embedding.toEmbedding s (xs s i)) =
      fun s i => A.embedding.toEmbedding s (x s i) := funext fun s => funext fun i => (he s (x s i)).symm
  have h := hgen B hAB hB φ xs
  rw [ht] at h
  exact h

end FixedRVLift

end GeneralizedEuler.Section2
