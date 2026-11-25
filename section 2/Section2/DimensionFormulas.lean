module

public import Section2.UniformCharts
public import Section2.DimensionLower

/-! A fiber's dimension bound is first order. The VF dimension is
the least field arity of a definable injection. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {Param : TCsort → Type a} {n m k : ℕ} {R : Type}

private theorem interior_nonempty_iff_box {K : Type*} [LinearOrder K] [TopologicalSpace K]
    [OrderTopology K] [DenselyOrdered K] [NoMinOrder K] [NoMaxOrder K]
    (U : Set (Fin m → K)) :
    (interior U).Nonempty ↔ ∃ a b : Fin m → K, (∀ i, a i < b i) ∧
      ∀ x : Fin m → K, (∀ i, a i < x i ∧ x i < b i) → x ∈ U := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    have hU := mem_interior_iff_mem_nhds.mp hx
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, _, S, hS, hsub⟩ := hU
    choose a b hab hI using fun i => mem_nhds_iff_exists_Ioo_subset.mp (hS i)
    refine ⟨a, b, fun i => (hab i).1.trans (hab i).2, fun y hy => hsub ?_⟩
    exact fun i _ => hI i (hy i)
  · rintro ⟨a, b, hab, hsub⟩
    choose x hx₁ hx₂ using fun i => exists_between (hab i)
    let V := Set.univ.pi (fun i => Set.Ioo (a i) (b i))
    have hv : IsOpen V := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
    have hVU : V ⊆ U := fun y hy => hsub y (fun i => hy i (Set.mem_univ i))
    exact ⟨x, interior_maximal hVU hv
      (fun i _ => ⟨hx₁ i, hx₂ i⟩)⟩

private def fieldOrderArguments {Y : TCsort → Type*} (x y : Y .vf) :
    SortedArgs Y [.vf, .vf] :=
  Fin.cases x (Fin.cases y (fun i => i.elim0))

/-- The designated relation symbol is the non-strict order on VF. -/
def InterpretsVFOrder [LE (X .vf)] (M : SortedStructure L E X) (le : L.Relations 2) : Prop :=
  ∀ x y : X .vf, M.relMap (.vf le) (fieldOrderArguments x y) ↔ x ≤ y

private def vfStrictFormula {Var : TCsort → Type a} (le : L.Relations 2) (x y : Var .vf) :
    SortedFormula L E Var :=
  (.rel (.vf le) (fieldOrderArguments (.var y) (.var x)) : SortedFormula L E Var).neg

private theorem realize_vfStrictFormula [LinearOrder (X .vf)] {M : SortedStructure L E X}
    {le : L.Relations 2} (hLE : InterpretsVFOrder M le)
    {Var : TCsort → Type a} (v : ∀ s, Var s → X s) (x y : Var .vf) :
    (vfStrictFormula (E := E) le x y).realize M v ↔ v .vf x < v .vf y := by
  have hargs : (fun i => (fieldOrderArguments (Y := SortedTerm L E Var) (.var y) (.var x) i).realize M v) =
      fieldOrderArguments (v .vf y) (v .vf x) := by
    funext i
    refine Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i
  unfold vfStrictFormula
  rw [SortedFormula.realize_neg]
  change (¬M.relMap (.vf le) _) ↔ _
  exact (not_congr ((congrArg (M.relMap (.vf le)) hargs).to_iff.trans (hLE _ _))).trans not_le

private theorem realize_finiteConjunction {Var : TCsort → Type a}
    (M : SortedStructure L E X) (v : ∀ s, Var s → X s) (φ : Fin m → SortedFormula L E Var) :
    (SortedFormula.allOf (List.ofFn φ)).realize M v ↔ ∀ i, (φ i).realize M v := by
  simp only [SortedFormula.realize_allOf, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff]

private abbrev ChartBounds (Param : TCsort → Type a) (n : ℕ) (R : Type) (m : ℕ) :=
  AddSortedBlock (AddSortedBlock (NamedChartVariables Param n R) .vf m) .vf m

private abbrev ChartBoxPoint (Param : TCsort → Type a) (n : ℕ) (R : Type) (m : ℕ) :=
  AddSortedBlock (ChartBounds Param n R m) .vf m

private abbrev ChartProjectionWitness (Param : TCsort → Type a) (n : ℕ) (R : Type) (m : ℕ) :=
  AddSortedBlock (ChartBoxPoint Param n R m) .vf n

private def chartProjectionReplacement (s : TCsort) :
    NamedChartVariables Param n R s → ChartProjectionWitness Param n R m s
  | .inl c => .inl (.inl (.inl (.inl (.inl c))))
  | .inr i => match s with
    | .vf => .inr ⟨i, ⟨rfl⟩⟩
    | .rv => .inl (.inl (.inl (.inl (.inr i))))

/-- The projection of this fiber onto the listed coordinates contains
an open box. The VF inputs of the formula are bound in the projection. -/
def projectionBoxFormula (le : L.Relations 2)
    (φ : SortedFormula L E (NamedChartVariables Param n R)) (p : Fin m ↪ Fin n) :
    SortedFormula L E (NamedChartVariables Param n R) :=
  let a (i : Fin m) : ChartBounds Param n R m .vf := .inl (.inr ⟨i, ⟨rfl⟩⟩)
  let b (i : Fin m) : ChartBounds Param n R m .vf := .inr ⟨i, ⟨rfl⟩⟩
  let y (i : Fin m) : ChartBoxPoint Param n R m .vf := .inr ⟨i, ⟨rfl⟩⟩
  let inside : SortedFormula L E (ChartBoxPoint Param n R m) :=
    .allOf (List.ofFn fun i => (vfStrictFormula le (.inl (a i)) (y i)).conjunction
      (vfStrictFormula le (y i) (.inl (b i))))
  let projects : SortedFormula L E (ChartProjectionWitness Param n R m) :=
    .allOf (List.ofFn fun i =>
      .equal (.var (s := .vf) (.inr ⟨p i, ⟨rfl⟩⟩)) (.var (.inl (y i))))
  let witness := (φ.relabel chartProjectionReplacement).conjunction projects
  let box := (SortedFormula.allOf (List.ofFn fun i => vfStrictFormula le (a i) (b i))).conjunction
    ((SortedFormula.imp inside (witness.exBlock .vf n)).allBlock .vf m)
  (box.exBlock .vf m).exBlock .vf m

theorem realize_projectionBoxFormula [LinearOrder (X .vf)] [TopologicalSpace (X .vf)]
    [OrderTopology (X .vf)] [DenselyOrdered (X .vf)] [NoMinOrder (X .vf)] [NoMaxOrder (X .vf)]
    {M : SortedStructure L E X} {le : L.Relations 2} (hLE : InterpretsVFOrder M le)
    (φ : SortedFormula L E (NamedChartVariables Param n R)) (p : Fin m ↪ Fin n)
    (v : ∀ s, NamedChartVariables Param n R s → X s) :
    (projectionBoxFormula le φ p).realize M v ↔
      (interior (coordinateProjection p '' {x | φ.realize M (replaceChartField v x)})).Nonempty := by
  have replace (a b y : Fin m → X .vf) (x : Fin n → X .vf) :
      (fun s => appendSortedBlock (appendSortedBlock (appendSortedBlock (appendSortedBlock v a) b) y) x s
        ∘ chartProjectionReplacement s) = replaceChartField v x := by
    funext s i
    cases s <;> cases i <;> rfl
  rw [interior_nonempty_iff_box]
  simp only [projectionBoxFormula, SortedFormula.realize_exBlock, SortedFormula.realize_allBlock,
    SortedFormula.realize_conjunction, realize_finiteConjunction, realize_vfStrictFormula hLE,
    SortedFormula.realize, SortedTerm.realize, SortedFormula.realize_relabel, replace, appendSortedBlock,
    Set.mem_image, Set.mem_ofPred_eq]
  refine exists_congr fun a => exists_congr fun b => and_congr_right fun _ => ?_
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  exact exists_congr fun x => and_congr_right fun _ => ⟨fun h => funext h, fun h => congrFun h⟩

/-- No projection of this fiber onto more than k coordinates has interior. -/
noncomputable def fiberDimensionBoundFormula (le : L.Relations 2)
    (φ : SortedFormula L E (NamedChartVariables Param n R)) (k : ℕ) :
    SortedFormula L E (NamedChartVariables Param n R) := by
  classical
  let Code := Σ m : Fin (n + 1), Fin m.val ↪ Fin n
  letI := Fintype.ofFinite Code
  exact .allOf (((Finset.univ : Finset Code).filter (fun c => k < c.1.val)).toList.map
    (fun c => (projectionBoxFormula le φ c.2).neg))

theorem realize_fiberDimensionBoundFormula_iff (M : SortedStructure L E X) (le : L.Relations 2)
    (φ : SortedFormula L E (NamedChartVariables Param n R))
    (v : ∀ s, NamedChartVariables Param n R s → X s) :
    (fiberDimensionBoundFormula le φ k).realize M v ↔
      ∀ (m : Fin (n + 1)) (p : Fin m.val ↪ Fin n), k < m.val →
        ¬(projectionBoxFormula le φ p).realize M v := by
  classical
  simp only [fiberDimensionBoundFormula, SortedFormula.realize_allOf, List.mem_map,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, forall_exists_index,
    and_imp, Sigma.forall]
  exact ⟨fun h m p hm => (SortedFormula.realize_neg _ _ _).mp (h _ m p hm rfl),
    fun h ψ m p hm he => he ▸ (SortedFormula.realize_neg _ _ _).mpr (h m p hm)⟩

theorem realize_fiberDimensionBoundFormula [LinearOrder (X .vf)] [TopologicalSpace (X .vf)]
    [OrderTopology (X .vf)] [DenselyOrdered (X .vf)] [NoMinOrder (X .vf)] [NoMaxOrder (X .vf)]
    {M : SortedStructure L E X} {le : L.Relations 2} (hLE : InterpretsVFOrder M le)
    (φ : SortedFormula L E (NamedChartVariables Param n R))
    (v : ∀ s, NamedChartVariables Param n R s → X s) :
    (fiberDimensionBoundFormula le φ k).realize M v ↔
      projectionDimension {x | φ.realize M (replaceChartField v x)} ≤ k := by
  rw [projectionDimension_le_iff, realize_fiberDimensionBoundFormula_iff]
  simp only [realize_projectionBoxFormula hLE]

/-- Pointwise charts in every model of the named theory. The chart
coordinates are drawn from the field tuple. Its defining formula can
use the named base and the RV fiber coordinates. -/
def HasPointwiseProjectionCharts (T : SortedTheory L E) (le : L.Relations 2)
    (φ : SortedFormula L E (NamedChartVariables Param n R)) : Prop :=
∀ P : T.PointedModel (NamedChartVariables Param n R),
      P.realizes φ → ∃ (m : ℕ) (p : Fin m ↪ Fin n)
        (χ : SortedFormula L E (NamedChartVariables Param n R)),
        P.realizes χ ∧ P.realizes (projectionBoxFormula le φ p) ∧
        ∀ x : Fin n → P.carrier .vf, (∀ i, P.point .vf (.inr (p i)) = x (p i)) →
          χ.realize P.model (replaceChartField P.point x) → ∀ i, P.point .vf (.inr i) = x i

/-- The upper bound of Lemma 2.26. The cited cell theorem supplies a
chart through each point of a fiber, injective on its chosen coordinates
and projecting onto a nonempty open set. The first-order bound restricts
compactness to fibers of the appropriate dimension in every model. -/
theorem exists_definable_embedding_of_vfDimension_le
    {X : TCsort → Type (max u v w z)} [LinearOrder (X .vf)] [TopologicalSpace (X .vf)]
    [OrderTopology (X .vf)] [DenselyOrdered (X .vf)] [NoMinOrder (X .vf)] [NoMaxOrder (X .vf)]
    (T : SortedTheory L E) (M : SortedStructure L E X)
    (hM : ∀ ψ ∈ T, ψ.realize M) (hX : ∀ s, Nonempty (X s))
    (le : L.Relations 2) (hLE : InterpretsVFOrder M le)
    (A : ∀ s, Set (X s)) [Finite R] (D : Set (MixedTuple X n R))
    (φ : SortedFormula L E (NamedChartVariables (fun s => (A s : Type (max u v w z))) n R))
    (hD : ∀ x : (∀ s, MixedVariables n R s → X s),
      mixedTuple x ∈ D ↔ φ.realize M (fun s => Sum.elim Subtype.val (x s)))
    (hcharts : HasPointwiseProjectionCharts T le φ)
    (hdim : vfDimension D ≤ k) (padding : A .vf) (tag : ℕ ↪ X .rv) (htag : ∀ i, tag i ∈ A .rv) :
    ∃ f : D ↪ (Fin k → X .vf) × ((R → X .rv) × X .rv),
      SortedDefinableOver M A {a : ∀ s, ChartGraphVariables n R k s → X s |
        ∃ x : D, x.val = chartInput a ∧ f x = chartOutput a} := by
  let bound := fiberDimensionBoundFormula le φ k
  apply exists_definable_embedding_of_local_projection_charts T M hM hX A D
    (φ.conjunction bound) ?_ ?_ padding tag htag
  · intro x
    let p (s : TCsort) :
        NamedChartVariables (fun s => (A s : Type (max u v w z))) n R s → X s :=
      Sum.elim Subtype.val (x s)
    have hfiber : {z | φ.realize M (replaceChartField p z)} = sortedFiber D (x .rv) := by
      ext y
      let coords : ∀ s, MixedVariables n R s → X s
        | .vf => y
        | .rv => x .rv
      have heq : replaceChartField p y = (fun s => Sum.elim Subtype.val (coords s)) := by
        funext s i
        cases s <;> cases i <;> rfl
      exact (heq ▸ (hD coords).symm : φ.realize M (replaceChartField p y) ↔ (y, x .rv) ∈ D)
    have hb : bound.realize M p := (realize_fiberDimensionBoundFormula hLE φ p).mpr (by
      rw [hfiber]
      exact (projectionDimension_fiber_le_vfDimension D (x .rv)).trans hdim)
    rw [SortedFormula.realize_conjunction, hD x]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩
  · intro P hP
    obtain ⟨hφ, hb⟩ := (SortedFormula.realize_conjunction P.model P.point φ bound).mp hP
    obtain ⟨j, p, χ, hχ, hp, hu⟩ := hcharts P hφ
    have hj : j ≤ n := by simpa using Fintype.card_le_of_injective p p.injective
    have hjk : j ≤ k := le_of_not_gt (fun h =>
      (realize_fiberDimensionBoundFormula_iff P.model le φ P.point).mp hb
        ⟨j, Nat.lt_succ_of_le hj⟩ p h hp)
    exact ⟨⟨j, hjk, p, χ⟩, hχ, hu⟩

private def mixedTupleEquiv (X : TCsort → Type z) (n : ℕ) (R : Type) :
    (∀ s, MixedVariables n R s → X s) ≃ MixedTuple X n R where
  toFun := mixedTuple
  invFun x := fun
    | .vf => x.1
    | .rv => x.2
  left_inv _ := by funext s; cases s <;> rfl
  right_inv _ := rfl

/-- The field arities for which a mixed set admits a definable
injection into field and finitely many RV coordinates. -/
def definableMixedEmbeddingArities (M : SortedStructure L E X) (A : ∀ s, Set (X s))
    (D : Set (MixedTuple X n R)) : Set ℕ :=
  {j | ∃ (S : Type) (_ : Finite S) (f : D ↪ MixedTuple X j S),
    SortedDefinableOver M A {a : ∀ s, (MixedVariables n R s ⊕ MixedVariables j S s) → X s |
      ∃ x : D, x.val = mixedTuple (fun s => a s ∘ Sum.inl) ∧
        f x = mixedTuple (fun s => a s ∘ Sum.inr)}}

/-- Lemma 2.26. The cited pointwise charts and compactness attain the
minimum. Rank in the field pregeometry bounds every competing arity,
using the no-new-VF-points property from §3. -/
theorem isLeast_definableMixedEmbeddingArities
    {X : TCsort → Type (max u v w z)} [LinearOrder (X .vf)] [TopologicalSpace (X .vf)]
    [OrderTopology (X .vf)] [DenselyOrdered (X .vf)] [NoMinOrder (X .vf)] [NoMaxOrder (X .vf)]
    (T : SortedTheory L E) (M : SortedStructure L E X)
    (hM : ∀ ψ ∈ T, ψ.realize M) (hX : ∀ s, Nonempty (X s))
    (le : L.Relations 2) (hLE : InterpretsVFOrder M le)
    (A : ∀ s, Set (X s)) [Finite R] (D : Set (MixedTuple X n R)) (hne : D.Nonempty)
    (φ : SortedFormula L E (NamedChartVariables (fun s => (A s : Type (max u v w z))) n R))
    (hD : ∀ x : (∀ s, MixedVariables n R s → X s),
      mixedTuple x ∈ D ↔ φ.realize M (fun s => Sum.elim Subtype.val (x s)))
    (hcharts : HasPointwiseProjectionCharts T le φ)
    (padding : A .vf) (tag : ℕ ↪ X .rv) (htag : ∀ i, tag i ∈ A .rv)
    (B : Matroid (X .vf))
    (hrank : ∀ (y : R → X .rv), (sortedFiber D y).Nonempty →
      ∃ x ∈ sortedFiber D y, (B.eRk (Set.range x)).toNat = projectionDimension (sortedFiber D y))
    (hclosure : ∀ {j : ℕ} {S : Type} [Finite S]
      (p : ∀ s, MixedVariables n R s → X s) (q : ∀ s, MixedVariables j S s → X s),
      SortedDefinableOver M (fun s => A s ∪ Set.range (q s)) {p} →
        Set.range (p .vf) ⊆ B.closure (Set.range (q .vf))) :
    IsLeast (definableMixedEmbeddingArities M A D) (vfDimension D) := by
  constructor
  · obtain ⟨f, hf⟩ := exists_definable_embedding_of_vfDimension_le T M hM hX le hLE
      A D φ hD hcharts le_rfl padding tag htag
    let recode : ((R → X .rv) × X .rv) ↪ (R ⊕ Unit → X .rv) :=
      ⟨fun q => Sum.elim q.1 (fun _ => q.2), fun p q h =>
        Prod.ext (funext fun r => congrFun h (.inl r)) (congrFun h (.inr ()))⟩
    let g : D ↪ MixedTuple X (vfDimension D) (R ⊕ Unit) :=
      f.trans (Function.Embedding.prodMap (Function.Embedding.refl _) recode)
    refine ⟨R ⊕ Unit, inferInstance, g, ?_⟩
    convert hf using 1
    ext a
    change (∃ x : D, x.val = chartInput a ∧ g x = _) ↔
      ∃ x : D, x.val = chartInput a ∧ f x = chartOutput a
    apply exists_congr
    intro x
    refine and_congr_right fun _ => ?_
    have h : (Function.Embedding.prodMap (Function.Embedding.refl _) recode) (chartOutput a) =
        mixedTuple (fun s => a s ∘ Sum.inr) := by
      apply Prod.ext
      · rfl
      · funext i
        cases i <;> rfl
    rw [← h]
    exact (Function.Embedding.prodMap (Function.Embedding.refl _) recode).injective.eq_iff
  · rintro j ⟨S, hS, f, hf⟩
    let e := mixedTupleEquiv X n R
    let U := e ⁻¹' D
    let i : U ↪ D := ⟨fun x => ⟨e x.val, x.property⟩, fun x y h =>
      Subtype.ext (e.injective (congrArg Subtype.val h))⟩
    let g := i.trans (f.trans (mixedTupleEquiv X j S).symm.toEmbedding)
    have hImage : mixedTuple '' U = D := e.image_preimage D
    have hg : SortedDefinableOver M A {a : ∀ s, (MixedVariables n R s ⊕ MixedVariables j S s) → X s |
        ∃ x : U, x.val = (fun s => a s ∘ Sum.inl) ∧ g x = (fun s => a s ∘ Sum.inr)} := by
      convert hf using 1
      ext a
      constructor
      · rintro ⟨x, hx, hy⟩
        refine ⟨i x, congrArg e hx, ?_⟩
        have h := congrArg (mixedTupleEquiv X j S) hy
        change (mixedTupleEquiv X j S) ((mixedTupleEquiv X j S).symm (f (i x))) = _ at h
        rwa [Equiv.apply_symm_apply] at h
      · rintro ⟨x, hx, hy⟩
        let y : U := ⟨e.symm x.val, (e.apply_symm_apply x.val).symm ▸ x.property⟩
        have hiy : i y = x := Subtype.ext (e.apply_symm_apply x.val)
        refine ⟨y, e.injective ((e.apply_symm_apply _).trans hx), ?_⟩
        change (mixedTupleEquiv X j S).symm (f (i y)) = _
        rw [hiy, hy]
        exact (mixedTupleEquiv X j S).symm_apply_apply _
    exact hImage ▸ vfDimension_le_arity_of_definable_embedding M A U
      (hne.preimage e.surjective) g hg B (hImage.symm ▸ hrank) hclosure

end GeneralizedEuler.Section2
