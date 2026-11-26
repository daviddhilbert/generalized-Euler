module

public import Section4.SignedAffineLift
public import Section4.GlueRVEquivalences
public import Section4.TaggedValueLift
import all Section4.ValuePullback
import all Section4.SignedValueGeneration

/-! Lemma 4.12. Its external input is the finite piecewise-GL description
in the ordered value space (Lemma 4.11). The lifted bijection commutes
with the original map on signed values. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false

/-- Finite affine description of the given map, entirely in the value sort. -/
structure SignedAffinePartition {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {JG : Language} [JG.Structure V] (G : Submodule F V) {k : ℕ}
    {D C : Set (Fin k → SignTypeˣ × V)} (e : D ≃ C) where
  count : ℕ
  inputSign : Fin count → Fin k → SignTypeˣ
  outputSign : Fin count → Fin k → SignTypeˣ
  domain : Fin count → Set (Fin k → V)
  definable : ∀ i, (G : Set V).Definable JG (domain i)
  matrix : Fin count → (Matrix (Fin k) (Fin k) F)ˣ
  intercept : Fin count → Fin k → G
  cover : (⋃ i, signInsert (inputSign i) '' domain i) = D
  disjoint : Pairwise fun i j => Disjoint (signInsert (inputSign i) '' domain i) (signInsert (inputSign j) '' domain j)
  action : ∀ i (a : Fin k → V) (_ : a ∈ domain i) (x : D), signInsert (inputSign i) a = x.val →
    (e x).val = signInsert (outputSign i) (affineLift (matrix i) (Subtype.val ∘ intercept i) a)

/-- The value-sort assertion supplied by the cited piecewise-affine
function theorem and matrix completion in Lemma 4.11. -/
def HasSignedAffinePartitions {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {JG JS : Language} [JG.Structure V] [JS.Structure (SignTypeˣ × V)]
    (G : Submodule F V) (A : Set (SignTypeˣ × V)) : Prop :=
  ∀ {k} (D C : Set (Fin k → SignTypeˣ × V)), A.Definable JS D → A.Definable JS C →
    ∀ e : D ≃ C, A.Definable JS {w : Fin k ⊕ Fin k → SignTypeˣ × V |
      ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      Nonempty (SignedAffinePartition (JG := JG) G e)

variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) (hO : IsOrderConvex O) {J JG JS : Language}
  [J.Structure K] [J.Structure (Residue O)] [JG.Structure O.ValueGroupˣ] [JS.Structure (SignedValueGroup O)]
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul =
    P e (positiveRVToRV0 O x.toMul))
  (G : Submodule F (Additive O.ValueGroupˣ)) (A : Set (SignedValueGroup O))
  (reps : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
local instance piecewiseLiftAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) := inferInstanceAs (JG.Structure O.ValueGroupˣ)
local instance piecewiseLiftSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) := inferInstanceAs (JS.Structure (SignedValueGroup O))
variable (interpret : SignedInterpretation (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A)
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
local notation "model" => canonicalStructure (L := J) O hO P
local notation "lab" => signedLabel O hO
local notation "sh" => sharp model lab

include hv hs reps powers interpret defSharp witness in
theorem lemma_4_12 {k} {D C : Set (Fin k → SignedValueGroup O)} (e : D ≃ C)
    (p : SignedAffinePartition (JG := JG) G e) :
    ∃ f : sh D ≃ sh C, SortedDefinableOver model S.carrier (rvGraph fun x => (f x).val) ∧
      ∀ x : sh D, lab ∘ (f x).val = (e ⟨lab ∘ x.val,by
        have hx : (∀ i, x.val i ≠ 0) ∧ lab ∘ x.val ∈ D := x.property
        exact hx.2⟩).val := by
  let U i := signInsert (p.inputSign i) '' p.domain i
  let W i := signInsert (p.outputSign i) '' (affineLift (p.matrix i) (Subtype.val ∘ p.intercept i) '' p.domain i)
  have inc (i) : U i ⊆ D := p.cover ▸ Set.subset_iUnion U i
  have image (i) (y : Fin k → SignedValueGroup O) : y ∈ W i ↔ ∃ x : D, x.val ∈ U i ∧ (e x).val = y := by
    constructor
    · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
      have h : signInsert (p.inputSign i) a ∈ U i := ⟨a,ha,rfl⟩
      exact ⟨⟨_,inc i h⟩,h,p.action i a ha _ rfl⟩
    · rintro ⟨x,⟨a,ha,hx⟩,rfl⟩
      exact ⟨_,⟨a,ha,rfl⟩,(p.action i a ha x hx).symm⟩
  have dst : (⋃ i, W i) = C := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨x,_,rfl⟩ := (image i y).mp hi
      exact (e x).property
    · intro hy
      let x := e.symm ⟨y,hy⟩
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (p.cover.ge x.property)
      exact Set.mem_iUnion.mpr ⟨i,(image i y).mpr ⟨x,hi,congrArg Subtype.val (e.apply_symm_apply _)⟩⟩
  have disj : Pairwise fun i j => Disjoint (W i) (W j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hi hj
    obtain ⟨x,hx,ex⟩ := (image i y).mp hi
    obtain ⟨z,hz,ez⟩ := (image j y).mp hj
    have eq := e.injective (Subtype.ext (ex.trans ez.symm))
    exact Set.disjoint_left.mp (p.disjoint hij) hx (eq ▸ hz)
  have unionSharp (B : Fin p.count → Set (Fin k → SignedValueGroup O)) :
      (⋃ i, sh (B i)) = sh (⋃ i, B i) := by
    ext x
    simp only [Set.mem_iUnion,sharp,Set.mem_ofPred_eq]
    exact ⟨fun ⟨i,hn,hi⟩ => ⟨hn,i,hi⟩,fun ⟨hn,i,hi⟩ => ⟨i,hn,hi⟩⟩
  have disjSharp (B : Fin p.count → Set (Fin k → SignedValueGroup O)) (h : Pairwise fun i j => Disjoint (B i) (B j)) :
      Pairwise fun i j => Disjoint (sh (B i)) (sh (B j)) :=
    fun _ _ hij => Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (h hij) hx.2 hy.2
  choose f hf lf using fun i => signed_affine_cell_lift O hO P S v hv s hs powers G A reps @interpret
    @defSharp @witness (p.inputSign i) (p.outputSign i) (p.matrix i) (p.intercept i) (p.domain i) (p.definable i)
  obtain ⟨g,hg,lg⟩ := glue_rv_equivalences (fun i => sh (U i)) (fun i => sh (W i))
    ((unionSharp U).trans (congrArg sh p.cover)) ((unionSharp W).trans (congrArg sh dst))
    (disjSharp U p.disjoint) (disjSharp W disj) f hf
  refine ⟨g,hg,?_⟩
  intro x
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (p.cover.ge x.property.2)
  let t : sh (U i) := ⟨x.val,x.property.1,hi⟩
  obtain ⟨a,ha,eq⟩ := hi
  rw [lg i t x rfl,lf]
  have same : (fun j => Additive.ofMul (lab (t.val j)).2) = a :=
    funext fun j => (congrArg Prod.snd (congrFun eq j)).symm
  rw [same]
  exact (p.action i a ha _ eq).symm

include hv hs reps powers interpret defSharp witness in
theorem value_morphism_lift
    (affine : HasSignedAffinePartitions (JG := JG) (JS := JS) G A)
    {k} (D C : Set (Fin k → SignedValueGroup O)) (hd : A.Definable JS D) (hc : A.Definable JS C)
    (e : D ≃ C) (he : A.Definable JS {w : Fin k ⊕ Fin k → SignedValueGroup O |
      ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr}) :
    RVDefinablyEquivalent model S.carrier (sh D) (sh C) := by
  obtain ⟨p⟩ := affine D C hd hc e he
  obtain ⟨f,hf,_⟩ := lemma_4_12 O hO P S v hv s hs powers G A reps @interpret @defSharp @witness e p
  exact ⟨f,hf⟩

include hv hs reps powers interpret defSharp witness in
theorem lemma_4_12_tagged (affine : HasSignedAffinePartitions (JG := JG) (JS := JS) G A)
    {k} (U W : Over (J := JS) A k) (e : (Σ i, U.piece i) ≃ (Σ j, W.piece j))
    (he : ∀ i j, A.Definable JS (sliceGraph U.piece W.piece e i j)) :
    ∃ f : (Σ i, sh (U.piece i)) ≃ (Σ j, sh (W.piece j)),
      (∀ i j, isRVSet model S (sliceGraph (fun i => sh (U.piece i)) (fun j => sh (W.piece j)) f i j)) ∧
      ∀ x, e ⟨x.1,lab ∘ x.2.val,by exact x.2.property.2⟩ =
        ⟨(f x).1,lab ∘ (f x).2.val,by exact (f x).2.property.2⟩ := by
  apply tagged_value_morphism_lift model S lab A _ U W e he
  intro n D C hd hc g hg
  obtain ⟨p⟩ := affine D C hd hc g hg
  exact lemma_4_12 O hO P S v hv s hs powers G A reps @interpret @defSharp @witness g p

end GeneralizedEuler.Section4
