module

public import Section4.ValueScissors
public import Section4.DegreeZeroInclusion
import all Section4.DegreeZeroInclusion
import all Section4.Factors
import all Section4.ValueScissors

/-! Every tagged value generator is the sum of its single-piece classes. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject
variable {V : Type*} {J : Language} [J.Structure V] {A : Set V} {k : ℕ}
  (U : Over (J := J) A k)
open scoped Classical

private def mask (s : Set (Fin U.tags)) : Over (J := J) A k :=
  ⟨U.tags,fun i => {x | i ∈ s ∧ x ∈ U.piece i},fun i => by
    by_cases h : i ∈ s
    · simpa [h] using U.isDefinable i
    · simp [h,Set.definable_empty]⟩

private theorem tagDiagonal (D : Set (Fin k → V)) (hd : A.Definable J D) :
    A.Definable J {w : Fin k ⊕ Fin k → V | w ∘ Sum.inl ∈ D ∧ w ∘ Sum.inl = w ∘ Sum.inr} := by
  exact graph_of_map (J := J) (A := A) id (fun _ => Set.DefinableFun.proj J) D hd

/-- A tag-preserving map whose tuple map is the identity has a definable
graph on a pair of tags whenever its destination tag depends only on the source tag. -/
theorem identity_tag_slice {n m} (D : Fin n → Set (Fin k → V)) (E : Fin m → Set (Fin k → V))
    (hd : ∀ i, A.Definable J (D i)) (i : Fin n) (j : Fin m) (p : Prop)
    (R : (D i) → (E j) → Prop)
    (rule : ∀ x y, R x y ↔ p ∧ x.val = y.val) (sub : p → D i ⊆ E j) :
    A.Definable J {w : Fin k ⊕ Fin k → V | ∃ x : D i, x.val = w ∘ Sum.inl ∧ ∃ y : E j, y.val = w ∘ Sum.inr ∧ R x y} := by
  by_cases h : p
  · convert tagDiagonal (D i) (hd i) using 1
    ext w
    exact ⟨fun ⟨x,hx,y,hy,eq⟩ => ⟨hx ▸ x.property,hx.symm.trans (((rule x y).mp eq).2.trans hy)⟩,
      fun z => ⟨⟨_,z.1⟩,rfl,⟨_,sub h z.1⟩,z.2,(rule _ _).mpr ⟨h,rfl⟩⟩⟩
  · convert Set.definable_empty (A := A) (L := J) using 1
    ext w
    exact ⟨fun ⟨x,_,y,_,r⟩ => (h ((rule x y).mp r).1).elim,False.elim⟩

private def splitMask (s t : Set (Fin U.tags)) (disj : Disjoint s t) :
    (mask U (s∪t)).points A ≃ (mask U s).points A ⊕ (mask U t).points A where
  toFun x := if h : x.1 ∈ s then .inl ⟨x.1,x.2.val,h,x.2.property.2⟩
    else .inr ⟨x.1,x.2.val,x.2.property.1.resolve_left h,x.2.property.2⟩
  invFun
    | .inl x => ⟨x.1,x.2.val,Or.inl x.2.property.1,x.2.property.2⟩
    | .inr x => ⟨x.1,x.2.val,Or.inr x.2.property.1,x.2.property.2⟩
  left_inv x := by
    dsimp only
    split_ifs <;> rfl
  right_inv x := by
    cases x with
    | inl a =>
      dsimp only
      split_ifs with h
      · rfl
      · exact (h a.2.property.1).elim
    | inr b =>
      dsimp only
      split_ifs with h
      · exact (Set.disjoint_left.mp disj h b.2.property.1).elim
      · rfl

private theorem splitMask_class (s t : Set (Fin U.tags)) (disj : Disjoint s t) :
    taggedValueClass A (mask U (s∪t)) = taggedValueClass A (mask U s) + taggedValueClass A (mask U t) := by
  let f := splitMask U s t disj
  apply relation_sound (Relation.cut _ _ _ ⟨f,?_,?_⟩)
  · intro i j
    apply identity_tag_slice _ _ (mask U (s∪t)).isDefinable i j (i=j ∧ i∈s)
    · intro x y; by_cases h : i ∈ s
      · by_cases e : i=j
        · subst j; simp [f,splitMask,h]; constructor
          · intro eq; cases eq; rfl
          · intro eq; cases y; cases eq; rfl
        · simp [f,splitMask,h,e]; intro eq; cases eq; exact e rfl
      · simp [f,splitMask,h]
    · rintro ⟨rfl,h⟩ x hx; exact ⟨h,hx.2⟩
  · intro i j
    apply identity_tag_slice _ _ (mask U (s∪t)).isDefinable i j (i=j ∧ i∉s)
    · intro x y; by_cases h : i ∈ s
      · simp [f,splitMask,h]
      · by_cases e : i=j
        · subst j; simp [f,splitMask,h]; constructor
          · intro eq; cases eq; rfl
          · intro eq; cases y; cases eq; rfl
        · simp [f,splitMask,h,e]; intro eq; cases eq; exact e rfl
    · rintro ⟨rfl,h⟩ x hx; exact ⟨hx.1.resolve_left h,hx.2⟩

private theorem tagged_ext {I X : Type*} {p : I → Set X} {a b : Σ i, p i}
    (tag : a.1=b.1) (val : a.2.val=b.2.val) : a=b := by
  obtain ⟨i,x,hx⟩ := a; obtain ⟨j,y,hy⟩ := b
  change i=j at tag; change x=y at val; subst j; subst y; rfl

private theorem single_mask_class (a : Fin U.tags) :
    taggedValueClass A (mask U {a}) = pieceClass (U.piece a) (U.isDefinable a) := by
  let f : (mask U {a}).points A ≃ U.piece a :=
    { toFun := fun ⟨i,x,h⟩ => ⟨x,(show i=a from h.1) ▸ h.2⟩
      invFun := fun x => ⟨a,x.val,rfl,x.property⟩
      left_inv := fun ⟨i,x,h⟩ => tagged_ext (show a=i from (show i=a from h.1).symm) rfl
      right_inv := fun _ => rfl }
  let e := f.trans (singlePoints (U.isDefinable a)).symm
  apply relation_sound (Relation.iso _ _ ⟨e,?_⟩)
  intro i j
  apply identity_tag_slice _ _ (mask U {a}).isDefinable i j True
  · intro x y
    constructor
    · intro eq
      exact ⟨trivial,congrArg (fun t => ((singlePoints (U.isDefinable a)) t).val) eq⟩
    · rintro ⟨_,eq⟩; exact tagged_ext (Subsingleton.elim _ _) eq
  · intro _ x hx; exact (show i=a from hx.1) ▸ hx.2

theorem taggedValueClass_eq_sum :
    taggedValueClass A U = ∑ i, pieceClass (U.piece i) (U.isDefinable i) := by
  classical
  have go (t : Finset (Fin U.tags)) : taggedValueClass A (mask U (t : Set _)) =
      ∑ i ∈ t, pieceClass (U.piece i) (U.isDefinable i) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty,Finset.coe_empty]
      exact relation_sound (Relation.empty (mask U (∅ : Set _)) ⟨fun x => x.2.property.1⟩)
    | insert i t hi ih =>
      rw [Finset.sum_insert hi,Finset.coe_insert,← Set.singleton_union,← ih,← single_mask_class]
      exact splitMask_class U _ _ (Set.disjoint_singleton_left.mpr hi)
  have top : mask U Set.univ = U := by
    cases U with
    | mk n p hp =>
      unfold mask
      congr
      funext i; ext x; exact ⟨fun h => h.2,fun h => ⟨Set.mem_univ _,h⟩⟩
  simpa only [Finset.coe_univ,top] using go Finset.univ

end GeneralizedEuler.Section4
