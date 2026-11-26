module

public import Section4.SignedWholeMatches
import all Section4.FiniteScissors
import all Section4.RVTaggedEquivalence
import all Section4.WholeFiberRelation
import all Section4.Scissors

/-! Fixed-base definability of whole matches on representative pairs. The
test quantifies over every graph component, including components outside
the chosen source and target tags. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.RVFamily
open FirstOrder GeneralizedEuler.Section2
variable {J : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure J F Z}
  {S : SortedSubstructure M} (A B : RVFamily M S)

private theorem definable_all {I N : Type} [Finite N] (D : N → Set (I → Z .rv))
    (hd : ∀ n, isRVSet M S (D n)) : isRVSet M S {x | ∀ n, x ∈ D n} := by
  unfold isRVSet
  convert SortedDefinableOver.iInter hd using 1
  ext x
  simp

/-- A label on a family can be tested on representatives tag by tag. -/
structure LabelTest (A : RVFamily M S) (L : Type*) (label : A.Points → L) where
  test : (i j : A.Tag) → (A.Coord i → Z .rv) → (A.Coord j → Z .rv) → Prop
  definable : ∀ i j, isRVSet M S {p : A.Coord i ⊕ A.Coord j → Z .rv |
    test i j (p ∘ Sum.inl) (p ∘ Sum.inr)}
  correct : ∀ (i j) (x : A.piece i) (y : A.piece j),
    test i j x.val y.val ↔ label ⟨i,x⟩ = label ⟨j,y⟩

variable {X Y : Type*} {a : A.Points → X} {b : B.Points → Y}
  (ta : LabelTest A X a) (tb : LabelTest B Y b)
  (f : A.Points ≃ B.Points) (graph : ∀ i j, isRVSet M S (graphPiece A B f i j))

def representedMatches (i : A.Tag) (j : B.Tag) : Set (A.Coord i ⊕ B.Coord j → Z .rv) :=
  {p | ∃ (x : A.piece i) (y : B.piece j), x.val = p ∘ Sum.inl ∧ y.val = p ∘ Sum.inr ∧
      WholeMatch a b f (a ⟨i,x⟩) (b ⟨j,y⟩)}

theorem mem_representedMatches (i : A.Tag) (j : B.Tag) (x : A.Coord i → Z .rv) (y : B.Coord j → Z .rv) :
    Sum.elim x y ∈ representedMatches A B (a := a) (b := b) f i j ↔
      ∃ (hx : x ∈ A.piece i) (hy : y ∈ B.piece j),
        WholeMatch a b f (a ⟨i,x,hx⟩) (b ⟨j,y,hy⟩) := by
  constructor
  · rintro ⟨⟨u,hu⟩,⟨w,hw⟩,h,k,whole⟩
    change u = x at h
    change w = y at k
    subst x
    subst y
    exact ⟨hu,hw,whole⟩
  · rintro ⟨hx,hy,whole⟩
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,rfl,rfl,whole⟩

theorem representedMatches_inverse (i : A.Tag) (j : B.Tag) (x : A.Coord i → Z .rv) (y : B.Coord j → Z .rv) :
    Sum.elim y x ∈ representedMatches B A (a := b) (b := a) f.symm j i ↔
      Sum.elim x y ∈ representedMatches A B (a := a) (b := b) f i j := by
  rw [mem_representedMatches,mem_representedMatches]
  exact ⟨fun ⟨hy,hx,h⟩ => ⟨hx,hy,(wholeMatch_inverse a b f _ _).mp h⟩,
    fun ⟨hx,hy,h⟩ => ⟨hy,hx,(wholeMatch_inverse a b f _ _).mpr h⟩⟩

include ta tb graph in
theorem representedMatches_definable (i : A.Tag) (j : B.Tag) :
    isRVSet M S (representedMatches A B (a := a) (b := b) f i j) := by
  let N := A.Coord i ⊕ B.Coord j
  let D (t : A.Tag × B.Tag) : Set (N → Z .rv) :=
    {p | ∀ w : A.Coord t.1 ⊕ B.Coord t.2 → Z .rv, w ∈ graphPiece A B f t.1 t.2 →
      (ta.test i t.1 (p ∘ Sum.inl) (w ∘ Sum.inl) ↔ tb.test j t.2 (p ∘ Sum.inr) (w ∘ Sum.inr))}
  have hd (t) : isRVSet M S (D t) := by
    let U := A.Coord t.1 ⊕ B.Coord t.2
    let pa : A.Coord i ⊕ A.Coord t.1 → N ⊕ U := Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
    let pb : B.Coord j ⊕ B.Coord t.2 → N ⊕ U := Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr)
    have ha := isRVSet_precomp pa (ta.definable i t.1)
    have hb := isRVSet_precomp pb (tb.definable j t.2)
    have hg := isRVSet_precomp (Sum.inr : U → N ⊕ U) (graph t.1 t.2)
    apply isRVSet_forall (D := {z : N ⊕ U → Z .rv | z ∘ Sum.inr ∈ graphPiece A B f t.1 t.2 →
      (ta.test i t.1 (z ∘ Sum.inl ∘ Sum.inl) (z ∘ Sum.inr ∘ Sum.inl) ↔
       tb.test j t.2 (z ∘ Sum.inl ∘ Sum.inr) (z ∘ Sum.inr ∘ Sum.inr))})
    unfold isRVSet
    convert hg.compl.union ((ha.inter hb).union (ha.compl.inter hb.compl)) using 1
    ext z
    change (_ → (_ ↔ _)) ↔ ¬ _ ∨ (_ ∧ _) ∨ (¬ _ ∧ ¬ _)
    tauto
  have h := isRVSet_inter (rv_product_definable (A.definable i) (B.definable j)) (definable_all D hd)
  refine (show representedMatches A B (a := a) (b := b) f i j =
      productSet (A.piece i) (B.piece j) ∩ {p | ∀ t, p ∈ D t} from ?_).symm ▸ h
  ext p
  constructor
  · rintro ⟨x,y,hx,hy,whole⟩
    refine ⟨⟨hx ▸ x.property,hy ▸ y.property⟩,?_⟩
    rintro ⟨m,n⟩ w ⟨u,v,hu,hv,eq⟩
    change ta.test i m (p ∘ Sum.inl) (w ∘ Sum.inl) ↔ tb.test j n (p ∘ Sum.inr) (w ∘ Sum.inr)
    rw [← hx,← hy,← hu,← hv,ta.correct,tb.correct,← eq]
    exact eq_comm.trans (((wholeMatch_iff a b f _ _).mp whole ⟨m,u⟩).trans eq_comm)
  · rintro ⟨⟨hx,hy⟩,allTags⟩
    let x : A.piece i := ⟨p ∘ Sum.inl,hx⟩
    let y : B.piece j := ⟨p ∘ Sum.inr,hy⟩
    refine ⟨x,y,rfl,rfl,(wholeMatch_iff a b f _ _).mpr ?_⟩
    rintro ⟨m,u⟩
    generalize eq : f ⟨m,u⟩ = z
    obtain ⟨n,v⟩ := z
    have test := allTags (m,n) (Sum.elim u.val v.val) ⟨u,v,rfl,rfl,eq⟩
    change ta.test i m x.val u.val ↔ tb.test j n y.val v.val at test
    rw [ta.correct,tb.correct] at test
    exact eq_comm.trans (test.trans eq_comm)

end GeneralizedEuler.Section4.RVFamily
