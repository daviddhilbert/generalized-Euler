module

public import Section4.RVTaggedEquivalence
import all Section4.RVTaggedEquivalence
import all Section4.RVProducts
import all Section4.Scissors

/-! Tagged disjoint union and Cartesian product preserve definable
bijections, including those which split individual components. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.RVFamily
set_option backward.isDefEq.respectTransparency false
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
variable (A B C D : RVFamily M S)

def single {I : Type} [Finite I] (U : Set (I → Z .rv)) (h : isRVSet M S U) : RVFamily M S where
  Tag := Unit
  Coord _ := I
  piece _ := U
  definable _ := h

def emptyFamily (M : SortedStructure L F Z) (S : SortedSubstructure M) : RVFamily M S where
  Tag := Empty
  Coord _ := Empty
  piece t := t.elim
  definable t := t.elim

def unitFamily (M : SortedStructure L F Z) (S : SortedSubstructure M) : RVFamily M S :=
  single (Set.univ : Set (Empty → Z .rv)) ⟨.imp .falsum .falsum,fun _ => by exact ⟨fun _ h => h, fun _ => trivial⟩⟩

def append : RVFamily M S where
  Tag := A.Tag ⊕ B.Tag
  Coord := Sum.elim A.Coord B.Coord
  finiteCoord i := by cases i with | inl j => exact A.finiteCoord j | inr j => exact B.finiteCoord j
  piece := fun i => match i with | .inl j => A.piece j | .inr j => B.piece j
  definable := fun i => by cases i with | inl j => exact A.definable j | inr j => exact B.definable j

def product : RVFamily M S where
  Tag := A.Tag × B.Tag
  Coord t := A.Coord t.1 ⊕ B.Coord t.2
  piece t := productSet (A.piece t.1) (B.piece t.2)
  definable t := rv_product_definable (A.definable t.1) (B.definable t.2)

def appendPoints : A.Points ⊕ B.Points ≃ (A.append B).Points where
  toFun := Sum.elim (fun a => ⟨.inl a.1,a.2⟩) (fun b => ⟨.inr b.1,b.2⟩)
  invFun x := match x with | ⟨.inl i,p⟩ => .inl ⟨i,p⟩ | ⟨.inr j,p⟩ => .inr ⟨j,p⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by obtain ⟨i,p⟩ := x; cases i <;> rfl

def cartesianPoints : A.Points × B.Points ≃ (A.product B).Points where
  toFun x := ⟨(x.1.1,x.2.1),productPoints _ _ (x.1.2,x.2.2)⟩
  invFun x := (⟨x.1.1,((productPoints _ _).symm x.2).1⟩,⟨x.1.2,((productPoints _ _).symm x.2).2⟩)
  left_inv _ := rfl
  right_inv x := Sigma.ext rfl (heq_of_eq ((productPoints _ _).apply_symm_apply x.2))

theorem append_congr (ab : A.Iso B) (cd : C.Iso D) : (A.append C).Iso (B.append D) := by
  obtain ⟨f,hf⟩ := ab
  obtain ⟨g,hg⟩ := cd
  let e := (appendPoints A C).symm.trans ((Equiv.sumCongr f g).trans (appendPoints B D))
  refine ⟨e,fun i j => ?_⟩
  cases i with
  | inl i => cases j with
    | inl j =>
      refine (show graphPiece _ _ e (.inl i) (.inl j) = graphPiece A B f i j from ?_).symm ▸ hf i j
      ext w
      constructor
      · rintro ⟨x,y,hx,hy,h⟩
        exact ⟨x,y,hx,hy,Sum.inl.inj ((appendPoints B D).injective h)⟩
      · rintro ⟨x,y,hx,hy,h⟩
        exact ⟨x,y,hx,hy,congrArg (fun p => appendPoints B D (.inl p)) h⟩
    | inr j =>
      have eq : graphPiece _ _ e (.inl i) (.inr j) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        fun _ ⟨_,_,_,_,h⟩ => Sum.inl_ne_inr (congrArg Sigma.fst h)
      rw [eq]; exact ⟨.falsum, fun _ => Iff.rfl⟩
  | inr i => cases j with
    | inl j =>
      have eq : graphPiece _ _ e (.inr i) (.inl j) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        fun _ ⟨_,_,_,_,h⟩ => Sum.inr_ne_inl (congrArg Sigma.fst h)
      rw [eq]; exact ⟨.falsum, fun _ => Iff.rfl⟩
    | inr j =>
      refine (show graphPiece _ _ e (.inr i) (.inr j) = graphPiece C D g i j from ?_).symm ▸ hg i j
      ext w
      constructor
      · rintro ⟨x,y,hx,hy,h⟩
        exact ⟨x,y,hx,hy,Sum.inr.inj ((appendPoints B D).injective h)⟩
      · rintro ⟨x,y,hx,hy,h⟩
        exact ⟨x,y,hx,hy,congrArg (fun p => appendPoints B D (.inr p)) h⟩

theorem product_congr (ab : A.Iso B) (cd : C.Iso D) : (A.product C).Iso (B.product D) := by
  obtain ⟨f,hf⟩ := ab
  obtain ⟨g,hg⟩ := cd
  let e := (cartesianPoints A C).symm.trans ((Equiv.prodCongr f g).trans (cartesianPoints B D))
  refine ⟨e,fun ⟨i,s⟩ ⟨j,t⟩ => ?_⟩
  let left : A.Coord i ⊕ B.Coord j → (A.Coord i ⊕ C.Coord s) ⊕ (B.Coord j ⊕ D.Coord t) := Sum.map Sum.inl Sum.inl
  let right : C.Coord s ⊕ D.Coord t → (A.Coord i ⊕ C.Coord s) ⊕ (B.Coord j ⊕ D.Coord t) := Sum.map Sum.inr Sum.inr
  let P := {w | w ∘ left ∈ graphPiece A B f i j} ∩ {w | w ∘ right ∈ graphPiece C D g s t}
  have hp : isRVSet M S P := isRVSet_inter (isRVSet_precomp left (hf i j)) (isRVSet_precomp right (hg s t))
  refine (show graphPiece _ _ e (i,s) (j,t) = P from ?_).symm ▸ hp
  ext w; constructor
  · rintro ⟨x,y,hx,hy,h⟩
    let a := (productPoints _ _).symm x
    let b := (productPoints _ _).symm y
    have eq := congrArg (cartesianPoints B D).symm h
    exact ⟨⟨a.1,b.1,congrArg (· ∘ Sum.inl) hx,congrArg (· ∘ Sum.inl) hy,congrArg Prod.fst eq⟩,
      ⟨a.2,b.2,congrArg (· ∘ Sum.inr) hx,congrArg (· ∘ Sum.inr) hy,congrArg Prod.snd eq⟩⟩
  · rintro ⟨⟨x,y,hx,hy,ef⟩,x',y',hx',hy',eg⟩
    exact ⟨productPoints _ _ (x,x'),productPoints _ _ (y,y'),
      funext (fun z => by cases z with | inl r => exact congrFun hx r | inr r => exact congrFun hx' r),
      funext (fun z => by cases z with | inl r => exact congrFun hy r | inr r => exact congrFun hy' r),
      congrArg (cartesianPoints B D) (show (f ⟨i,x⟩,g ⟨s,x'⟩) = (⟨j,y⟩,⟨t,y'⟩) from Prod.ext ef eg)⟩

end GeneralizedEuler.Section4.RVFamily
