module

public import Section4.RVProducts
public import Section4.WholeFiberRelation
import all Section4.ValueFactorMap

/-! Finite disjoint unions of definable RV sets, with a definable graph
on each pair of tags. This realizes the cut relations before cancellation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} (M : SortedStructure L F Z) (S : SortedSubstructure M)

structure RVFamily where
  Tag : Type
  [finiteTag : Finite Tag]
  Coord : Tag → Type
  [finiteCoord : ∀ i, Finite (Coord i)]
  piece : (i : Tag) → Set (Coord i → Z .rv)
  definable : ∀ i, isRVSet M S (piece i)

namespace RVFamily
attribute [instance] finiteTag finiteCoord
variable {M S} (A B C : RVFamily M S)

abbrev Points := (i : A.Tag) × A.piece i

def graphPiece (f : A.Points → B.Points) (i : A.Tag) (j : B.Tag) :
    Set (A.Coord i ⊕ B.Coord j → Z .rv) :=
  {w | ∃ (x : A.piece i) (y : B.piece j), x.val = w ∘ Sum.inl ∧ y.val = w ∘ Sum.inr ∧
    f ⟨i,x⟩ = ⟨j,y⟩}

def Iso (A B : RVFamily M S) : Prop :=
  ∃ f : A.Points ≃ B.Points, ∀ i j, isRVSet M S (graphPiece A B f i j)

theorem iso_retag (t : A.Tag ≃ B.Tag)
    (pieces : ∀ i, RVDefinablyEquivalent M S.carrier (A.piece i) (B.piece (t i))) : A.Iso B := by
  classical
  choose e he using pieces
  let f : A.Points ≃ B.Points := Equiv.sigmaCongr t e
  refine ⟨f,fun i j => ?_⟩
  by_cases eq : t i = j
  · subst j
    let G := {w : A.Coord i ⊕ B.Coord (t i) → Z .rv |
      ∃ x : A.piece i, x.val = w ∘ Sum.inl ∧ (e i x).val = w ∘ Sum.inr}
    have hg : isRVSet M S G := he i
    convert hg using 1
    ext w; constructor
    · rintro ⟨x,y,hx,hy,h⟩
      have same : e i x = y := (Sigma.mk.inj_iff.mp h).2.eq
      exact ⟨x,hx,same ▸ hy⟩
    · rintro ⟨x,hx,hy⟩
      exact ⟨x,e i x,hx,hy,rfl⟩
  · have empty : graphPiece A B f i j = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨_,_,_,_,h⟩ => eq (congrArg Sigma.fst h)
    rw [empty]; exact ⟨.falsum,fun _ => Iff.rfl⟩

theorem iso_refl : A.Iso A := by
  apply iso_retag A A (Equiv.refl _)
  intro i
  exact rv_reindex_equivalent M S (Equiv.refl _) _ (A.definable i)

theorem inverse_graph (f : A.Points ≃ B.Points) (graph : ∀ i j, isRVSet M S (graphPiece A B f i j))
    (j : B.Tag) (i : A.Tag) : isRVSet M S (graphPiece B A f.symm j i) := by
  convert isRVSet_precomp Sum.swap (graph i j) using 1
  ext w; constructor
  · rintro ⟨y,x,hy,hx,h⟩
    exact ⟨x,y,hx,hy,(f.symm_apply_eq.mp h).symm⟩
  · rintro ⟨x,y,hx,hy,h⟩
    exact ⟨y,x,hy,hx,f.symm_apply_eq.mpr h.symm⟩

theorem iso_symm (h : A.Iso B) : B.Iso A := by
  obtain ⟨f,graph⟩ := h
  exact ⟨f.symm,inverse_graph A B f graph⟩

theorem iso_trans (ab : A.Iso B) (bc : B.Iso C) : A.Iso C := by
  obtain ⟨f,hf⟩ := ab
  obtain ⟨g,hg⟩ := bc
  refine ⟨f.trans g,fun i k => ?_⟩
  let via (j : B.Tag) := {w : A.Coord i ⊕ C.Coord k → Z .rv |
    ∃ y : B.Coord j → Z .rv,
      Sum.elim (w ∘ Sum.inl) y ∈ graphPiece A B f i j ∧
      Sum.elim y (w ∘ Sum.inr) ∈ graphPiece B C g j k}
  have defVia j : isRVSet M S (via j) := isRVSet_project
    (isRVSet_inter (isRVSet_precomp (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (hf i j))
      (isRVSet_precomp (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) (hg j k)))
  have eq : graphPiece A C (f.trans g) i k = ⋃ j, via j := by
    ext w; rw [Set.mem_iUnion]; constructor
    · rintro ⟨x,z,hx,hz,h⟩
      let y := f ⟨i,x⟩
      exact ⟨y.1,y.2.val,⟨x,y.2,hx,rfl,rfl⟩,y.2,z,rfl,hz,h⟩
    · rintro ⟨j,p,⟨x,y,hx,hy,hf'⟩,y',z,hy',hz,hg'⟩
      have eq : y=y' := Subtype.ext (hy.trans hy'.symm)
      exact ⟨x,z,hx,hz,(congrArg g hf').trans (eq.symm ▸ hg')⟩
  rw [eq]
  exact isRVSet_iUnion defVia

end RVFamily
end GeneralizedEuler.Section4
