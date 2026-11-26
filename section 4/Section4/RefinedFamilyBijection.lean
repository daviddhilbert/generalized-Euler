module

public import Section4.RVTaggedEquivalence
import all Section4.RVTaggedEquivalence
import all Section4.FiniteScissors
import all Section4.RVProducts

/-! Restrict an RV bijection to finite families of disjoint pieces. Each
piece keeps the coordinates of its original tag; the bijection may take
one refined tag into several target tags. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.RVFamily
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {J : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure J F Z} {S : SortedSubstructure M}

structure Subfamily (A : RVFamily M S) where
  Tag : Type
  [finite : Finite Tag]
  parent : Tag → A.Tag
  piece : (i : Tag) → Set (A.Coord (parent i) → Z .rv)
  definable : ∀ i, isRVSet M S (piece i)
  subset : ∀ i, piece i ⊆ A.piece (parent i)

namespace Subfamily
attribute [instance] finite
variable {A B : RVFamily M S} (D : Subfamily A) (E : Subfamily B)

@[expose] def family : RVFamily M S where
  Tag := D.Tag
  Coord i := A.Coord (D.parent i)
  piece := D.piece
  definable := D.definable

def includePoint (p : D.family.Points) : A.Points := ⟨D.parent p.1,p.2.val,D.subset p.1 p.2.property⟩

theorem include_injective
    (unique : ∀ (i j : D.Tag) (x : D.piece i) (y : D.piece j),
      (⟨D.parent i,x.val,D.subset i x.property⟩ : A.Points) = ⟨D.parent j,y.val,D.subset j y.property⟩ → i = j) :
    Function.Injective D.includePoint := by
  rintro ⟨i,x⟩ ⟨j,y⟩ e
  obtain rfl := unique i j x y e
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (congrArg (fun z : A.piece (D.parent i) => z.val) (Sigma.mk.inj_iff.mp e).2.eq)))

theorem restrict_bijection (f : A.Points ≃ B.Points)
    (graph : ∀ i j, isRVSet M S (graphPiece A B f i j))
    (di : Function.Injective D.includePoint) (ei : Function.Injective E.includePoint)
    (keep : ∀ x, x ∈ Set.range D.includePoint ↔ f x ∈ Set.range E.includePoint) :
    D.family.Iso E.family := by
  let d := Equiv.ofInjective D.includePoint di
  let e := Equiv.ofInjective E.includePoint ei
  let mid : Set.range D.includePoint ≃ Set.range E.includePoint :=
    ⟨fun x => ⟨f x.val,(keep _).mp x.property⟩,fun y => ⟨f.symm y.val,(keep _).mpr (by rw [f.apply_symm_apply]; exact y.property)⟩,
      fun x => Subtype.ext (f.symm_apply_apply _),fun y => Subtype.ext (f.apply_symm_apply _)⟩
  let q := d.trans (mid.trans e.symm)
  have comm (x) : E.includePoint (q x) = f (D.includePoint x) := congrArg Subtype.val (e.apply_symm_apply (mid (d x)))
  refine ⟨q,fun i j => ?_⟩
  have hd := isRVSet_inter (rv_product_definable (D.definable i) (E.definable j)) (graph (D.parent i) (E.parent j))
  refine (show graphPiece D.family E.family q i j = productSet (D.piece i) (E.piece j) ∩
      graphPiece A B f (D.parent i) (E.parent j) from ?_).symm ▸ hd
  ext z
  constructor
  · rintro ⟨x,y,hx,hy,eq⟩
    exact ⟨⟨hx ▸ x.property,hy ▸ y.property⟩,⟨x.val,D.subset _ x.property⟩,⟨y.val,E.subset _ y.property⟩,hx,hy,
      (comm ⟨i,x⟩).symm.trans (congrArg E.includePoint eq)⟩
  · rintro ⟨⟨hx,hy⟩,x,y,h₁,h₂,eq⟩
    let u : D.piece i := ⟨_,hx⟩
    let w : E.piece j := ⟨_,hy⟩
    have ux : D.includePoint ⟨i,u⟩ = ⟨D.parent i,x⟩ := Sigma.ext rfl (heq_of_eq (Subtype.ext h₁.symm))
    have wy : E.includePoint ⟨j,w⟩ = ⟨E.parent j,y⟩ := Sigma.ext rfl (heq_of_eq (Subtype.ext h₂.symm))
    exact ⟨u,w,rfl,rfl,ei (((comm _).trans (congrArg f ux)).trans (eq.trans wy.symm))⟩

end Subfamily
end GeneralizedEuler.Section4.RVFamily
