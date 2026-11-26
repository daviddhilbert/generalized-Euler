module

public import Section4.TaggedMatchGraph
import all Section4.TaggedMatchGraph
import all Section4.RVTaggedEquivalence
import all Section4.Factors
import all Section4.ValuePullback
import all Section4.UnaryTaggedComparison

/-! Restrict a definable tagged bijection to finite unions of individually
definable label fibers. Different tags may carry the same value. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {Γ : Type*} {J : Language} [J.Structure Γ] (v : Z .rv → Γ) (A : Set Γ)
  (defSharp : ∀ {k} {C : Set (Fin k → Γ)}, A.Definable J C → isRVSet M S (sharp M v C))
  {k n m : ℕ} (U W : Over (J := J) A k)

variable (D : Set (U.points A)) (e : Fin n ≃ D)
  (de : ∀ i, A.Definable J {pointTuple U (e i).val})

@[expose] def selectedFamily : RVFamily M S where
  Tag := Fin n
  Coord _ := Fin k
  piece i := sharp M v {pointTuple U (e i).val}
  definable i := defSharp (de i)

local notation "sh" => taggedSharp (S := S) v A defSharp
local notation "lab" => sharpLabel (S := S) v A defSharp

private theorem tagged_ext {I X : Type*} {C : I → Set X} {a b : Σ i, C i}
    (tag : a.1 = b.1) (point : a.2.val = b.2.val) : a=b := by
  obtain ⟨i,x⟩ := a; obtain ⟨j,y⟩ := b; obtain rfl : i=j := tag
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext point))

private def sharpTuple (x : (sh U).Points) : Fin k → Z .rv := x.2.val

private theorem sharp_ext {x y : (sh U).Points} (h : x.1=y.1) (r : sharpTuple v A defSharp U x = sharpTuple v A defSharp U y) : x=y := by
  obtain ⟨i,a⟩ := x; obtain ⟨j,b⟩ := y; obtain rfl : i=j := h
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext r))

def selectedInclusion (x : (selectedFamily v A defSharp U D e de).Points) : (sh U).Points :=
  ⟨(e x.1).val.1,x.2.val,x.2.property.1,(congrArg (· ∈ U.piece (e x.1).val.1) x.2.property.2).mpr (e x.1).val.2.property⟩

theorem selectedInclusion_label (x : (selectedFamily v A defSharp U D e de).Points) :
    lab U (selectedInclusion v A defSharp U D e de x) = (e x.1).val :=
  by exact tagged_ext rfl x.2.property.2

def selectedPoints : (selectedFamily v A defSharp U D e de).Points ≃ {x : (sh U).Points // lab U x ∈ D} := by
  let h (x : (selectedFamily v A defSharp U D e de).Points) :
      lab U (selectedInclusion v A defSharp U D e de x) ∈ D :=
    (selectedInclusion_label v A defSharp U D e de x).symm ▸ (e x.1).property
  let g x := (⟨selectedInclusion v A defSharp U D e de x,h x⟩ : {x : (sh U).Points // lab U x ∈ D})
  apply Equiv.ofBijective g
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ eq
    have labels := congrArg (fun p : {x : (sh U).Points // lab U x ∈ D} => lab U p.val) eq
    change lab U (selectedInclusion v A defSharp U D e de ⟨i,x⟩) = lab U (selectedInclusion v A defSharp U D e de ⟨j,y⟩) at labels
    rw [selectedInclusion_label,selectedInclusion_label] at labels
    obtain rfl : i=j := e.injective (Subtype.ext labels)
    have coord := congrArg (fun z : {x : (sh U).Points // lab U x ∈ D} => sharpTuple v A defSharp U z.val) eq
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext coord))
  · rintro ⟨⟨t,x⟩,hx⟩
    obtain ⟨i,hi⟩ := e.surjective ⟨lab U ⟨t,x⟩,hx⟩
    have eq : (e i).val = lab U ⟨t,x⟩ := congrArg Subtype.val hi
    have tag : (e i).val.1 = t := congrArg Sigma.fst eq
    let p : (selectedFamily v A defSharp U D e de).Points :=
      ⟨i,x.val,x.property.1,(congrArg (pointTuple U) eq).symm⟩
    refine ⟨p,Subtype.ext ?_⟩
    exact sharp_ext v A defSharp U (x := selectedInclusion v A defSharp U D e de p) (y := ⟨t,x⟩) tag rfl

variable (E : Set (W.points A)) (g : Fin m ≃ E)
  (dg : ∀ j, A.Definable J {pointTuple W (g j).val})

theorem selected_iso
    (f : (sh U).Points ≃ (sh W).Points)
    (graph : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ f i j))
    (keep : ∀ x, lab U x ∈ D ↔ lab W (f x) ∈ E) :
    (selectedFamily v A defSharp U D e de).Iso (selectedFamily v A defSharp W E g dg) := by
  let a := selectedPoints v A defSharp U D e de
  let b := selectedPoints v A defSharp W E g dg
  let h := a.trans ((f.subtypeEquiv keep).trans b.symm)
  have law x y : h x = y ↔ f (selectedInclusion v A defSharp U D e de x) = selectedInclusion v A defSharp W E g dg y := by
    change b.symm ((f.subtypeEquiv keep) (a x)) = y ↔ _
    rw [b.symm_apply_eq]
    exact Subtype.ext_iff
  refine ⟨h,fun i j => ?_⟩
  let c := selectedFamily v A defSharp U D e de
  let d := selectedFamily v A defSharp W E g dg
  let aux := {w : Fin k ⊕ Fin k → Z .rv |
    (w ∘ Sum.inl ∈ c.piece i ∧ w ∘ Sum.inr ∈ d.piece j) ∧
    w ∈ RVFamily.graphPiece _ _ f (e i).val.1 (g j).val.1}
  have hp : isRVSet M S aux := isRVSet_inter (isRVSet_inter
    (isRVSet_precomp Sum.inl (c.definable i)) (isRVSet_precomp Sum.inr (d.definable j))) (graph _ _)
  refine (show RVFamily.graphPiece c d h i j = aux from ?_).symm ▸ hp
  ext w; constructor
  · rintro ⟨x,y,hx,hy,hh⟩
    exact ⟨⟨hx ▸ x.property,hy ▸ y.property⟩,
      (selectedInclusion v A defSharp U D e de ⟨i,x⟩).2,(selectedInclusion v A defSharp W E g dg ⟨j,y⟩).2,hx,hy,(law _ _).mp hh⟩
  · rintro ⟨⟨hx,hy⟩,x,y,l,r,hh⟩
    let a' : c.Points := ⟨i,_,hx⟩
    let b' : d.Points := ⟨j,_,hy⟩
    have left : (⟨_,x⟩ : (sh U).Points) = selectedInclusion v A defSharp U D e de a' := sharp_ext v A defSharp U (x := ⟨_,x⟩) (y := selectedInclusion v A defSharp U D e de a') rfl l
    have right : (⟨_,y⟩ : (sh W).Points) = selectedInclusion v A defSharp W E g dg b' := sharp_ext v A defSharp W (x := ⟨_,y⟩) (y := selectedInclusion v A defSharp W E g dg b') rfl r
    exact ⟨a'.2,b'.2,rfl,rfl,(law a' b').mpr ((congrArg f left).symm.trans (hh.trans right))⟩

end GeneralizedEuler.Section4
