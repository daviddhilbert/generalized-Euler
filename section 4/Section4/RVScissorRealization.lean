module

public import Section4.RVFamilySemiring
import all Section4.RVFamilySemiring
import all Section4.RVFamilyOperations
import all Section4.RVTaggedEquivalence
import all Section4.ValueFactorMap

/-! Equalities in the RV scissor semiring yield fixed-base definable
bijections of the original finite tagged unions. No cancellation is used. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.RVFamily
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}

theorem single_iso {I J : Type} [Finite I] [Finite J] {D : Set (I → Z .rv)} {E : Set (J → Z .rv)}
    (hd : isRVSet M S D) (he : isRVSet M S E) (iso : RVDefinablyEquivalent M S.carrier D E) :
    (single D hd).Iso (single E he) := iso_retag _ _ (Equiv.refl Unit) (fun _ => iso)

private def singlePoints {I : Type} [Finite I] (D : Set (I → Z .rv)) (hd : isRVSet M S D) :
    (single D hd).Points ≃ D where
  toFun x := x.2
  invFun x := ⟨(),x⟩
  left_inv := fun ⟨(),_⟩ => rfl
  right_inv _ := rfl

theorem single_empty {I : Type} [Finite I] {D : Set (I → Z .rv)} (hd : isRVSet M S D)
    (empty : D = ∅) : (single D hd).Iso (emptyFamily M S) := by
  subst D
  let h : IsEmpty (single (∅ : Set (I → Z .rv)) hd).Points := ⟨fun x => x.2.property⟩
  let h' : IsEmpty (emptyFamily M S).Points := ⟨fun x => x.1.elim⟩
  exact ⟨Equiv.equivOfIsEmpty _ _,fun _ j => j.elim⟩

theorem single_unit {I : Type} [Finite I] {D : Set (I → Z .rv)} (hd : isRVSet M S D)
    (one : ∃ x, D={x}) : (single D hd).Iso (unitFamily M S) := by
  obtain ⟨x,rfl⟩ := one
  apply iso_retag _ _ (Equiv.refl Unit)
  intro _
  let e : ({x} : Set _) ≃ (Set.univ : Set (Empty → Z .rv)) :=
    { toFun := fun _ => ⟨Empty.elim,trivial⟩
      invFun := fun _ => ⟨x,rfl⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  refine ⟨e,?_⟩
  have defG := isRVSet_precomp (J := I ⊕ Empty) Sum.inl hd
  let H := {w : I ⊕ Empty → Z .rv | ∃ y : ({x} : Set _), y.val = w ∘ Sum.inl ∧ (e y).val = w ∘ Sum.inr}
  change isRVSet M S H
  refine (show H = {w | w ∘ Sum.inl ∈ ({x} : Set _)} from ?_).symm ▸ defG
  apply Set.ext; intro w
  exact ⟨fun ⟨y,hy,_⟩ => (congrArg (· ∈ ({x} : Set _)) hy).mp y.property, fun h => ⟨⟨_,h⟩,rfl,Subsingleton.elim _ _⟩⟩

theorem single_cut {I : Type} [Finite I] {A B : Set (I → Z .rv)}
    (ha : isRVSet M S A) (hb : isRVSet M S B) (disj : Disjoint A B) :
    ((single A ha).append (single B hb)).Iso (single (A ∪ B) (ha.union hb)) := by
  classical
  let f := (appendPoints (single A ha) (single B hb)).symm.trans
      ((Equiv.sumCongr (singlePoints A ha) (singlePoints B hb)).trans
      ((Equiv.Set.union disj).symm.trans (singlePoints (A ∪ B) (ha.union hb)).symm))
  refine ⟨f,fun i _ => ?_⟩
  have diag (D : Set (I → Z .rv)) (hd : isRVSet M S D) :
      isRVSet M S {w : I ⊕ I → Z .rv | w ∘ Sum.inl ∈ D ∧ w ∘ Sum.inl = w ∘ Sum.inr} := by
    let aux := (isRVSet_precomp (J := I ⊕ I) Sum.inl hd).inter
      (SortedDefinableOver.iInter fun i : I => SortedDefinableOver.coordinate_eq
        (M := M) (A := S.carrier) (Var := RVVariables (I ⊕ I)) .rv (.inl i) (.inr i))
    unfold isRVSet
    convert aux using 1
    ext w; simp [funext_iff]
  cases i with
  | inl u =>
    refine (show graphPiece _ _ f (.inl u) () = _ from ?_).symm ▸ diag A ha
    ext w; constructor
    · rintro ⟨a,b,hx,hy,h⟩
      have eq : a.val = b.val := congrArg (fun p => ((singlePoints _ _ p).val)) h
      exact ⟨hx ▸ a.property,hx.symm.trans (eq.trans hy)⟩
    · rintro ⟨h,eq⟩
      exact ⟨⟨_,h⟩,⟨_,Or.inl h⟩,rfl,eq,rfl⟩
  | inr u =>
    refine (show graphPiece _ _ f (.inr u) () = _ from ?_).symm ▸ diag B hb
    ext w; constructor
    · rintro ⟨b,a,hx,hy,h⟩
      have eq : b.val = a.val := congrArg (fun p => ((singlePoints _ _ p).val)) h
      exact ⟨hx ▸ b.property,hx.symm.trans (eq.trans hy)⟩
    · rintro ⟨h,eq⟩
      exact ⟨⟨_,h⟩,⟨_,Or.inr h⟩,rfl,eq,rfl⟩

private theorem single_congr {I : Type} [Finite I] {D E : Set (I → Z .rv)} (eq : D=E)
    (hd : isRVSet M S D) (he : isRVSet M S E) : (single D hd).Iso (single E he) := by
  subst E; apply iso_refl

def realizeScissors (M : SortedStructure L F Z) (S : SortedSubstructure M) :
    RVSemiring M S →+* Classes M S := by
  let w (x : GradedObject M S) := cls (single x.2.carrier x.2.definable)
  apply descendWeights M S w
  intro a b relation
  cases relation with
  | iso U V h => simpa [w] using (cls_eq_iff _ _).mpr (single_iso U.definable V.definable h)
  | zero U h => simpa only [w,MvPolynomial.eval₂_X,MvPolynomial.eval₂_zero,cls_empty] using (cls_eq_iff _ _).mpr (single_empty U.definable h)
  | one U h => simpa only [w,MvPolynomial.eval₂_X,MvPolynomial.eval₂_one,cls_unit] using (cls_eq_iff _ _).mpr (single_unit U.definable h)
  | cut U V W A B ha hb disj cov ea eb =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_add,w,← cls_append]
    apply (cls_eq_iff _ _).mpr
    have same : (single U.carrier U.definable).Iso (single (A ∪ B) (ha.union hb)) := single_congr cov.symm _ _
    exact iso_trans _ _ _ same (iso_trans _ _ _ (iso_symm _ _ (single_cut ha hb disj))
      (append_congr _ _ _ _ (single_iso ha V.definable ea) (single_iso hb W.definable eb)))
  | prod U V W h =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul,w,← cls_product]
    apply (cls_eq_iff _ _).mpr
    let e : Unit ≃ Unit × Unit := (Equiv.punitProd Unit).symm
    exact iso_retag _ _ e (fun _ => h.symm)

@[simp] theorem realizeScissors_class (U : GradedObject M S) :
    realizeScissors M S (objectClass M S U) = cls (single U.2.carrier U.2.definable) := by
  unfold realizeScissors
  apply descendWeights_class

end GeneralizedEuler.Section4.RVFamily
