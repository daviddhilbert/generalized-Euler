module

public import Section5.MixedTaggedSemiring

/-! The VF scissor relations hold in the semiring of actual
mixed tagged bijections. Thus equality of VF classes supplies such a bijection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.MixedTaggedFamily

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {U V : TCsort → Type} [Finite (U .vf)] [Finite (U .rv)] [Finite (V .vf)] [Finite (V .rv)]

theorem single_iso {P : Set (SortedAssignment X U)} {Q : Set (SortedAssignment X V)}
    (dP : SortedDefinableOver M S.carrier P) (dQ : SortedDefinableOver M S.carrier Q)
    (e : MixedDefinablyEquivalent M S P Q) : (single P dP).Iso (single Q dQ) :=
  iso_retag _ _ (Equiv.refl Unit) (fun _ => e)

@[expose] def singlePoints (P : Set (SortedAssignment X U)) (dP : SortedDefinableOver M S.carrier P) :
    (single P dP).Points ≃ P where
  toFun x := x.2
  invFun x := ⟨(),x⟩
  left_inv := fun ⟨(),_⟩ => rfl
  right_inv _ := rfl

private theorem single_empty {P : Set (SortedAssignment X U)} (dP : SortedDefinableOver M S.carrier P)
    (h : P = ∅) : (single P dP).Iso (emptyFamily M S) := by
  subst P
  let : IsEmpty (single (∅ : Set (SortedAssignment X U)) dP).Points := ⟨fun x => x.2.property⟩
  let : IsEmpty (emptyFamily M S).Points := ⟨fun x => x.1.elim⟩
  exact ⟨Equiv.equivOfIsEmpty _ _,fun _ j => j.elim⟩

private theorem single_unit {P : Set (SortedAssignment X U)} (dP : SortedDefinableOver M S.carrier P)
    (h : ∃ x, P = {x}) : (single P dP).Iso (unitFamily M S) := by
  obtain ⟨x,rfl⟩ := h
  apply iso_retag _ _ (Equiv.refl Unit)
  intro _
  apply mixed_projection_equivalent (fun _ => Empty.elim) ({x} : Set (SortedAssignment X U))
    (Set.univ : Set (SortedAssignment X (fun _ => Empty))) dP
  refine ⟨fun _ _ => Set.mem_univ _,?_,?_⟩
  · intro a ha b hb _
    exact (Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm
  · intro b _
    exact ⟨x,rfl,Subsingleton.elim _ _⟩

private theorem single_cut {P Q : Set (SortedAssignment X U)} (dP : SortedDefinableOver M S.carrier P)
    (dQ : SortedDefinableOver M S.carrier Q) (disj : Disjoint P Q) :
    ((single P dP).append (single Q dQ)).Iso (single (P ∪ Q) (dP.union dQ)) := by
  classical
  let A := single P dP
  let B := single Q dQ
  let C := single (P ∪ Q) (dP.union dQ)
  let f : (A.append B).Points ≃ C.Points :=
    (A.appendPoints B).symm.trans ((Equiv.sumCongr (singlePoints P dP) (singlePoints Q dQ)).trans
      ((Equiv.Set.union disj).symm.trans (singlePoints (P ∪ Q) (dP.union dQ)).symm))
  let read (c : C.Points) : SortedAssignment X U := (singlePoints (P ∪ Q) (dP.union dQ) c).val
  refine ⟨f,fun i ⟨⟩ => ?_⟩
  cases i with
  | inl i =>
    apply (DefinableRelation.diagonal.inter_left dP).congr
    intro x y
    constructor
    · rintro ⟨rfl,hx⟩
      exact ⟨hx,Or.inl hx,rfl⟩
    · rintro ⟨hx,hy,e⟩
      have eq := congrArg read e
      exact ⟨eq,hx⟩
  | inr i =>
    apply (DefinableRelation.diagonal.inter_left dQ).congr
    intro x y
    constructor
    · rintro ⟨rfl,hx⟩
      exact ⟨hx,Or.inr hx,rfl⟩
    · rintro ⟨hx,hy,e⟩
      have eq := congrArg read e
      exact ⟨eq,hx⟩

variable [TopologicalSpace (X .vf)]

@[expose] def fieldObjectFamily (A : VFObject M S) : MixedTaggedFamily M S :=
  single A.2.carrier A.2.definable

private theorem fieldWeights_respect (a b : VFExpression M S) (h : VFRelation M S a b) :
    MvPolynomial.eval₂ (Nat.castRingHom (Classes M S)) (fun A => cls (fieldObjectFamily A)) a =
    MvPolynomial.eval₂ (Nat.castRingHom (Classes M S)) (fun A => cls (fieldObjectFamily A)) b := by
  cases h with
  | iso A B h =>
    simp only [MvPolynomial.eval₂_X]
    exact (cls_eq_iff _ _).2 (single_iso A.2.definable B.2.definable h)
  | zero A h =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_zero,← cls_empty]
    exact (cls_eq_iff _ _).2 (single_empty A.2.definable h)
  | one A h =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_one,← cls_unit]
    exact (cls_eq_iff _ _).2 (single_unit A.2.definable h)
  | cut A B C D E d e disj cover left right =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_add,← cls_append]
    apply (cls_eq_iff _ _).2
    have same : (fieldObjectFamily A).Iso (single (D ∪ E) (d.union e)) :=
      single_iso A.2.definable (d.union e) (cover.symm ▸ MixedDefinablyEquivalent.refl A.2.definable)
    exact iso_trans _ _ _ same (iso_trans _ _ _ (iso_symm _ _ (single_cut d e disj))
      (append_congr _ _ _ _ (single_iso d B.2.definable left) (single_iso e C.2.definable right)))
  | product A B C iso =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul,← cls_product]
    apply (cls_eq_iff _ _).2
    let tags : Unit ≃ Unit × Unit :=
      ⟨fun _ => ((),()),fun _ => (),fun x => by cases x; rfl,fun ⟨⟨⟩,⟨⟩⟩ => rfl⟩
    exact iso_retag _ _ tags (fun _ => iso.symm)

def realizeScissors : VFSemiring M S →+* Classes M S :=
  (ringConGen (VFRelation M S)).lift
    (MvPolynomial.eval₂Hom (Nat.castRingHom (Classes M S)) (fun A => cls (fieldObjectFamily A)))
    (RingCon.ringConGen_le.mpr (fieldWeights_respect (M := M) (S := S)))

theorem realizeScissors_class (A : VFObject M S) :
    realizeScissors (fieldClass M S A) = cls (fieldObjectFamily A) := by
  change MvPolynomial.eval₂ (Nat.castRingHom (Classes M S)) (fun A => cls (fieldObjectFamily A))
    (MvPolynomial.X A) = _
  exact MvPolynomial.eval₂_X _ _ _

end GeneralizedEuler.Section5.MixedTaggedFamily
