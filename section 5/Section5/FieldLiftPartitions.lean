module

public import Section5.RestrictedFieldLifts

/-! Reassemble the field lifts along a finite definable partition of the
source labels and its transported partition on the target. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

private def partitionEquiv {I Z : Type*} (A : I → Set Z)
    (disj : Pairwise (fun i j => Disjoint (A i) (A j))) (cover : ∀ x, ∃ i, x ∈ A i) :
    (Σ i, A i) ≃ Z := by
  classical
  refine Equiv.ofBijective (fun x => x.2.val) ⟨?_,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    change x.val = y.val at he
    obtain rfl : i = j := by
      by_contra hn
      exact Set.disjoint_left.1 (disj hn) x.property (he.symm ▸ y.property)
    exact congrArg (Sigma.mk i) (Subtype.ext he)
  · intro x
    obtain ⟨i,hi⟩ := cover x
    exact ⟨⟨i,⟨x,hi⟩⟩,rfl⟩

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {U V : Set (labelAssignment n X)}

theorem definable_lift_of_label_partition {I : Type*} [Finite I]
    (e : U ≃ V) (A : I → Set U)
    (disj : Pairwise (fun i j => Disjoint (A i) (A j))) (cover : ∀ u, ∃ i, u ∈ A i)
    (pieces : ∀ i, HasDefinableFieldLift S (restrictedLabelEquiv e (A i))) :
    HasDefinableFieldLift S e := by
  classical
  choose f hF fDef using fun i => relative_lift_of_restricted e (A i) (pieces i)
  let p := liftedLabel (M := M) U
  let q := liftedLabel (M := M) V
  let D (i : I) := p ⁻¹' A i
  let C (i : I) := q ⁻¹' (e '' A i)
  have dDisj : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j ne
    exact (Set.disjoint_left.2 fun _ h₁ h₂ => Set.disjoint_left.1 (disj ne) h₁ h₂)
  have cDisj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j ne
    refine Set.disjoint_left.2 ?_
    rintro y ⟨u,hu,eu⟩ ⟨v,hv,ev⟩
    have he : u = v := e.injective (eu.trans ev.symm)
    exact Set.disjoint_left.1 (disj ne) hu (he.symm ▸ hv)
  have dCover (x : fieldLiftDomain M U) : ∃ i, x ∈ D i := cover (p x)
  have cCover (y : fieldLiftDomain M V) : ∃ i, y ∈ C i := by
    obtain ⟨i,hi⟩ := cover (e.symm (q y))
    exact ⟨i,e.symm (q y),hi,e.apply_symm_apply (q y)⟩
  let P := partitionEquiv D dDisj dCover
  let Q := partitionEquiv C cDisj cCover
  let lift := P.symm.trans ((Equiv.sigmaCongrRight f).trans Q)
  have agrees (i : I) (x : D i) : lift x.val = (f i x).val := by
    have he := P.symm_apply_apply ⟨i,x⟩
    change P.symm x.val = ⟨i,x⟩ at he
    simp only [lift, Equiv.trans_apply, he]
    rfl
  refine ⟨lift,?_,?_⟩
  · intro x
    obtain ⟨i,hi⟩ := dCover x
    exact (congrArg q (agrees i ⟨x,hi⟩)).trans (hF i ⟨x,hi⟩)
  · let W := MixedVariables n Empty
    let R (i : I) : Set (SortedAssignment X (SumVariables W W)) :=
      {w | ∃ ha : (fun s => w s ∘ Sum.inl) ∈ fieldLiftDomain M U,
        ∃ hi : p ⟨fun s => w s ∘ Sum.inl,ha⟩ ∈ A i,
          (f i ⟨⟨fun s => w s ∘ Sum.inl,ha⟩,hi⟩).val.val = (fun s => w s ∘ Sum.inr)}
    have rDef (i : I) : SortedDefinableOver M S.carrier (R i) := fDef i
    unfold DefinableRelation
    convert SortedDefinableOver.iUnion rDef using 1
    ext w
    let x : fieldAssignment n X := fun s => w s ∘ Sum.inl
    let y : fieldAssignment n X := fun s => w s ∘ Sum.inr
    change (∃ ha : x ∈ fieldLiftDomain M U, (lift ⟨x,ha⟩).val = y) ↔ w ∈ ⋃ i, R i
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨ha,he⟩
      obtain ⟨i,hi⟩ := dCover ⟨x,ha⟩
      exact ⟨i,ha,hi,(congrArg Subtype.val (agrees i ⟨⟨x,ha⟩,hi⟩)).symm.trans he⟩
    · rintro ⟨i,ha,hi,he⟩
      exact ⟨ha,(congrArg Subtype.val (agrees i ⟨⟨x,ha⟩,hi⟩)).trans he⟩

end GeneralizedEuler.Section5
