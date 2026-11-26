module

public import Section5.ObjectLiftRestrictions
public import Section5.FieldLiftPartitions

/-! Glue lifts of object isomorphisms along finite partitions of their
RV tags. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.ObjectLift

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}
  {U V : RVObject M S k}

/-- The graphs on the restricted objects are over the full ambient
tuple variables, so a finite union defines the glued graph. -/
theorem definable_lift_of_tag_partition {I : Type*} [Finite I]
    (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
    (A : I → Set (Fin U.arity → X .rv))
    (sub : ∀ i, A i ⊆ U.carrier) (defA : ∀ i, isRVSet M S (A i))
    (disj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (cover : ∀ a : U.carrier, ∃ i, a.val ∈ A i)
    (pieces : ∀ i, HasDefinableObjectLift (sourceRestriction (sub i) (defA i))
      (targetRestriction e eDef (defA i)) (restrictIso e eDef (sub i) (defA i))) :
    HasDefinableObjectLift U V e := by
  classical
  choose f hTag hDef using pieces
  let D (i : I) := (fun x : carrier U => (tag U x).val) ⁻¹' A i
  let C (i : I) := (fun y : carrier V => (tag V y).val) ⁻¹' tagImage e (A i)
  have dDisj : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j ne
    exact Set.disjoint_left.2 fun _ hi hj => Set.disjoint_left.1 (disj ne) hi hj
  have cDisj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j ne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨u,hu,eu⟩ ⟨v,hv,ev⟩
    have he : u = v := e.injective (Subtype.ext (eu.trans ev.symm))
    exact Set.disjoint_left.1 (disj ne) hu (he.symm ▸ hv)
  have dCover (x : carrier U) : ∃ i, x ∈ D i := cover (tag U x)
  have cCover (y : carrier V) : ∃ i, y ∈ C i := by
    obtain ⟨i,hi⟩ := cover (e.symm (tag V y))
    exact ⟨i,e.symm (tag V y),hi,congrArg Subtype.val (e.apply_symm_apply (tag V y))⟩
  let DEquiv := equivOfSetPartition D dDisj dCover
  let CEquiv := equivOfSetPartition C cDisj cCover
  let d (i : I) := restrictCarrierEquiv (sub i) (defA i)
  let c (i : I) := restrictCarrierEquiv (tagImage_subset e (A i)) (tagImage_definable e eDef (defA i))
  let g (i : I) : D i ≃ C i := (d i).symm.trans ((f i).trans (c i))
  let F := DEquiv.symm.trans ((Equiv.sigmaCongrRight g).trans CEquiv)
  have agree (i : I) (x : D i) : F x.val = (g i x).val := by
    have eq := DEquiv.symm_apply_apply ⟨i,x⟩
    have eqD : DEquiv ⟨i,x⟩ = x.val := equivOfSetPartition_apply D dDisj dCover ⟨i,x⟩
    rw [eqD] at eq
    simp only [F, Equiv.trans_apply, eq]
    exact equivOfSetPartition_apply C cDisj cCover ⟨i,g i x⟩
  have tagg (i : I) (x : D i) : tag V (g i x).val = e (tag U x.val) := by
    let u := (d i).symm x
    let v := f i u
    have source : (tag (sourceRestriction (sub i) (defA i)) u).val = (tag U x.val).val := by
      symm
      have he := restrictCarrierEquiv_tag_val (sub i) (defA i) u
      change (tag U (d i u).val).val = _ at he
      rw [(d i).apply_symm_apply] at he
      exact he
    apply Subtype.ext
    change (tag V (c i v).val).val = _
    rw [show (tag V (c i v).val).val = (tag (targetRestriction e eDef (defA i)) v).val from
      restrictCarrierEquiv_tag_val (tagImage_subset e (A i)) (tagImage_definable e eDef (defA i)) v]
    rw [hTag i u,restrictIso_apply]
    exact congrArg (fun a : U.carrier => (e a).val) (Subtype.ext source)
  refine ⟨F,?_,?_⟩
  · intro x
    obtain ⟨i,hi⟩ := dCover x
    exact (congrArg (tag V) (agree i ⟨x,hi⟩)).trans (tagg i ⟨x,hi⟩)
  · let T := SumVariables (Vars U) (Vars V)
    let G (i : I) : Set (SortedAssignment X T) :=
      {w | ∃ hw : (fun s => w s ∘ Sum.inl) ∈ carrier (sourceRestriction (sub i) (defA i)),
        (f i ⟨fun s => w s ∘ Sum.inl,hw⟩).val = (fun s => w s ∘ Sum.inr)}
    have gDef (i : I) : SortedDefinableOver M S.carrier (G i) := hDef i
    unfold DefinableRelation
    convert SortedDefinableOver.iUnion gDef using 1
    ext w
    let x : SortedAssignment X (Vars U) := fun s => w s ∘ Sum.inl
    let y : SortedAssignment X (Vars V) := fun s => w s ∘ Sum.inr
    change (∃ hx : x ∈ carrier U, (F ⟨x,hx⟩).val = y) ↔ w ∈ ⋃ i, G i
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨hx,he⟩
      obtain ⟨i,hi⟩ := dCover ⟨x,hx⟩
      let x' : D i := ⟨⟨x,hx⟩,hi⟩
      let a := (d i).symm x'
      have hField : a.val = x := restrictCarrierEquiv_symm_val (sub i) (defA i) x'
      have hVal : (g i x').val.val = (f i a).val :=
        restrictCarrierEquiv_val (tagImage_subset e (A i)) (tagImage_definable e eDef (defA i)) (f i a)
      have he' := hVal.symm.trans ((congrArg Subtype.val (agree i x')).symm.trans he)
      have xMem : x ∈ carrier (sourceRestriction (sub i) (defA i)) := hField ▸ a.property
      have eX : a = ⟨x,xMem⟩ := Subtype.ext hField
      refine ⟨i,?_⟩
      change ∃ hx : x ∈ carrier (sourceRestriction (sub i) (defA i)), (f i ⟨x,hx⟩).val = y
      exact ⟨xMem,by rw [← eX]; exact he'⟩
    · rintro ⟨i,hx,hy⟩
      let a : carrier (sourceRestriction (sub i) (defA i)) := ⟨x,hx⟩
      let x' := d i a
      have hx' : x'.val.val = x := restrictCarrierEquiv_val (sub i) (defA i) a
      have ha : (d i).symm x' = a := (d i).symm_apply_apply a
      have hVal : (g i x').val.val = (f i a).val := by
        change (c i (f i ((d i).symm x'))).val.val = _
        rw [ha]
        exact restrictCarrierEquiv_val (tagImage_subset e (A i))
          (tagImage_definable e eDef (defA i)) (f i a)
      have eX : x'.val = ⟨x,hx' ▸ x'.val.property⟩ := Subtype.ext hx'
      exact ⟨hx' ▸ x'.val.property,by
        rw [← eX,agree i x',hVal]
        exact hy⟩

end GeneralizedEuler.Section5.ObjectLift
