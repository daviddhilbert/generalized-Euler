module

public import Section5.InjectiveObjectLifts
import all Section4.FiniteScissors

/-! Restrict an object isomorphism and its lift to a definable subset of
the source RV coordinates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.ObjectLift

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}
  {U V : RVObject M S k}

@[expose] def tagPreimage (e : U.carrier ≃ V.carrier) (B : Set (Fin V.arity → X .rv)) :
    Set (Fin U.arity → X .rv) := {a | ∃ ha : a ∈ U.carrier, (e ⟨a,ha⟩).val ∈ B}

theorem tagPreimage_definable (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
    {B : Set (Fin V.arity → X .rv)} (bDef : isRVSet M S B) :
    isRVSet M S (tagPreimage e B) := by
  have h := (relation_of_rvGraph eDef).transpose.image bDef
  unfold isRVSet
  convert h using 1
  ext a
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨rvTupleAssignment (e ⟨a .rv,ha⟩).val,hb,⟨a .rv,ha⟩,rfl,rfl⟩
  · rintro ⟨b,hb,⟨a',ha⟩,he,he'⟩
    change a' = a .rv at he
    subst a'
    exact ⟨ha,he'.symm ▸ hb⟩

@[expose] def tagImage (e : U.carrier ≃ V.carrier) (A : Set (Fin U.arity → X .rv)) :
    Set (Fin V.arity → X .rv) := {b | ∃ a : U.carrier, a.val ∈ A ∧ (e a).val = b}

theorem tagImage_subset (e : U.carrier ≃ V.carrier) (A : Set (Fin U.arity → X .rv)) :
    tagImage e A ⊆ V.carrier := by
  rintro _ ⟨a,_,rfl⟩
  exact (e a).property

theorem tagImage_definable (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
    {A : Set (Fin U.arity → X .rv)} (aDef : isRVSet M S A) :
    isRVSet M S (tagImage e A) := by
  have h := (relation_of_rvGraph eDef).image aDef
  unfold isRVSet
  convert h using 1
  ext b
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨rvTupleAssignment a.val,ha,a,rfl,he⟩
  · rintro ⟨a,ha,a',he,he'⟩
    exact ⟨a',he.symm ▸ ha,he'⟩

/-- The Section 4 restriction with its coordinates available for the
mixed graph of the field lift. -/
@[expose] def restrictTags (U : RVObject M S k) {A : Set (Fin U.arity → X .rv)}
    (sub : A ⊆ U.carrier) (hA : isRVSet M S A) : RVObject M S k where
  arity := U.arity
  carrier := A
  definable := hA
  label x := U.label ⟨x.val,sub x.property⟩
  graph := by exact (U.restrict sub hA).graph
  nonzero x := U.nonzero ⟨x.val,sub x.property⟩
  finiteFibers y := by exact (U.restrict sub hA).finiteFibers y

variable (e : U.carrier ≃ V.carrier)
  (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
  {A : Set (Fin U.arity → X .rv)} (sub : A ⊆ U.carrier) (defA : isRVSet M S A)

abbrev sourceRestriction := restrictTags U sub defA
abbrev targetRestriction := restrictTags V (tagImage_subset e A) (tagImage_definable e eDef defA)

def restrictIso : (sourceRestriction sub defA).carrier ≃ (targetRestriction e eDef defA).carrier := by
  let map (a : A) : tagImage e A :=
    ⟨(e ⟨a.val,sub a.property⟩).val,⟨⟨a.val,sub a.property⟩,a.property,rfl⟩⟩
  refine Equiv.ofBijective map ⟨?_,?_⟩
  · intro a b he
    have h : (e ⟨a.val,sub a.property⟩).val = (e ⟨b.val,sub b.property⟩).val :=
      congrArg (fun t : tagImage e A => t.val) he
    have h₁ := e.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (fun z : U.carrier => z.val) h₁)
  · rintro ⟨b,a,ha,rfl⟩
    exact ⟨⟨a.val,ha⟩,Subtype.ext rfl⟩

theorem restrictIso_apply (a : (sourceRestriction sub defA).carrier) :
    (restrictIso e eDef sub defA a).val = (e ⟨a.val,sub a.property⟩).val := by
  rfl

theorem restrictIso_definable :
    SortedDefinableOver M S.carrier (rvGraph (fun a => (restrictIso e eDef sub defA a).val)) := by
  let T := RVVariables (Fin U.arity ⊕ Fin V.arity)
  let g (a : A) : Fin V.arity → X .rv := (restrictIso e eDef sub defA a).val
  let D : Set (SortedAssignment X T) := {x | x .rv ∘ Sum.inl ∈ A}
  change SortedDefinableOver M S.carrier (rvGraph g)
  have defL : SortedDefinableOver M S.carrier D := isRVSet_precomp Sum.inl defA
  have eq : rvGraph g = D ∩ rvGraph (fun a => (e a).val) := by
    ext x
    change (∃ a : A, a.val = x .rv ∘ Sum.inl ∧ g a = x .rv ∘ Sum.inr) ↔
      x .rv ∘ Sum.inl ∈ A ∧ (∃ a : U.carrier, a.val = x .rv ∘ Sum.inl ∧
        (e a).val = x .rv ∘ Sum.inr)
    constructor
    · rintro ⟨a,ha,hb⟩
      exact ⟨ha ▸ a.property,⟨a.val,sub a.property⟩,ha,(restrictIso_apply e eDef sub defA a).symm.trans hb⟩
    · rintro ⟨hx,a,ha,hb⟩
      let b : A := ⟨a.val,ha.symm ▸ hx⟩
      exact ⟨b,ha,(restrictIso_apply e eDef sub defA b).trans hb⟩
  rw [eq]
  exact defL.inter eDef

/-- Restricting the RV tags cuts out the corresponding part of the
object lift, preserving the actual field and RV tuple. -/
def restrictCarrierEquiv :
    (carrier (sourceRestriction sub defA)) ≃ {x : carrier U // (tag U x).val ∈ A} where
  toFun x := by
    let a := tag (sourceRestriction sub defA) x
    have hx : x.val ∈ carrier U :=
      ⟨⟨a.val,sub a.property⟩,tag_val _ x,tag_label _ x⟩
    refine ⟨⟨x.val,hx⟩,?_⟩
    have he : tag U ⟨x.val,hx⟩ = ⟨a.val,sub a.property⟩ :=
      tag_of_val_eq U _ _ (tag_val _ x)
    exact he.symm ▸ a.property
  invFun x :=
    ⟨x.val.val,⟨⟨(tag U x.val).val,x.property⟩,tag_val U x.val,tag_label U x.val⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem restrictCarrierEquiv_val (x : carrier (sourceRestriction sub defA)) :
    ((restrictCarrierEquiv sub defA x).val).val = x.val := by
  rfl

theorem restrictCarrierEquiv_symm_val
    (x : {x : carrier U // (tag U x).val ∈ A}) :
    ((restrictCarrierEquiv sub defA).symm x).val = x.val.val := by
  rfl

theorem restrictCarrierEquiv_tag_val (x : carrier (sourceRestriction sub defA)) :
    (tag U ((restrictCarrierEquiv sub defA x).val)).val =
      (tag (sourceRestriction sub defA) x).val := by
  rw [tag_val,tag_val,restrictCarrierEquiv_val]

end GeneralizedEuler.Section5.ObjectLift
