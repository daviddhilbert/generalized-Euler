module

public import Section5.FieldScissors
public import Section5.SimultaneousLabelRefinement
public import Section5.ZeroBlowupObject

/-! A mixed isomorphism that contracts in both directions induces a
fixed-base definable bijection of its RV labels. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {V W : TCsort → Type} [Finite (V .vf)] [Finite (V .rv)]
  [Finite (W .vf)] [Finite (W .rv)] {I J : Type}
  {A : Set (SortedAssignment X V)} {B : Set (SortedAssignment X W)}

/-- The induced map is defined by existentially quantifying the mixed
representatives in the two label graphs and the original bijection. -/
theorem definable_label_iso_of_mutually_contractible
    (e : A ≃ B)
    (eDef : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (e ⟨a,ha⟩).val = b))
    (p : SortedAssignment X V → I → X .rv) (q : SortedAssignment X W → J → X .rv)
    (pDef : DefinableRelation M S.carrier
      (fun a (b : SortedAssignment X (RVVariables I)) => p a = b .rv))
    (qDef : DefinableRelation M S.carrier
      (fun b (c : SortedAssignment X (RVVariables J)) => q b = c .rv))
    (forward : Contractible (p ∘ Subtype.val) (q ∘ Subtype.val) e)
    (backward : Contractible (q ∘ Subtype.val) (p ∘ Subtype.val) e.symm) :
    ∃ f : (p '' A) ≃ (q '' B),
      SortedDefinableOver M S.carrier (rvGraph fun x => (f x).val) ∧
      ∀ x : A, (f ⟨p x.val,⟨x.val,x.property,rfl⟩⟩).val = q (e x).val := by
  have rng (R : TCsort → Type) (D : Set (SortedAssignment X R)) {H : Type}
      (f : SortedAssignment X R → H → X .rv) :
      Set.range (f ∘ (Subtype.val : D → SortedAssignment X R)) = f '' D := by
    ext a
    exact ⟨fun ⟨x,h⟩ => ⟨x.val,x.property,h⟩,fun ⟨x,h,hx⟩ => ⟨⟨x,h⟩,hx⟩⟩
  obtain ⟨g,hg⟩ := equiv_of_mutual_contraction e (p ∘ Subtype.val) (q ∘ Subtype.val) forward backward
  let f := (Set.equivOfEq (rng V A p).symm).trans (g.trans (Set.equivOfEq (rng W B q)))
  have hf (x : A) : (f ⟨p x.val,⟨x.val,x.property,rfl⟩⟩).val = q (e x).val := hg x
  refine ⟨f,?_,hf⟩
  have raw := (pDef.transpose.comp eDef).comp qDef
  apply rvGraph_of_relation (raw.congr ?_)
  intro x y
  constructor
  · rintro ⟨b,⟨a,hp,ha,he⟩,hq⟩
    let t : p '' A := ⟨p a,⟨a,ha,rfl⟩⟩
    have hval : (f t).val = q (e ⟨a,ha⟩).val := hf ⟨a,ha⟩
    exact ⟨t,hp,hval.trans ((congrArg q he).trans hq)⟩
  · rintro ⟨t,ht,hy⟩
    obtain ⟨a,ha,hp⟩ := t.property
    have ht' : (⟨p a,⟨a,ha,rfl⟩⟩ : p '' A) = t := Subtype.ext hp
    have hval := hf (⟨a,ha⟩ : A)
    change (f ⟨p a,⟨a,ha,rfl⟩⟩).val = _ at hval
    rw [ht'] at hval
    exact ⟨(e ⟨a,ha⟩).val,⟨a,hp.trans ht,ha,rfl⟩,hval.symm.trans hy⟩

theorem definable_iso_of_mutually_contractible
    (e : A ≃ B)
    (eDef : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (e ⟨a,ha⟩).val = b))
    (p : SortedAssignment X V → I → X .rv) (q : SortedAssignment X W → J → X .rv)
    (pDef : DefinableRelation M S.carrier
      (fun a (b : SortedAssignment X (RVVariables I)) => p a = b .rv))
    (qDef : DefinableRelation M S.carrier
      (fun b (c : SortedAssignment X (RVVariables J)) => q b = c .rv))
    (forward : Contractible (p ∘ Subtype.val) (q ∘ Subtype.val) e)
    (backward : Contractible (q ∘ Subtype.val) (p ∘ Subtype.val) e.symm) :
    RVDefinablyEquivalent M S.carrier (p '' A) (q '' B) := by
  obtain ⟨f,hf,_⟩ := definable_label_iso_of_mutually_contractible e eDef p q pDef qDef forward backward
  exact ⟨f,hf⟩

end GeneralizedEuler.Section5
