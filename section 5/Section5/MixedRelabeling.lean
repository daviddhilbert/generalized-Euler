module

public import Section5.FieldScissors

/-! Definable coordinate equivalences for mixed tuples. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {V W : TCsort → Type}

theorem mixed_reindex_equivalent [Finite (W .vf)] [Finite (W .rv)]
    (p : ∀ s, W s ≃ V s)
    (A : Set (SortedAssignment X V)) (defA : SortedDefinableOver M S.carrier A) :
    MixedDefinablyEquivalent M S A
      {b : SortedAssignment X W | (fun s => b s ∘ (p s).symm) ∈ A} := by
  let B : Set (SortedAssignment X W) := {b | (fun s => b s ∘ (p s).symm) ∈ A}
  let e : A ≃ B :=
    { toFun := fun a => ⟨fun s => a.val s ∘ p s,by
        change (fun s => (a.val s ∘ p s) ∘ (p s).symm) ∈ A
        convert a.property using 1
        funext s i
        exact congrArg (a.val s) ((p s).apply_symm_apply i)⟩
      invFun := fun b => ⟨fun s => b.val s ∘ (p s).symm,b.property⟩
      left_inv := fun a => Subtype.ext (funext fun s => funext fun i =>
        congrArg (a.val s) ((p s).apply_symm_apply i))
      right_inv := fun b => Subtype.ext (funext fun s => funext fun i =>
        congrArg (b.val s) ((p s).symm_apply_apply i)) }
  refine ⟨e,?_⟩
  let T := SumVariables V W
  have hA := defA.pullback_relabel (fun s => (Sum.inl : V s → T s))
  have hVF := SortedDefinableOver.iInter (fun i : W .vf =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T) .vf
      (.inl (p .vf i)) (.inr i))
  have hRV := SortedDefinableOver.iInter (fun i : W .rv =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T) .rv
      (.inl (p .rv i)) (.inr i))
  unfold DefinableRelation
  convert hA.inter (hVF.inter hRV) using 1
  ext w
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  let a : SortedAssignment X V := fun s => w s ∘ Sum.inl
  let b : SortedAssignment X W := fun s => w s ∘ Sum.inr
  change (∃ ha : a ∈ A, (fun s => a s ∘ p s) = b) ↔
    a ∈ A ∧ ((∀ i, a .vf (p .vf i) = b .vf i) ∧ (∀ i, a .rv (p .rv i) = b .rv i))
  constructor
  · rintro ⟨ha,he⟩
    exact ⟨ha,fun i => congrFun (congrFun he .vf) i,fun i => congrFun (congrFun he .rv) i⟩
  · rintro ⟨ha,hf,hr⟩
    refine ⟨ha,?_⟩
    funext s i
    cases s with
    | vf => exact hf i
    | rv => exact hr i

theorem mixed_projection_graph [Finite (W .vf)] [Finite (W .rv)]
    (p : ∀ s, W s → V s) :
    DefinableRelation M S.carrier (fun x y => (fun s => x s ∘ p s) = y) := by
  let T := SumVariables V W
  have vf := SortedDefinableOver.iInter (fun i : W .vf =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T)
      .vf (.inl (p .vf i)) (.inr i))
  have rv := SortedDefinableOver.iInter (fun i : W .rv =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T)
      .rv (.inl (p .rv i)) (.inr i))
  unfold DefinableRelation
  convert vf.inter rv using 1
  ext w
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  let x : SortedAssignment X V := fun s => w s ∘ Sum.inl
  let y : SortedAssignment X W := fun s => w s ∘ Sum.inr
  change (fun s => x s ∘ p s) = y ↔
    (∀ i, x .vf (p .vf i) = y .vf i) ∧ (∀ i, x .rv (p .rv i) = y .rv i)
  constructor
  · intro eq
    exact ⟨fun i => congrFun (congrFun eq .vf) i,fun i => congrFun (congrFun eq .rv) i⟩
  · rintro ⟨hf,hr⟩
    funext s i
    cases s with
    | vf => exact hf i
    | rv => exact hr i

/-- A bijective coordinate projection between definable sets has a
definable graph, even when it drops coordinates fixed by the domain. -/
theorem mixed_projection_equivalent [Finite (W .vf)] [Finite (W .rv)]
    (p : ∀ s, W s → V s)
    (A : Set (SortedAssignment X V)) (B : Set (SortedAssignment X W))
    (defA : SortedDefinableOver M S.carrier A)
    (bij : Set.BijOn (fun x : SortedAssignment X V => fun s => x s ∘ p s) A B) :
    MixedDefinablyEquivalent M S A B := by
  let f (x : A) : B := ⟨fun s => x.val s ∘ p s,bij.mapsTo x.property⟩
  have bf : Function.Bijective f := by
    constructor
    · intro x y eq
      exact Subtype.ext (bij.injOn x.property y.property (congrArg Subtype.val eq))
    · intro y
      obtain ⟨x,hx,eq⟩ := bij.surjOn y.property
      exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  refine ⟨Equiv.ofBijective f bf,((mixed_projection_graph p).inter_left defA).congr ?_⟩
  intro a b
  exact ⟨fun ⟨e,h⟩ => ⟨h,e⟩,fun ⟨h,e⟩ => ⟨e,h⟩⟩

end GeneralizedEuler.Section5
