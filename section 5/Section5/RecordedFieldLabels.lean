module

public import Section5.HeadContractionFamilies
public import Section5.MixedGraphIsomorphisms
public import Section5.MixedRelabeling

/-! Adjoin a definable RV label without moving any field coordinate
or losing any old RV tag. The annotation preserves finite fibers. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ} {J : Type}

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S n k)
  (code : SortedAssignment (CanonicalSort O) (MixedVariables n A.tags) → J → RV0 O)

local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables n A.tags
local notation "V" => MixedVariables n (J ⊕ A.tags)
local notation "Q" => RVVariables J

@[expose] def recordedForget : SortedAssignment Z V → SortedAssignment Z U :=
  fun x s => match s with
  | .vf => x .vf
  | .rv => x .rv ∘ Sum.inr

@[expose] def recordedAssignment (a : SortedAssignment Z U) : SortedAssignment Z V
  | .vf => a .vf
  | .rv => Sum.elim (code a) (a .rv)

theorem recordedForget_recorded (a : SortedAssignment Z U) :
    A.recordedForget (A.recordedAssignment code a) = a := by
  funext s i
  cases s <;> rfl

theorem recordedAssignment_of_agree (a : SortedAssignment Z V)
    (eq : code (A.recordedForget a) = a .rv ∘ Sum.inl) :
    A.recordedAssignment code (A.recordedForget a) = a := by
  funext s i
  cases s with
  | vf => rfl
  | rv =>
    rcases i with i | i
    · exact congrFun eq i
    · rfl

@[expose] def recordedCarrier : Set (PreparationPoint O (Fin n) (J ⊕ A.tags)) :=
  {p | ∃ a : SortedAssignment Z U, mixedTuple a = (p.1,p.2 ∘ Sum.inr) ∧
     mixedTuple a ∈ A.carrier ∧ code a = p.2 ∘ Sum.inl}

theorem recordedCarrier_mem (a : SortedAssignment Z V) :
    mixedTuple a ∈ A.recordedCarrier code ↔
      mixedTuple (A.recordedForget a) ∈ A.carrier ∧ code (A.recordedForget a) = a .rv ∘ Sum.inl := by
  constructor
  · rintro ⟨u,e,h,c⟩
    have eq : u = A.recordedForget a := mixedTuple_injective e
    exact eq ▸ ⟨h,c⟩
  · rintro ⟨h,c⟩
    exact ⟨_,rfl,h,c⟩

variable [Finite J] (graph : DefinableRelation M S.carrier (fun
    (a : SortedAssignment (CanonicalSort O) (MixedVariables n A.tags))
    (r : SortedAssignment (CanonicalSort O) (RVVariables J)) => code a = r .rv))

@[expose] def withRecordedLabels : RetainedFieldFamily M S n k where
  tags := J ⊕ A.tags
  finiteTags := by
    let : Finite A.tags := A.finiteTags
    infer_instance
  select := Sum.inr ∘ A.select
  carrier := A.recordedCarrier code
  definable := by
    let ren : (s : TCsort) → U s → V s
      | .vf => id
      | .rv => Sum.inr
    let aux : (s : TCsort) → Q s → V s
      | .vf => PEmpty.elim
      | .rv => Sum.inl
    unfold DefinableRelation at graph
    convert (A.definable.pullback_relabel ren).inter
      (graph.pullback_relabel (fun s => Sum.elim (ren s) (aux s))) using 1
    ext a
    have eq : (fun s => a s ∘ ren s) = A.recordedForget a := by
      funext s i
      cases s <;> rfl
    simp only [Set.mem_inter_iff]
    change mixedTuple a ∈ A.recordedCarrier code ↔
      mixedTuple (fun s => a s ∘ ren s) ∈ A.carrier ∧ code (fun s => a s ∘ ren s) = a .rv ∘ Sum.inl
    rw [eq]
    exact A.recordedCarrier_mem code a
  finiteFibers b v := by
    apply (A.finiteFibers b v).of_injOn (f := fun t => t ∘ Sum.inr)
    · intro t ht
      obtain ⟨a,e,ha,_⟩ := ht.1
      exact ⟨e ▸ ha,ht.2⟩
    · intro t ht u hu eq
      obtain ⟨a,ea,_,ta⟩ := ht.1
      obtain ⟨w,ew,_,tu⟩ := hu.1
      have ae : a = w := mixedTuple_injective (ea.trans ((congrArg (b,·) eq).trans ew.symm))
      funext j
      rcases j with i | i
      · exact congrFun (ta.symm.trans (ae ▸ tu)) i
      · exact congrFun eq i

theorem withRecordedLabels_iso :
    ∃ f : MixedGraphIso M S
      {a : SortedAssignment Z U | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z V | mixedTuple b ∈ (A.withRecordedLabels code graph).carrier},
      (∀ a, (f.equiv a).val .vf = a.val .vf) ∧
      (∀ a, (f.equiv a).val .rv ∘ Sum.inr = a.val .rv) := by
  let B := A.withRecordedLabels code graph
  let e : {a : SortedAssignment Z U | mixedTuple a ∈ A.carrier} ≃
      {b : SortedAssignment Z V | mixedTuple b ∈ B.carrier} :=
    { toFun := fun a => ⟨A.recordedAssignment code a.val,⟨a.val,rfl,a.property,rfl⟩⟩
      invFun := fun b => ⟨A.recordedForget b.val,((A.recordedCarrier_mem code b.val).1 b.property).1⟩
      left_inv := fun a => Subtype.ext (A.recordedForget_recorded code a.val)
      right_inv := fun b => Subtype.ext (A.recordedAssignment_of_agree code b.val
        ((A.recordedCarrier_mem code b.val).1 b.property).2) }
  let ren : (s : TCsort) → U s → V s
    | .vf => id
    | .rv => Sum.inr
  let : Finite A.tags := A.finiteTags
  have projection : DefinableRelation M S.carrier (fun (b : SortedAssignment Z V) (a : SortedAssignment Z U) =>
      A.recordedForget b = a) := by
    apply (mixed_projection_graph (M := M) (S := S) ren).congr
    intro b a
    have eq : (fun s => b s ∘ ren s) = A.recordedForget b := by
      funext s i
      cases s <;> rfl
    rw [eq]
  refine ⟨⟨e,?_⟩,fun _ => rfl,fun _ => rfl⟩
  apply (projection.inter_left B.definable).transpose.congr
  intro a b
  constructor
  · rintro ⟨eq,h⟩
    have hb := (A.recordedCarrier_mem code b).1 h
    refine ⟨eq ▸ hb.1,?_⟩
    exact (congrArg (A.recordedAssignment code) eq).symm.trans (A.recordedAssignment_of_agree code b hb.2)
  · rintro ⟨h,rfl⟩
    exact ⟨A.recordedForget_recorded code a, (e ⟨a,h⟩).property⟩

end RetainedFieldFamily

end GeneralizedEuler.Section5
