module

public import Section5.RetainedFamilyIsoTransport

/-! A definable unary map can be applied in each tag fiber. When it
is injective there, its image keeps the selected labels and remains
a retained-field family. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem tagged_unary_image_iso
    (A : RetainedFieldFamily 𝓜 S 1 k)
    (f : K → (A.tags → RV0 O) → K)
    (graph : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 A.tags)) (b : fieldAssignment 1 Z) =>
        f (a .vf 0) (a .rv) = b .vf 0))
    (inj : ∀ t : A.tags → RV0 O, Set.InjOn (fun x => f x t) {x | ((fun _ => x),t) ∈ A.carrier}) :
    ∃ e : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables 1 A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables 1 A.tags) |
        ∃ x, ((fun _ => x),b .rv) ∈ A.carrier ∧ f x (b .rv) = b .vf 0},
      ∀ a, (e.equiv a).val .rv = a.val .rv := by
  let U := MixedVariables 1 A.tags
  let P := {a : SortedAssignment Z U | mixedTuple a ∈ A.carrier}
  let map (a : P) : SortedAssignment Z U :=
    mixedAssignment (fun _ => f (a.val .vf 0) (a.val .rv)) (a.val .rv)
  have only (a : SortedAssignment Z U) : (fun _ : Fin 1 => a .vf 0) = a .vf := by
    funext i
    rw [Fin.eq_zero i]
  have injection : Function.Injective map := by
    intro a b eq
    have tags : a.val .rv = b.val .rv := congrFun eq .rv
    have field : f (a.val .vf 0) (a.val .rv) = f (b.val .vf 0) (b.val .rv) := congrFun (congrFun eq .vf) 0
    rw [← tags] at field
    have ha : ((fun _ : Fin 1 => a.val .vf 0),a.val .rv) ∈ A.carrier := by rw [only]; exact a.property
    have hb : ((fun _ : Fin 1 => b.val .vf 0),a.val .rv) ∈ A.carrier := by rw [only,tags]; exact b.property
    have head := inj (a.val .rv) ha hb field
    exact Subtype.ext (mixedTuple_injective (Prod.ext
      ((only a.val).symm.trans ((congrArg (fun x _ => x) head).trans (only b.val))) tags))
  let W := SumVariables U U
  let vars : (s : TCsort) → SumVariables U (MixedVariables 1 Empty) s → W s
    | .vf => Sum.map id id
    | .rv => Sum.elim Sum.inl Empty.elim
  have source := A.definable.pullback_relabel (fun s => (Sum.inl : U s → W s))
  let : Finite A.tags := A.finiteTags
  have keep := SortedDefinableOver.iInter (fun i : A.tags =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := W) .rv (.inl i) (.inr i))
  have graph' := graph
  unfold DefinableRelation at graph'
  have defMap : DefinableRelation 𝓜 S.carrier (fun a b => ∃ h : a ∈ P, map ⟨a,h⟩ = b) := by
    unfold DefinableRelation
    convert source.inter ((graph'.pullback_relabel vars).inter keep) using 1
    ext w
    simp only [Set.mem_iInter,Set.mem_inter_iff]
    let a : SortedAssignment Z U := fun s => w s ∘ Sum.inl
    let b : SortedAssignment Z U := fun s => w s ∘ Sum.inr
    change (∃ h : a ∈ P, map ⟨a,h⟩ = b) ↔
      a ∈ P ∧ f (a .vf 0) (a .rv) = b .vf 0 ∧ ∀ i, a .rv i = b .rv i
    constructor
    · rintro ⟨h,e⟩
      exact ⟨h,congrFun (congrFun e .vf) 0,fun i => congrFun (congrFun e .rv) i⟩
    · rintro ⟨h,ev,et⟩
      refine ⟨h,?_⟩
      funext s i
      cases s
      · rw [Fin.eq_zero i]
        exact ev
      · exact et i
  let e := MixedGraphIso.toRange map injection defMap
  let R := Set.range map
  let B := {b : SortedAssignment Z U | ∃ x, ((fun _ => x),b .rv) ∈ A.carrier ∧ f x (b .rv) = b .vf 0}
  have asSet : B = R := by
    ext b
    change (∃ x, ((fun _ => x),b .rv) ∈ A.carrier ∧ f x (b .rv) = b .vf 0) ↔ b ∈ R
    constructor
    · rintro ⟨x,h,eq⟩
      refine ⟨⟨mixedAssignment (fun _ => x) (b .rv),h⟩,?_⟩
      funext s i
      cases s
      · rw [Fin.eq_zero i]
        exact eq
      · rfl
    · rintro ⟨a,eq⟩
      have tag : a.val .rv = b .rv := congrFun eq .rv
      refine ⟨a.val .vf 0,?_,?_⟩
      · rw [only,← tag]
        exact a.property
      · rw [← tag]
        exact congrFun (congrFun eq .vf) 0
  let e' : MixedGraphIso 𝓜 S P B := asSet.symm ▸ e
  have eval (a : P) : (e'.equiv a).val = map a := by
    have h (D : Set (SortedAssignment Z U)) (eq : R = D) :
        ((eq ▸ e : MixedGraphIso 𝓜 S P D).equiv a).val = map a := by cases eq; rfl
    exact h _ asSet.symm
  exact ⟨e',fun a => congrFun (eval a) .rv⟩

end GeneralizedEuler.Section5
