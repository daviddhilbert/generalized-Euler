module

public import Section5.DefinableRelativeTranslations
public import Section5.HeadContractionFamilies

/-! Translate the first field coordinate by a definable function
of the remaining tuple and the RV tags. A finite center range in
each remaining field fiber preserves the retained fiber bound. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k)
  (c : (Fin n → K) → (A.tags → RV0 O) → K)

@[expose] def translateHeadAssignment (a : SortedAssignment Z (MixedVariables (n+1) A.tags)) :
    SortedAssignment Z (MixedVariables (n+1) A.tags)
  | .vf => Fin.cons (a .vf 0 - c (a .vf ∘ Fin.succ) (a .rv)) (a .vf ∘ Fin.succ)
  | .rv => a .rv

theorem translateHeadAssignment_injective : Function.Injective (A.translateHeadAssignment O hO power S c) := by
  intro x y eq
  have tail : x .vf ∘ Fin.succ = y .vf ∘ Fin.succ := by
    funext i
    exact congrFun (congrFun eq .vf) i.succ
  have tags : x .rv = y .rv := congrFun eq .rv
  have first := congrFun (congrFun eq .vf) 0
  change x .vf 0 - c (x .vf ∘ Fin.succ) (x .rv) = y .vf 0 - c (y .vf ∘ Fin.succ) (y .rv) at first
  rw [tail,tags,sub_left_inj] at first
  funext s i
  cases s
  · exact Fin.cases first (fun j => congrFun tail j) i
  · exact congrFun tags i

variable
  (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
  (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

include F minusOne hm hF in
theorem translateHeadAssignment_graph
    (defC : DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment Z (MixedVariables n A.tags))
      (b : fieldAssignment 1 Z) => c (a .vf) (a .rv) = b .vf 0)) :
    DefinableRelation 𝓜 S.carrier (fun a b =>
      ∃ _ : mixedTuple a ∈ A.carrier, A.translateHeadAssignment O hO power S c a = b) := by
  let U := MixedVariables (n+1) A.tags
  let V := MixedVariables 1 Empty
  let W := SumVariables U U
  let T := SumVariables W V
  let data : (s : TCsort) → SumVariables (MixedVariables n A.tags) V s → T s
    | .vf => Sum.elim (Sum.inl ∘ Sum.inl ∘ Fin.succ) Sum.inr
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl) Empty.elim
  let left : (s : TCsort) → U s → T s := fun _ => Sum.inl ∘ Sum.inl
  let out : SortedTerm L E (WithBase S.carrier T) .vf := .var (.inr (.inl (.inl 0)))
  let center : SortedTerm L E (WithBase S.carrier T) .vf := .var (.inr (.inr 0))
  have source := A.definable.pullback_relabel left
  have field := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := T)
      .vf (.inl (.inl i.succ)) (.inl (.inr i.succ)))
  let : Finite A.tags := A.finiteTags
  have tags := SortedDefinableOver.iInter (fun i : A.tags =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := T)
      .rv (.inl (.inl i)) (.inl (.inr i)))
  have moved := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := T)
    .vf (.inl (.inr 0)) (subVF F out center)
  unfold DefinableRelation at defC ⊢
  convert definable_project_mixed
    (source.inter ((defC.pullback_relabel data).inter (moved.inter (field.inter tags)))) using 1
  ext a
  let x : SortedAssignment Z U := fun s => a s ∘ Sum.inl
  let y : SortedAssignment Z U := fun s => a s ∘ Sum.inr
  have eval (v : SortedAssignment Z V) :
      (subVF F out center).realize 𝓜 (fun s => Sum.elim Subtype.val (appendAssignments a v s)) =
        x .vf 0 - v .vf 0 := by rw [eval_subVF O hO power F minusOne hm hF]; rfl
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  change (∃ _ : mixedTuple x ∈ A.carrier, A.translateHeadAssignment O hO power S c x = y) ↔
    ∃ v : SortedAssignment Z V, mixedTuple x ∈ A.carrier ∧ c (x .vf ∘ Fin.succ) (x .rv) = v .vf 0 ∧
      y .vf 0 = (subVF F out center).realize 𝓜 (fun s => Sum.elim Subtype.val (appendAssignments a v s)) ∧
      (∀ i : Fin n, x .vf i.succ = y .vf i.succ) ∧ (∀ i : A.tags, x .rv i = y .rv i)
  simp only [eval]
  constructor
  · rintro ⟨hx,e⟩
    refine ⟨fieldTupleAssignment (fun _ => c (x .vf ∘ Fin.succ) (x .rv)),hx,rfl,?_,?_,?_⟩
    · exact (congrFun (congrFun e .vf) 0).symm
    · exact fun i => congrFun (congrFun e .vf) i.succ
    · exact fun i => congrFun (congrFun e .rv) i
  · rintro ⟨v,hx,hc,hy,tail,tags⟩
    refine ⟨hx,?_⟩
    funext s i
    cases s
    · refine Fin.cases ?_ tail i
      exact (congrArg (x .vf 0 - ·) hc).trans hy.symm
    · exact tags i

variable
  (defC : DefinableRelation (canonicalStructure (L := L) O hO power) S.carrier
    (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables n A.tags))
      (b : fieldAssignment 1 (CanonicalSort O)) => c (a .vf) (a .rv) = b .vf 0))

@[expose] def taggedHeadTranslationIso :
    MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      (Set.range fun a : {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier} =>
        A.translateHeadAssignment O hO power S c a.val) :=
  MixedGraphIso.toRange (fun a => A.translateHeadAssignment O hO power S c a.val)
    (fun _ _ e => Subtype.ext (A.translateHeadAssignment_injective O hO power S c e))
    (A.translateHeadAssignment_graph O hO power S c F minusOne hm hF defC)

theorem taggedHeadTranslation_range_mem (a : SortedAssignment Z (MixedVariables (n+1) A.tags)) :
    a ∈ Set.range (fun u : {u : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple u ∈ A.carrier} =>
      A.translateHeadAssignment O hO power S c u.val) ↔
    (Fin.cons (a .vf 0 + c (a .vf ∘ Fin.succ) (a .rv)) (a .vf ∘ Fin.succ),a .rv) ∈ A.carrier := by
  constructor
  · rintro ⟨u,rfl⟩
    have fields : (Fin.cons (u.val .vf 0) (u.val .vf ∘ Fin.succ) : Fin (n+1) → K) = u.val .vf := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    change (Fin.cons (u.val .vf 0 - c (u.val .vf ∘ Fin.succ) (u.val .rv) + c (u.val .vf ∘ Fin.succ) (u.val .rv))
      (u.val .vf ∘ Fin.succ),u.val .rv) ∈ A.carrier
    rw [sub_add_cancel,fields]
    exact u.property
  · intro h
    let u : SortedAssignment Z (MixedVariables (n+1) A.tags)
      | .vf => Fin.cons (a .vf 0 + c (a .vf ∘ Fin.succ) (a .rv)) (a .vf ∘ Fin.succ)
      | .rv => a .rv
    refine ⟨⟨u,h⟩,?_⟩
    funext s i
    cases s
    · refine Fin.cases ?_ (fun _ => rfl) i
      exact add_sub_cancel_right _ _
    · rfl

@[expose] def taggedTranslatedHead (finite : ∀ b, (Set.range (c b)).Finite) :
    RetainedFieldFamily 𝓜 S (n+1) k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := {p | (Fin.cons (p.1 0 + c (p.1 ∘ Fin.succ) p.2) (p.1 ∘ Fin.succ),p.2) ∈ A.carrier}
  definable := by
    let : Finite A.tags := A.finiteTags
    have dd := (A.taggedHeadTranslationIso O hO power S c F minusOne hm hF defC).target_definable A.definable
    convert dd using 1
    ext a
    exact (A.taggedHeadTranslation_range_mem O hO power S c a).symm
  finiteFibers x v := by
    let b := x ∘ Fin.succ
    let R (y : K) := {t : A.tags → RV0 O | (Fin.cons (x 0 + y) b,t) ∈ A.carrier ∧ t ∘ A.select = v}
    have all : (⋃ y ∈ Set.range (c b), R y).Finite := (finite b).biUnion (fun y _ => A.finiteFibers _ _)
    apply all.subset
    rintro q ⟨hq,eq⟩
    exact Set.mem_iUnion₂.2 ⟨c b q,Set.mem_range_self q,hq,eq⟩

@[expose] def taggedTranslatedHead_iso (finite : ∀ b, (Set.range (c b)).Finite) :
    MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) A.tags) |
        mixedTuple b ∈ (A.taggedTranslatedHead O hO power S c F minusOne hm hF defC finite).carrier} :=
  (Set.ext fun _ => A.taggedHeadTranslation_range_mem O hO power S c _ ) ▸
    A.taggedHeadTranslationIso O hO power S c F minusOne hm hF defC

end RetainedFieldFamily

end GeneralizedEuler.Section5
