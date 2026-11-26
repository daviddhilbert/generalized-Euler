module

public import Section5.PositionedTwoHeadOutputs
public import Section5.TaggedPositionedHeads
public import Section5.TaggedCenterFiniteness
public import Section5.TaggedUnaryImages

/-! The first change translates the positioned fibers. The second
change takes the unary target of positioning to a common prepared
domain, carrying the paradigm as an RV label. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem positioned_two_head_refinement
    (hyp : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    (A : RetainedFieldFamily 𝓜 S 2 k) (B D : Set (K × (A.tags → RV0 O)))
    (center move : K → (A.tags → RV0 O) → K)
    (paradigm : (A.tags → RV0 O) → RV0 O)
    (defC : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 A.tags)) (v : fieldAssignment 1 Z) =>
        center (a .vf 0) (a .rv) = v .vf 0))
    (defMove : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables 1 A.tags)) (v : fieldAssignment 1 Z) =>
        move (a .vf 0) (a .rv) = v .vf 0))
    (shape : ∀ x b t, (x,b,t) ∈ A.verticalCarrier ↔
      (b 0,t) ∈ B ∧ rv O (x-center (b 0) t) = paradigm t)
    (bij : ∀ t, Set.BijOn (fun x => move x t) {y | (y,t) ∈ B} {y | (y,t) ∈ D})
    (cs : List (S.carrier .vf))
    (stable : ∀ x y (t : A.tags → RV0 O),
      ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label x =
        ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label y →
      ((x,t) ∈ D ↔ (y,t) ∈ D)) :
    Nonempty (PositionedTwoHeadOutput A D A.select paradigm
      ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs)) := by
  let : Finite A.tags := A.finiteTags
  let F := hyp.fieldTerms
  let minusOne := hyp.minusOne
  let hm := hyp.minusOne_realizes
  let hF := hyp.fieldTerms_realize
  let c (b : Fin 1 → K) (t : A.tags → RV0 O) := center (b 0) t
  have finite := finite_tagged_center_range O hO power S hyp he small c defC
  let P := A.taggedTranslatedHead O hO power S c F minusOne hm hF defC finite
  let B' : Set (PreparationPoint O (Fin 1) A.tags) := {p | (p.1 0,p.2) ∈ B}
  let H := HeadContractionData.taggedPositionHead O hO power S A c F minusOne hm hF defC finite
    B' paradigm shape zero hz
  let R := H.target
  have rshape (b : Fin 1 → K) (t : Unit ⊕ A.tags → RV0 O) :
      (b,t) ∈ R.carrier ↔ (b 0,t ∘ Sum.inr) ∈ B ∧ t (.inl ()) = paradigm (t ∘ Sum.inr) :=
    HeadContractionData.taggedPositionHead_target_mem O hO power S A c F minusOne hm hF defC finite
      B' paradigm shape zero hz b t
  let initialIso := A.taggedTranslatedHead_iso O hO power S c F minusOne hm hF defC finite
  have firstEval := A.taggedTranslatedHead_iso_apply O hO power S c F minusOne hm hF defC finite
  let U := MixedVariables 1 A.tags
  let U' := MixedVariables 1 R.tags
  let V := MixedVariables 1 Empty
  let ren : (s : TCsort) → SumVariables U V s → SumVariables U' V s
    | .vf => id
    | .rv => Sum.elim (Sum.inl ∘ Sum.inr) Empty.elim
  have moveDef : DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment Z U') (v : fieldAssignment 1 Z) =>
      move (a .vf 0) (a .rv ∘ Sum.inr) = v .vf 0) := by
    unfold DefinableRelation at defMove ⊢
    exact defMove.pullback_relabel ren
  have inj (t : R.tags → RV0 O) :
      Set.InjOn (fun x => move x (t ∘ Sum.inr)) {x | ((fun _ => x),t) ∈ R.carrier} := by
    intro x hx y hy e
    exact (bij (t ∘ Sum.inr)).injOn ((rshape _ t).1 hx).1 ((rshape _ t).1 hy).1 e
  obtain ⟨e,keep⟩ := tagged_unary_image_iso O hO power S R (fun x t => move x (t ∘ Sum.inr)) moveDef inj
  let D' : MixedCarrier Z 1 R.tags := {b | ∃ x, ((fun _ => x),b .rv) ∈ R.carrier ∧
    move x (b .rv ∘ Sum.inr) = b .vf 0}
  let : Finite R.tags := R.finiteTags
  let C := RetainedFieldFamily.ofRelativeIso O hO power S R D' R.select hyp he small zero e
    (fun a => congrArg (· ∘ R.select) (keep a))
  have target : {b : SortedAssignment Z U' | mixedTuple b ∈ C.carrier} = D' := by
    ext a
    change mixedAssignment (a .vf) (a .rv) ∈ D' ↔ a ∈ D'
    rw [mixedAssignment_eta]
  let centeredIso : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z U' | mixedTuple a ∈ R.carrier}
      {b : SortedAssignment Z U' | mixedTuple b ∈ C.carrier} := target.symm ▸ e
  have secondKeep (a : {a : SortedAssignment Z U' | mixedTuple a ∈ R.carrier}) :
      (centeredIso.equiv a).val .rv ∘ C.select = a.val .rv ∘ R.select := by
    have transports (D₀ : Set (SortedAssignment Z U')) (h : D' = D₀) :
        ((h ▸ e : MixedGraphIso 𝓜 S _ D₀).equiv a).val .rv = a.val .rv := by
      cases h
      exact keep a
    exact congrArg (· ∘ R.select) (transports _ target.symm)
  have cshape (b : Fin 1 → K) (t : Unit ⊕ A.tags → RV0 O) :
      (b,t) ∈ C.carrier ↔ (b 0,t ∘ Sum.inr) ∈ D ∧ t (.inl ()) = paradigm (t ∘ Sum.inr) := by
    change (∃ x, ((fun _ => x),t) ∈ R.carrier ∧ move x (t ∘ Sum.inr) = b 0) ↔ _
    constructor
    · rintro ⟨x,h,he⟩
      obtain ⟨mem,tag⟩ := (rshape _ t).1 h
      exact ⟨he ▸ (bij (t ∘ Sum.inr)).mapsTo mem,tag⟩
    · rintro ⟨h,tag⟩
      obtain ⟨x,hx,he⟩ := (bij (t ∘ Sum.inr)).surjOn h
      exact ⟨x,(rshape _ t).2 ⟨hx,tag⟩,he⟩
  let J := HeadContractionData.positionedTail O hO power S C Sum.inr (.inl ()) paradigm D cs
    F minusOne hm hF cshape stable
  let : Finite J.target.tags := J.target.finiteTags
  let setup : TwoHeadRefinement A :=
    { positioned := P
      first := H
      centered := C
      second := J
      firstIso := initialIso
      firstTail := fun a => congrArg (fun x => x .vf ∘ Fin.succ) (firstEval a)
      firstSelected := fun a => congrArg (fun x => x .rv ∘ A.select) (firstEval a)
      secondIso := centeredIso
      secondSelected := secondKeep
      arity := Nat.card J.target.tags
      enumerate := (Finite.equivFin _).symm }
  refine ⟨⟨setup,Equiv.refl _,?_,?_⟩⟩
  · intro i
    change J.target.select i = positionedPairSelect A.select i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [J.target_select_last,positionedPairSelect,Fin.lastCases_last]
      rfl
    · rw [J.target_select_castSucc]
      unfold positionedPairSelect
      rw [Fin.lastCases_castSucc]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · change Sum.inr (H.target.select (Fin.last k)) = _
        rw [H.target_select_last,Fin.lastCases_last]
        rfl
      · change Sum.inr (H.target.select (Fin.castSucc j)) = _
        rw [H.target_select_castSucc,Fin.lastCases_castSucc]
        rfl
  · exact HeadContractionData.positionedTail_target_mem O hO power S C Sum.inr (.inl ()) paradigm D cs
      F minusOne hm hF cshape stable

end GeneralizedEuler.Section5
