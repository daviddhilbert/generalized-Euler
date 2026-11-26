module

public import Section5.HeadContractionLift
public import Section5.MixedGraphIsomorphisms

/-! A preparation can be carried out before contracting its head.
Keep the normalized field coordinate and its full history, and only
add the leading term to the selection when that coordinate is dropped. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ}

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+1) k} (H : HeadContractionData A)

local notation "X" => CanonicalSort O

@[expose] def preparedFamily : RetainedFieldFamily M S (n+1) k where
  tags := H.target.tags
  finiteTags := H.target.finiteTags
  select := Sum.inr ∘ A.select
  carrier := H.liftedCarrier
  definable := H.liftedCarrier_definable
  finiteFibers b v := by
    let V : Fin (k+1) → RV0 O := Fin.lastCases (rv O (b 0)) v
    apply (H.target.finiteFibers (b ∘ Fin.succ) V).subset
    rintro t ⟨⟨ht,lead⟩,eq⟩
    refine ⟨ht,funext (fun i => ?_)⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have last : H.target.select (Fin.last k) = .inl (lastIndex H.length) := by
        change Fin.lastCases (motive := fun _ => HistoryIndex H.length ⊕ A.tags)
          (.inl (lastIndex H.length)) (Sum.inr ∘ A.select) (Fin.last k) = _
        exact Fin.lastCases_last
      have eV : V (Fin.last k) = rv O (b 0) := Fin.lastCases_last
      exact (congrArg t last).trans (lead.symm.trans eV.symm)
    · have earlier : H.target.select (Fin.castSucc j) = .inr (A.select j) := by
        change Fin.lastCases (motive := fun _ => HistoryIndex H.length ⊕ A.tags)
          (.inl (lastIndex H.length)) (Sum.inr ∘ A.select) (Fin.castSucc j) = _
        exact Fin.lastCases_castSucc j
      have eV : V (Fin.castSucc j) = v j := Fin.lastCases_castSucc j
      exact (congrArg t earlier).trans ((congrFun eq j).trans eV.symm)

theorem prepared_head_stable (b : Fin n → K) (x y : K) (t : H.preparedFamily.tags → RV0 O)
    (same : rv O x = rv O y) :
    ((x,b,t) ∈ H.preparedFamily.verticalCarrier ↔ (y,b,t) ∈ H.preparedFamily.verticalCarrier) := by
  change ((b,t) ∈ H.target.carrier ∧ rv O x = t (.inl (lastIndex H.length))) ↔
    ((b,t) ∈ H.target.carrier ∧ rv O y = t (.inl (lastIndex H.length)))
  rw [same]

theorem preparedFamily_iso :
    ∃ f : MixedGraphIso M S
      {a : SortedAssignment X (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment X (MixedVariables (n+1) H.preparedFamily.tags) | mixedTuple b ∈ H.preparedFamily.carrier},
      (∀ a, (f.equiv a).val .vf ∘ Fin.succ = a.val .vf ∘ Fin.succ) ∧
      (∀ a, (f.equiv a).val .rv ∘ Sum.inr = a.val .rv) := by
  let D := {a : SortedAssignment X (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
  let V := MixedVariables (n+1) H.preparedFamily.tags
  let R := {a : SortedAssignment X V | mixedTuple a ∈ H.preparedFamily.carrier}
  let pack : SortedAssignment X V ≃ PreparationPoint O (Fin (n+1)) H.preparedFamily.tags :=
    Equiv.ofBijective mixedTuple ⟨mixedTuple_injective,mixedTuple_surjective⟩
  let map (a : D) : SortedAssignment X V := pack.symm (H.liftPoint (mixedTuple a.val))
  have ev (a : D) : mixedTuple (map a) = H.liftPoint (mixedTuple a.val) := pack.apply_symm_apply _
  have inj : Function.Injective map := by
    intro a b e
    exact Subtype.ext (mixedTuple_injective (H.liftPoint_injective (by rw [← ev,← ev,e])))
  have graph : DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ D, map ⟨a,h⟩ = b) := by
    apply (H.liftPoint_definable.inter_left A.definable).congr
    intro a b
    constructor
    · rintro ⟨eq,ha⟩
      exact ⟨ha,mixedTuple_injective ((ev ⟨a,ha⟩).trans eq)⟩
    · rintro ⟨ha,rfl⟩
      exact ⟨(ev ⟨a,ha⟩).symm,ha⟩
  have target : Set.range map = R := by
    ext b
    constructor
    · rintro ⟨a,rfl⟩
      change mixedTuple (map a) ∈ H.liftedCarrier
      rw [ev,← H.liftPoint_image]
      exact ⟨_,a.property,rfl⟩
    · intro hb
      change mixedTuple b ∈ H.liftedCarrier at hb
      rw [← H.liftPoint_image] at hb
      obtain ⟨q,hq,eq⟩ := hb
      obtain ⟨a,rfl⟩ := mixedTuple_surjective q
      exact ⟨⟨a,hq⟩,mixedTuple_injective ((ev ⟨a,hq⟩).trans eq)⟩
  let f : MixedGraphIso M S D R := target ▸ MixedGraphIso.toRange map inj graph
  have evaluates (a : D) : mixedTuple (f.equiv a).val = H.liftPoint (mixedTuple a.val) := by
    have eq (V' : Set (SortedAssignment X V)) (h : Set.range map = V') :
        ∀ (a : D), ((h ▸ MixedGraphIso.toRange map inj graph : MixedGraphIso M S D V').equiv a).val = map a := by
      cases h
      exact fun _ => rfl
    rw [eq R target a]
    exact ev a
  refine ⟨f,?_,?_⟩
  · intro a
    funext i
    exact congrFun (congrArg Prod.fst (evaluates a)) i.succ
  · intro a
    funext i
    exact congrFun (congrArg Prod.snd (evaluates a)) (.inr i)

end HeadContractionData

end GeneralizedEuler.Section5
