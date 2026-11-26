module

public import Section5.TerminalSelectedEquivalence
public import Section5.HeadContractionIteration

/-! The two head steps of a Cartesian product can be taken
independently in its two unary factors. The terminal tags retain
both original histories. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}

local notation "Z" => CanonicalSort O

namespace RetainedFieldFamily

variable (A B : RetainedFieldFamily M S 1 0)

@[expose] def unaryProduct : RetainedFieldFamily M S 2 0 where
  tags := A.tags ⊕ B.tags
  finiteTags := by
    let := A.finiteTags
    let := B.finiteTags
    infer_instance
  select := Fin.elim0
  carrier := {p | ((fun _ => p.1 0),p.2 ∘ Sum.inl) ∈ A.carrier ∧
                 ((fun _ => p.1 1),p.2 ∘ Sum.inr) ∈ B.carrier}
  definable := by
    let left : (s : TCsort) → MixedVariables 1 A.tags s → MixedVariables 2 (A.tags ⊕ B.tags) s
      | .vf => fun _ => 0
      | .rv => Sum.inl
    let right : (s : TCsort) → MixedVariables 1 B.tags s → MixedVariables 2 (A.tags ⊕ B.tags) s
      | .vf => fun _ => 1
      | .rv => Sum.inr
    exact (A.definable.pullback_relabel left).inter (B.definable.pullback_relabel right)
  finiteFibers p _ := by
    let split (t : A.tags ⊕ B.tags → RV0 O) := (t ∘ Sum.inl,t ∘ Sum.inr)
    have injective : Function.Injective split := by
      intro t u e
      funext i
      rcases i with i | i
      · exact congrFun (congrArg Prod.fst e) i
      · exact congrFun (congrArg Prod.snd e) i
    have a := A.finiteFibers (fun _ => p 0) Fin.elim0
    have b := B.finiteFibers (fun _ => p 1) Fin.elim0
    apply ((a.prod b).preimage injective.injOn).subset
    intro t ht
    exact ⟨⟨ht.1.1,Subsingleton.elim _ _⟩,⟨ht.1.2,Subsingleton.elim _ _⟩⟩

end RetainedFieldFamily

namespace HeadContractionData

variable {A B : RetainedFieldFamily M S 1 0}
  (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B)

omit [Field K] in
private theorem unary_cons (x : K) (p : Fin 0 → K) : Fin.cons x p = fun _ => x := by
  funext i
  rw [Fin.fin_one_eq_zero i]
  rfl

@[expose] def productFirst (B : RetainedFieldFamily M S 1 0) :
    HeadContractionData (n := 1) (A.unaryProduct B) where
  length := H.length
  preparation _ := H.preparation Fin.elim0
  mapGraph := by
    let take : (s : TCsort) → HistoryGraphVariables 0 H.length s → HistoryGraphVariables 1 H.length s
      | .vf => Sum.elim Sum.inl Fin.elim0
      | .rv => id
    have dom : ∀ a : SortedAssignment Z (HistoryGraphVariables 1 H.length),
        a .vf ∘ take .vf ∘ Sum.inr = (Fin.elim0 : Fin 0 → K) := fun _ => Subsingleton.elim _ _
    convert H.mapGraph.pullback_relabel take using 1
    ext a
    change (H.preparation Fin.elim0).map (a .vf (.inl 0)) = _ ↔
      (H.preparation (a .vf ∘ take .vf ∘ Sum.inr)).map (a .vf (.inl 0)) = _
    rw [dom]
    rfl
  historyGraph := by
    let U := VerticalVariables 0 A.tags
    let V := VerticalVariables 1 (A.unaryProduct B).tags
    let W := RVVariables (HistoryIndex H.length)
    let take : (s : TCsort) → SumVariables U W s → SumVariables V W s
      | .vf => Sum.map (Sum.elim Sum.inl Fin.elim0) id
      | .rv => Sum.map Sum.inl id
    have g := H.historyGraph
    unfold DefinableRelation at g ⊢
    convert g.pullback_relabel take using 1
    apply Set.ext
    intro a
    change (H.preparation Fin.elim0).label (a .vf (.inl (.inl ()))) = _ ↔
      (H.preparation (fun i : Fin 0 => a .vf (take .vf (.inl (.inr i))))).label (a .vf (.inl (.inl ()))) = _
    rw [show (fun i : Fin 0 => a .vf (take .vf (.inl (.inr i)))) = (Fin.elim0 : Fin 0 → K) from Subsingleton.elim _ _]
    rfl
  constant b x y t h := by
    have c := H.constant Fin.elim0 x y (t ∘ Sum.inl) h
    change ((Fin.cons x Fin.elim0,t ∘ Sum.inl) ∈ A.carrier ↔ (Fin.cons y Fin.elim0,t ∘ Sum.inl) ∈ A.carrier) at c
    rw [unary_cons,unary_cons] at c
    change (((fun _ => x),t ∘ Sum.inl) ∈ A.carrier ∧ ((fun _ => b 0),t ∘ Sum.inr) ∈ B.carrier) ↔
      (((fun _ => y),t ∘ Sum.inl) ∈ A.carrier ∧ ((fun _ => b 0),t ∘ Sum.inr) ∈ B.carrier)
    exact and_congr c Iff.rfl
  finiteOffsets _ := H.finiteOffsets Fin.elim0
  finalLead _ := H.finalLead Fin.elim0

@[expose] def firstFactorTags
    (t : HistoryIndex H.length ⊕ (A.tags ⊕ B.tags) → RV0 O) : H.target.tags → RV0 O :=
  Sum.elim (t ∘ Sum.inl) (t ∘ Sum.inr ∘ Sum.inl)

theorem productFirst_target_mem
    (x : Fin 1 → K) (t : HistoryIndex H.length ⊕ (A.tags ⊕ B.tags) → RV0 O) :
    (x,t) ∈ (H.productFirst B).target.carrier ↔
      (Fin.elim0,H.firstFactorTags t) ∈ H.target.carrier ∧ (x,t ∘ Sum.inr ∘ Sum.inr) ∈ B.carrier := by
  have eta : (fun _ : Fin 1 => x 0) = x := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  change (∃ u, (((fun _ => u),t ∘ Sum.inr ∘ Sum.inl) ∈ A.carrier ∧
      ((fun _ => x 0),t ∘ Sum.inr ∘ Sum.inr) ∈ B.carrier) ∧
      (H.preparation Fin.elim0).label u = decodeHistory O H.length (t ∘ Sum.inl)) ↔
    (∃ u, (Fin.cons u Fin.elim0,t ∘ Sum.inr ∘ Sum.inl) ∈ A.carrier ∧
      (H.preparation Fin.elim0).label u = decodeHistory O H.length (t ∘ Sum.inl)) ∧
      (x,t ∘ Sum.inr ∘ Sum.inr) ∈ B.carrier
  rw [eta]
  simp only [unary_cons]
  exact ⟨fun ⟨u,⟨a,b⟩,e⟩ => ⟨⟨u,a,e⟩,b⟩,fun ⟨⟨u,a,e⟩,b⟩ => ⟨u,⟨a,b⟩,e⟩⟩

@[expose] def productSecond : HeadContractionData (n := 0) (H.productFirst B).target where
  length := J.length
  preparation _ := J.preparation Fin.elim0
  mapGraph := by
    convert J.mapGraph using 1
    ext v
    change (J.preparation Fin.elim0).map (v .vf (.inl 0)) = _ ↔
      (J.preparation (v .vf ∘ Sum.inr)).map (v .vf (.inl 0)) = _
    rw [show v .vf ∘ Sum.inr = (Fin.elim0 : Fin 0 → K) from Subsingleton.elim _ _]
  historyGraph := by
    let U := VerticalVariables 0 B.tags
    let V := VerticalVariables 0 (H.productFirst B).target.tags
    let W := RVVariables (HistoryIndex J.length)
    let take : (s : TCsort) → SumVariables U W s → SumVariables V W s
      | .vf => id
      | .rv => Sum.map (Sum.inr ∘ Sum.inr) id
    unfold DefinableRelation
    convert J.historyGraph.pullback_relabel take using 1
    ext v
    have b : (fun i : Fin 0 => v .vf (.inl (.inr i))) = Fin.elim0 := Subsingleton.elim _ _
    change (J.preparation Fin.elim0).label (v .vf (.inl (.inl ()))) = _ ↔
      (J.preparation (fun i : Fin 0 => v .vf (.inl (.inr i)))).label (v .vf (.inl (.inl ()))) = _
    rw [b]
    rfl
  constant b x y t h := by
    change (HistoryIndex H.length ⊕ (A.tags ⊕ B.tags) → RV0 O) at t
    change (Fin.cons x b,t) ∈ (H.productFirst B).target.carrier ↔
      (Fin.cons y b,t) ∈ (H.productFirst B).target.carrier
    rw [H.productFirst_target_mem,H.productFirst_target_mem]
    apply and_congr_right
    intro _
    have eq : b = (Fin.elim0 : Fin 0 → K) := Subsingleton.elim _ _
    rw [eq]
    exact J.constant Fin.elim0 x y (t ∘ Sum.inr ∘ Sum.inr) h
  finiteOffsets _ := J.finiteOffsets Fin.elim0
  finalLead _ := J.finalLead Fin.elim0

/-- The two unary preparations act independently in the given order. -/
theorem unaryProduct_run : HeadContractionRun (A.unaryProduct B) (H.productSecond J).target :=
  .next (H.productFirst B) (.next (H.productSecond J) (.done _))

end HeadContractionData

end GeneralizedEuler.Section5
