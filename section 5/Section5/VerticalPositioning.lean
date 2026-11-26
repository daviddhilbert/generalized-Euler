module

public import Section5.UniformVerticalPreparation
public import Section5.DefinableRelations
public import Section5.DefinableBijectionSchemes
public import Section5.LiftBoundaryDimension

/-! The vertical preparation gives full translated leading-term
fibers and a positioning function definable over the original base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K) {H : Type*}

theorem UnaryPreparation.restricted_label_fiber (P : UnaryPreparation O H) (D : Set K)
    (constant : ∀ x y, P.label x = P.label y → (x ∈ D ↔ y ∈ D)) (h : H) (x : K) :
    (x ∈ D ∧ P.label x = h) ↔
      (∃ y ∈ D, P.label y = h) ∧ rv O (x - P.offset h) = P.lead h := by
  constructor
  · rintro ⟨hx,e⟩
    exact ⟨⟨x,hx,e⟩,e ▸ P.leading x⟩
  · rintro ⟨⟨y,hy,ey⟩,hr⟩
    have e : P.label x = P.label y := P.constant_label (ey.symm ▸ hr)
    exact ⟨(constant x y e).2 hy,e.trans ey⟩

variable {n ℓ : ℕ} {I : Type}

local notation "Hist" => HistoryIndex ℓ
local notation "Prep" => UnaryPreparation O (PreparationLabels O (RV0 O) ℓ)
local notation "Domain" => Set (K × ((Fin n → K) × (I → RV0 O)))

@[expose] def verticalPositioningGraph
    (P : (Fin n → K) → Prep) (A : Domain)
    (a : SortedAssignment (CanonicalSort O) (MixedVariables n (I ⊕ Hist)))
    (c : fieldAssignment 1 (CanonicalSort O)) : Prop :=
  let h := decodeHistory O ℓ (a .rv ∘ Sum.inr)
  (∃ x, (x,a .vf,a .rv ∘ Sum.inl) ∈ A ∧ (P (a .vf)).label x = h) ∧ (P (a .vf)).offset h = c .vf 0

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
  {E : Type*} [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O

theorem vertical_history_graph_definable
    (P : (Fin n → K) → Prep)
    (defP : SortedDefinableOver 𝓜 S.carrier {v : SortedAssignment X (HistoryGraphVariables n ℓ) |
      (P (v .vf ∘ Sum.inr)).map (v .vf (.inl 0)) = (v .vf (.inl 1),decodeHistory O ℓ (v .rv))}) :
    DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment X (VerticalVariables n I))
      (h : SortedAssignment X (RVVariables Hist)) =>
        (P (a .vf ∘ Sum.inr)).label (a .vf (.inl ())) = decodeHistory O ℓ (h .rv)) := by
  let U := VerticalVariables n I
  let V := RVVariables Hist
  let W := SumVariables U V
  let T := SumVariables W (MixedVariables 1 Empty)
  let r : (s : TCsort) → HistoryGraphVariables n ℓ s → T s
    | .vf => Sum.elim (fun j => if j = 0 then .inl (.inl (.inl ())) else .inr 0)
        (Sum.inl ∘ Sum.inl ∘ Sum.inr)
    | .rv => Sum.inl ∘ Sum.inr
  unfold DefinableRelation
  convert definable_project_mixed (defP.pullback_relabel r) using 1
  ext w
  let Q := P (w .vf ∘ Sum.inl ∘ Sum.inr)
  let x := w .vf (.inl (.inl ()))
  let h := decodeHistory O ℓ (w .rv ∘ Sum.inr)
  change Q.label x = h ↔ ∃ y : fieldAssignment 1 X, Q.map x = (y .vf 0,h)
  exact ⟨fun e => ⟨fieldTupleAssignment (fun _ => (Q.map x).1),Prod.ext rfl e⟩,
    fun ⟨_,e⟩ => congrArg Prod.snd e⟩

theorem verticalPositioningGraph_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (P : (Fin n → K) → Prep) (A : Domain)
    (defA : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment X (VerticalVariables n I) | (a .vf (.inl ()),a .vf ∘ Sum.inr,a .rv) ∈ A})
    (defP : SortedDefinableOver 𝓜 S.carrier {v : SortedAssignment X (HistoryGraphVariables n ℓ) |
      (P (v .vf ∘ Sum.inr)).map (v .vf (.inl 0)) = (v .vf (.inl 1),decodeHistory O ℓ (v .rv))}) :
    DefinableRelation 𝓜 S.carrier (verticalPositioningGraph O P A) := by
  let U := MixedVariables n (I ⊕ Hist)
  let V := MixedVariables 1 Empty
  let W := SumVariables U V
  let T := SumVariables W (MixedVariables 2 Empty)
  let input : (s : TCsort) → VerticalVariables n I s → T s
    | .vf => Sum.elim (fun _ => .inr 0) (Sum.inl ∘ Sum.inl)
    | .rv => Sum.inl ∘ Sum.inl ∘ Sum.inl
  let prep : (s : TCsort) → HistoryGraphVariables n ℓ s → T s
    | .vf => Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)
    | .rv => Sum.inl ∘ Sum.inl ∘ Sum.inr
  let vars := WithBase S.carrier T
  let x : SortedTerm L E vars .vf := .var (.inr (.inr 0))
  let y : SortedTerm L E vars .vf := .var (.inr (.inr 1))
  have center := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := T)
    .vf (.inl (.inr 0)) (subVF F x y)
  unfold DefinableRelation
  convert definable_project_mixed ((defA.pullback_relabel input).inter ((defP.pullback_relabel prep).inter center)) using 1
  ext w
  let b := w .vf ∘ Sum.inl
  let c := w .vf (.inr 0)
  let e := w .rv ∘ Sum.inl ∘ Sum.inl
  let h := decodeHistory O ℓ (w .rv ∘ Sum.inl ∘ Sum.inr)
  let Q := P b
  have coord (v : SortedAssignment X (MixedVariables 2 Empty)) :
      (subVF F x y).realize 𝓜 (fun s => Sum.elim Subtype.val (appendAssignments w v s)) = v .vf 0 - v .vf 1 := by
    rw [eval_subVF O hO power F minusOne hm hF]
    rfl
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff]
  change ((∃ x, (x,b,e) ∈ A ∧ Q.label x = h) ∧ Q.offset h = c) ↔
    (∃ v : SortedAssignment X (MixedVariables 2 Empty),
      (v .vf 0,b,e) ∈ A ∧ Q.map (v .vf 0) = (v .vf 1,h) ∧
        c = (subVF F x y).realize 𝓜 (fun s => Sum.elim Subtype.val (appendAssignments w v s)))
  simp only [coord]
  constructor
  · rintro ⟨⟨a,ha,eq⟩,he⟩
    let v : fieldAssignment 2 X := fieldTupleAssignment (Fin.cases a (fun _ => a-Q.offset h))
    refine ⟨v,ha,Prod.ext ?_ eq,?_⟩
    · change a - Q.offset (Q.label a) = a - Q.offset h
      rw [eq]
    · change c = a - (a - Q.offset h)
      rw [sub_sub_cancel,he]
  · rintro ⟨v,hv,eq,he⟩
    have lbl := congrArg Prod.snd eq
    have fld := congrArg Prod.fst eq
    change Q.label (v .vf 0) = h at lbl
    change v .vf 0 - Q.offset (Q.label (v .vf 0)) = v .vf 1 at fld
    refine ⟨⟨v .vf 0,hv,lbl⟩,?_⟩
    rw [← lbl,he,← fld,sub_sub_cancel]

set_option linter.style.haveILetI false in
theorem uniform_vertical_positioning
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
      (BaseAssignments S.carrier (VerticalPairVariables n I)))
    (immediate : ∀ (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Domain)
    (defA : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment X (VerticalVariables n I) | (a .vf (.inl ()),a .vf ∘ Sum.inr,a .rv) ∈ A}) :
    ∃ (m : ℕ) (terms : Fin m → SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf),
      let cs := List.ofFn (id : Fin m → Fin m)
      let P (b : Fin n → K) := centerPreparation (O := O) (centerValues O hO power S terms b) cs
      DefinableRelation 𝓜 S.carrier (verticalPositioningGraph O P A) ∧
      DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment X (VerticalVariables n I))
        (h : SortedAssignment X (RVVariables (HistoryIndex cs.length))) =>
          (P (a .vf ∘ Sum.inr)).label (a .vf (.inl ())) = decodeHistory O cs.length (h .rv)) ∧
      ∀ (b : Fin n → K) (ξ : I → RV0 O) h x,
        ((x,b,ξ) ∈ A ∧ (P b).label x = h) ↔
          (∃ y, (y,b,ξ) ∈ A ∧ (P b).label y = h) ∧ rv O (x - (P b).offset h) = (P b).lead h := by
  obtain ⟨m,terms,stable,hgraph,_⟩ := uniform_vertical_preparation O hO power S minusOne hm F hF sat immediate A defA
  let cs := List.ofFn (id : Fin m → Fin m)
  let P (b : Fin n → K) := centerPreparation (O := O) (centerValues O hO power S terms b) cs
  refine ⟨m,terms,verticalPositioningGraph_definable O hO power S F minusOne hm hF P A defA hgraph,
    vertical_history_graph_definable O hO power S (I := I) (ℓ := cs.length) (n := n) P hgraph,?_⟩
  intro b ξ h x
  exact UnaryPreparation.restricted_label_fiber O _ {y | (y,b,ξ) ∈ A}
    (fun a d e => stable b a d ξ e) h x

end GeneralizedEuler.Section5
