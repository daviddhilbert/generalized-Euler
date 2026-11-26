module

public import Section5.VerticalContraction
public import Section5.UnaryLiftObjects
public import Section5.UnaryLifting

/-! A head contraction of a retained-label family preserves the
finite-fiber condition after the new leading term is appended. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}

structure RetainedFieldFamily (M : SortedStructure L E (CanonicalSort O)) (S : SortedSubstructure M) (n k : ℕ) where
  tags : Type
  finiteTags : Finite tags
  select : Fin k → tags
  carrier : Set (PreparationPoint O (Fin n) tags)
  definable : SortedDefinableOver M S.carrier
    {a : SortedAssignment (CanonicalSort O) (MixedVariables n tags) | mixedTuple a ∈ carrier}
  finiteFibers : ∀ b (v : Fin k → RV0 O), {q : tags → RV0 O | (b,q) ∈ carrier ∧ q ∘ select = v}.Finite

variable {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S (n+1) k)

@[expose] def verticalCarrier : Set (K × ((Fin n → K) × (A.tags → RV0 O))) :=
  {p | (Fin.cons p.1 p.2.1,p.2.2) ∈ A.carrier}

theorem verticalCarrier_definable :
    SortedDefinableOver M S.carrier
      {a : SortedAssignment (CanonicalSort O) (VerticalVariables n A.tags) |
        (a .vf (.inl ()), a .vf ∘ Sum.inr,a .rv) ∈ A.verticalCarrier} := by
  let relabel : (s : TCsort) → MixedVariables (n+1) A.tags s → VerticalVariables n A.tags s
    | .vf => Fin.cases (.inl ()) (fun i => .inr i)
    | .rv => id
  convert A.definable.pullback_relabel relabel using 1
  ext a
  have fields : Fin.cons (a .vf (.inl ())) (a .vf ∘ Sum.inr) = a .vf ∘ relabel .vf := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  change (Fin.cons (a .vf (.inl ())) (a .vf ∘ Sum.inr),a .rv) ∈ A.carrier ↔
    (a .vf ∘ relabel .vf,a .rv) ∈ A.carrier
  rw [fields]

end RetainedFieldFamily

structure HeadContractionData (A : RetainedFieldFamily M S (n+1) k) where
  length : ℕ
  preparation : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) length)
  mapGraph : SortedDefinableOver M S.carrier
    {a : SortedAssignment (CanonicalSort O) (HistoryGraphVariables n length) |
      (preparation (a .vf ∘ Sum.inr)).map (a .vf (.inl 0)) = (a .vf (.inl 1),decodeHistory O length (a .rv))}
  historyGraph : DefinableRelation M S.carrier
    (fun (a : SortedAssignment (CanonicalSort O) (VerticalVariables n A.tags))
      (h : SortedAssignment (CanonicalSort O) (RVVariables (HistoryIndex length))) =>
        (preparation (a .vf ∘ Sum.inr)).label (a .vf (.inl ())) = decodeHistory O length (h .rv))
  constant : ∀ b x y t, (preparation b).label x = (preparation b).label y →
    ((x,b,t) ∈ A.verticalCarrier ↔ (y,b,t) ∈ A.verticalCarrier)
  finiteOffsets : ∀ b, (Set.range (preparation b).offset).Finite
  finalLead : ∀ b q, (preparation b).lead (decodeHistory O length q) = q (lastIndex length)

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+1) k} (H : HeadContractionData A)

theorem target_finite (b : Fin n → K) (v : Fin (k+1) → RV0 O) :
    {t : HistoryIndex H.length ⊕ A.tags → RV0 O |
      (b,t) ∈ contractedVerticalSet O H.preparation A.verticalCarrier ∧
      t ∘ Fin.lastCases (.inl (lastIndex H.length)) (Sum.inr ∘ A.select) = v}.Finite := by
  have f := contractedVerticalSet_selected_finite O H.preparation A.verticalCarrier A.select (lastIndex H.length)
    H.finalLead H.finiteOffsets (fun x b => A.finiteFibers (Fin.cons x b)) H.constant
    b (v (Fin.last k)) (v ∘ Fin.castSucc)
  apply f.subset
  rintro t ⟨ht,eq⟩
  refine ⟨ht,?_,?_⟩
  · have he := congrFun eq (Fin.last k)
    simpa only [Function.comp_apply,Fin.lastCases_last] using he
  · funext i
    have he := congrFun eq (Fin.castSucc i)
    simpa only [Function.comp_apply,Fin.lastCases_castSucc] using he

/-- The old head start occupies its original positions. The leading
term of the coordinate just removed is the final selected label. -/
@[expose] def target : RetainedFieldFamily M S n (k+1) where
  tags := HistoryIndex H.length ⊕ A.tags
  finiteTags := by
    let := A.finiteTags
    infer_instance
  select := Fin.lastCases (.inl (lastIndex H.length)) (Sum.inr ∘ A.select)
  carrier := contractedVerticalSet O H.preparation A.verticalCarrier
  definable := contractedVerticalSet_definable O H.preparation A.verticalCarrier A.verticalCarrier_definable H.historyGraph
  finiteFibers := H.target_finite

theorem target_select_last : H.target.select (Fin.last k) = .inl (lastIndex H.length) := by
  change Fin.lastCases (motive := fun _ => HistoryIndex H.length ⊕ A.tags)
    (.inl (lastIndex H.length)) (Sum.inr ∘ A.select) (Fin.last k) = _
  exact Fin.lastCases_last

theorem target_select_castSucc (i : Fin k) : H.target.select (Fin.castSucc i) = .inr (A.select i) := by
  change Fin.lastCases (motive := fun _ => HistoryIndex H.length ⊕ A.tags)
    (.inl (lastIndex H.length)) (Sum.inr ∘ A.select) (Fin.castSucc i) = _
  exact Fin.lastCases_castSucc i

end HeadContractionData

section Canonical
variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem head_contraction_data_exists
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S₀ (n+1) k)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S₀.carrier (VerticalPairVariables n A.tags))
      (BaseAssignments S₀.carrier (VerticalPairVariables n A.tags)))
    (immediate : ∀ (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S₀ b)
      (∀ c : B.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t) :
    Nonempty (HeadContractionData A) := by
  obtain ⟨m,terms,stable,graph,_⟩ := uniform_vertical_preparation O hO power S₀ minusOne hm F hF sat immediate
    A.verticalCarrier A.verticalCarrier_definable
  let cs := List.ofFn (id : Fin m → Fin m)
  let centers := centerValues O hO power S₀ terms
  let P (b : Fin n → K) := centerPreparation (O := O) (centers b) cs
  exact ⟨⟨cs.length,P,graph,vertical_history_graph_definable O hO power S₀ (I := A.tags) (ℓ := cs.length) P graph,
    stable,fun b => UnaryPreparation.finite_prepared_offsets (centers b ∘ some) cs,
    fun b => lead_decode_history O (centers b ∘ some) cs⟩⟩

end Canonical

end GeneralizedEuler.Section5
