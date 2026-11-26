module

public import Section5.InverseUnaryTests
public import Section5.PaddedFieldLift

/-! Construct the graph of an actual unary translation from the
definable relation selecting its focus. The old leading term is retained. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Use the chosen focus on its definable domain and zero on the
complement. This gives the offset used in the translation graph. -/
theorem default_zero_focus_definable
    {V : TCsort → Type}
    (focus : SortedAssignment (CanonicalSort O) V → K → Prop)
    (defFocus : DefinableRelation 𝓜 S.carrier
      (fun a (v : fieldAssignment 1 (CanonicalSort O)) => focus a (v .vf 0))) :
    DefinableRelation 𝓜 S.carrier
      (fun a (v : fieldAssignment 1 (CanonicalSort O)) =>
        focus a (v .vf 0) ∨ ((∀ c, ¬ focus a c) ∧ v .vf 0 = 0)) := by
  let W := MixedVariables 1 Empty
  have top : SortedDefinableOver 𝓜 S.carrier (Set.univ : Set (fieldAssignment 1 (CanonicalSort O))) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have dom := defFocus.preimage top
  have fail : SortedDefinableOver 𝓜 S.carrier {x | ∀ c, ¬ focus x c} := by
    convert dom.compl using 1
    ext x
    constructor
    · intro h
      rintro ⟨v,_,hv⟩
      exact h _ hv
    · intro h c hc
      exact h ⟨fieldTupleAssignment (fun _ => c),Set.mem_univ _,hc⟩
  have zero := field_eq_zero_definable O hO power S (V := W) 0
  have h : DefinableRelation 𝓜 S.carrier
      (fun a (v : fieldAssignment 1 (CanonicalSort O)) => (∀ c, ¬ focus a c) ∧ v .vf 0 = 0) :=
    (fail.pullback_relabel (fun _ => Sum.inl)).inter (zero.pullback_relabel (fun _ => Sum.inr))
  exact defFocus.union h

/-- With a focus selected by a definable graph, the new coordinate is a
field difference, and the new tag is the old leading term. -/
theorem unary_translation_graph_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (focus : SortedAssignment (CanonicalSort O) (MixedVariables 1 I) → K → Prop)
    (defFocus : DefinableRelation 𝓜 S.carrier
      (fun a (v : fieldAssignment 1 (CanonicalSort O)) => focus a (v .vf 0))) :
    DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
      (b : SortedAssignment (CanonicalSort O) (MixedVariables 1 (I ⊕ Unit))) =>
      ∃ c, focus a c ∧ b .vf 0 = a .vf 0-c ∧
        (∀ i, b .rv (.inl i) = a .rv i) ∧ b .rv (.inr ()) = rv O (a .vf 0)) := by
  let U := MixedVariables 1 I
  let V := MixedVariables 1 (I ⊕ Unit)
  let W := SumVariables (SumVariables U V) (MixedVariables 1 Empty)
  let rename : ∀ s, SumVariables U (MixedVariables 1 Empty) s → W s
    | .vf => Sum.map Sum.inl id
    | .rv => Sum.map Sum.inl Empty.elim
  let T := WithBase S.carrier W
  let x : SortedTerm L E T .vf := .var (.inr (.inl (.inl 0)))
  let z : SortedTerm L E T .vf := .var (.inr (.inr 0))
  have hs := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .vf (.inl (.inr 0)) (subVF F x z)
  have hl := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inl (.inr (.inr ()))) (rvOfVF x)
  have he := SortedDefinableOver.iInter (fun i : I =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := W)
      .rv (.inl (.inr (.inl i))) (.inl (.inl i)))
  unfold DefinableRelation at defFocus ⊢
  have all := (defFocus.pullback_relabel rename).inter (hs.inter (he.inter hl))
  convert definable_project_mixed all using 1
  ext w
  let a : SortedAssignment (CanonicalSort O) U := fun s => w s ∘ Sum.inl
  let b : SortedAssignment (CanonicalSort O) V := fun s => w s ∘ Sum.inr
  let input (v : fieldAssignment 1 (CanonicalSort O)) : SortedAssignment (CanonicalSort O) U :=
    fun s => (Sum.elim (w s) (v s) ∘ rename s) ∘ Sum.inl
  have inputEq (v) : input v = a := by
    funext s i
    cases s <;> rfl
  let interpret (v : fieldAssignment 1 (CanonicalSort O)) (s : TCsort) : T s → CanonicalSort O s :=
    Sum.elim Subtype.val (Sum.elim (w s) (v s))
  have sub (v) : (subVF F x z).realize 𝓜 (interpret v) = a .vf 0 - v .vf 0 := by
    rw [eval_subVF O hO power F minusOne hm hF]
    rfl
  have lead (v) : (rvOfVF x).realize 𝓜 (interpret v) = rv O (a .vf 0) := by
    rw [eval_rvOfVF O hO power]
    rfl
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  change (∃ c, focus a c ∧ b .vf 0 = a .vf 0 - c ∧
      (∀ i, b .rv (.inl i) = a .rv i) ∧ b .rv (.inr ()) = rv O (a .vf 0)) ↔
    ∃ v : fieldAssignment 1 (CanonicalSort O), focus (input v) (v .vf 0) ∧
      b .vf 0 = (subVF F x z).realize 𝓜 (interpret v) ∧
      (∀ i, b .rv (.inl i) = a .rv i) ∧ b .rv (.inr ()) = (rvOfVF x).realize 𝓜 (interpret v)
  simp only [inputEq,sub,lead]
  exact ⟨fun ⟨c,hc⟩ => ⟨fieldTupleAssignment (fun _ => c),hc⟩,fun ⟨v,hv⟩ => ⟨v .vf 0,hv⟩⟩

end GeneralizedEuler.Section5
