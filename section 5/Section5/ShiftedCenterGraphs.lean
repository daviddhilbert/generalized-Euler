module

public import Section5.PairedUnaryGraphs

/-! A later center test subtracts the previous offset. The old tag
and leading term supply this offset on the new RV tag. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "𝕂" => fieldAssignment 1 (CanonicalSort O)

theorem definable_difference_of_field_graphs {P : TCsort → Type}
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (c d : SortedAssignment (CanonicalSort O) P → K)
    (hc : DefinableRelation 𝓜 S.carrier (fun a (v : 𝕂) => v .vf 0 = c a))
    (hd : DefinableRelation 𝓜 S.carrier (fun a (v : 𝕂) => v .vf 0 = d a)) :
    DefinableRelation 𝓜 S.carrier (fun a (v : 𝕂) => v .vf 0 = c a - d a) := by
  let V := MixedVariables 1 Empty
  let Z := MixedVariables 2 Empty
  let W := SumVariables (SumVariables P V) Z
  let rename (i : Fin 2) : ∀ s, SumVariables P V s → W s
    | .vf => Sum.elim (Sum.inl ∘ Sum.inl) (fun _ => .inr i)
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl) Empty.elim
  let x : SortedTerm L E (WithBase S.carrier W) .vf := .var (.inr (.inr 0))
  let y : SortedTerm L E (WithBase S.carrier W) .vf := .var (.inr (.inr 1))
  have hs := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .vf (.inl (.inr 0)) (subVF F x y)
  unfold DefinableRelation at hc hd ⊢
  have h := ((hc.pullback_relabel (rename 0)).inter (hd.pullback_relabel (rename 1))).inter hs
  convert definable_project_mixed h using 1
  ext w
  let a : SortedAssignment (CanonicalSort O) P := fun s => w s ∘ Sum.inl
  let value (v : fieldAssignment 2 (CanonicalSort O)) (s : TCsort) : WithBase S.carrier W s → _ :=
    Sum.elim Subtype.val (Sum.elim (w s) (v s))
  have input (v : fieldAssignment 2 (CanonicalSort O)) (i : Fin 2) :
      (fun s => ((Sum.elim (w s) (v s)) ∘ rename i s) ∘ Sum.inl) = a := by
    funext s k
    cases s <;> rfl
  have sub (v : fieldAssignment 2 (CanonicalSort O)) : (subVF F x y).realize 𝓜 (value v) =
      v .vf 0 - v .vf 1 := by
    rw [eval_subVF O hO power F minusOne hm hF]
    rfl
  change w .vf (.inr 0) = c a - d a ↔
    ∃ v : fieldAssignment 2 (CanonicalSort O), (v .vf 0 = c (fun s => _ ∘ Sum.inl) ∧
      v .vf 1 = d (fun s => _ ∘ Sum.inl)) ∧
      w .vf (.inr 0) = (subVF F x y).realize 𝓜 (value v)
  simp only [input,sub]
  constructor
  · intro eq
    exact ⟨fieldTupleAssignment ![c a,d a],⟨rfl,rfl⟩,eq⟩
  · rintro ⟨v,⟨hc',hd'⟩,hs'⟩
    simpa only [hc',hd'] using hs'

variable {J : Type} [Finite J] {B : Set (K × (J → RV0 O))}
  (C : Set (RV0 O × (J → RV0 O))) (focus : RV0 O × (J → RV0 O) → B)

theorem shiftedCenter_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (defFocus : targetFocusGraphDefinable O hO power S C focus)
    (c : (J → RV0 O) → K)
    (hc : DefinableRelation 𝓜 S.carrier (fun
      (t : SortedAssignment (CanonicalSort O) (RVVariables J)) (v : 𝕂) => v .vf 0 = c (t .rv))) :
    DefinableRelation 𝓜 S.carrier (fun
      (t : SortedAssignment (CanonicalSort O) (RVVariables (J ⊕ Unit))) (v : 𝕂) =>
      v .vf 0 = c (t .rv ∘ Sum.inl) -
        (pairedTargetTranslation O C focus).offset (t .rv ∘ Sum.inl) (t .rv (.inr ()))) := by
  let U := RVVariables (J ⊕ Unit)
  let V := MixedVariables 1 Empty
  let W := SumVariables U V
  let old : ∀ s, SumVariables (RVVariables J) V s → W s
    | .vf => Sum.elim PEmpty.elim Sum.inr
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl) Empty.elim
  let lab : ∀ s, SumVariables (RVVariables (Fin 1 ⊕ J)) V s → W s
    | .vf => Sum.elim PEmpty.elim Sum.inr
    | .rv => Sum.elim (Sum.elim (fun _ => .inl (.inr ())) (Sum.inl ∘ Sum.inl)) Empty.elim
  have ho := targetOffsetAtLabel_definable O hO power S C focus defFocus
  unfold DefinableRelation at hc ho
  exact definable_difference_of_field_graphs O hO power S F minusOne hm hF
    (fun t : SortedAssignment (CanonicalSort O) U => c (t .rv ∘ Sum.inl))
    (fun t => (pairedTargetTranslation O C focus).offset (t .rv ∘ Sum.inl) (t .rv (.inr ())))
    (hc.pullback_relabel old) (ho.pullback_relabel lab)

end GeneralizedEuler.Section5
