module

public import Section5.BlowupFocusChoice
public import Section5.ScaleTerms

/-! Fixed-base graphs of the translation and multiplier construction.
The focus may be chosen by a definable function of the other VF coordinates. -/

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
  {n k : ℕ} {I : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def updateBlowupPoint (j : Fin n)
    (x : SortedAssignment (CanonicalSort O) (MixedVariables n I)) (c : K) :
    SortedAssignment (CanonicalSort O) (MixedVariables n (I ⊕ Unit))
  | .vf => Function.update (x .vf) j (x .vf j - c)
  | .rv => Sum.elim (x .rv) (fun _ => rv O ((x .vf j - c) / c))

/-- With a named focus variable, the output is described by field
subtraction, one new RV term, and equality of all unchanged coordinates. -/
private theorem updateBlowupGraph_definable [Finite I] (j : Fin n)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    let V := SumVariables (MixedVariables n I) (MixedVariables n (I ⊕ Unit))
    let W := SumVariables V (MixedVariables 1 Empty)
    SortedDefinableOver 𝓜 S.carrier
      {w : SortedAssignment (CanonicalSort O) W |
        updateBlowupPoint O j (fun s => w s ∘ Sum.inl ∘ Sum.inl) (w .vf (.inr 0)) =
          (fun s => w s ∘ Sum.inl ∘ Sum.inr)} := by
  intro V W
  let P := WithBase S.carrier W
  let focus : SortedTerm L E P .vf := .var (.inr (.inr 0))
  let input (i : Fin n) : SortedTerm L E P .vf := .var (.inr (.inl (.inl i)))
  let shift := subVF F (input j) focus
  let y (i : Fin n) := if i = j then shift else input i
  let s := rvOfVF (mulVF F shift (invVF F focus))
  have field := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
      .vf (.inl (.inr i)) (y i))
  have rvKeep := SortedDefinableOver.iInter (fun i : I =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := W)
      .rv (.inl (.inr (.inl i))) (.inl (.inl i)))
  have multiplier := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inl (.inr (.inr ()))) s
  convert field.inter (rvKeep.inter multiplier) using 1
  ext w
  let a : SortedAssignment (CanonicalSort O) (MixedVariables n I) :=
    fun s => w s ∘ Sum.inl ∘ Sum.inl
  let b : SortedAssignment (CanonicalSort O) (MixedVariables n (I ⊕ Unit)) :=
    fun s => w s ∘ Sum.inl ∘ Sum.inr
  let c := w .vf (.inr 0)
  let v : ∀ s, P s → CanonicalSort O s := fun s => Sum.elim Subtype.val (w s)
  have hField (i : Fin n) : (y i).realize 𝓜 v = (updateBlowupPoint O j a c) .vf i := by
    by_cases hi : i = j
    · subst i
      rw [show y j = shift from ite_eq_left rfl]
      change (subVF F (input j) focus).realize 𝓜 v = _
      rw [eval_subVF O hO power F minusOne hm hF]
      change a .vf j - c = Function.update (a .vf) j (a .vf j - c) j
      rw [Function.update_self]
    · dsimp only [y]
      rw [ite_eq_right hi]
      change a .vf i = Function.update (a .vf) j (a .vf j - c) i
      exact (Function.update_of_ne hi _ _).symm
  have hMul : s.realize 𝓜 v = rv O ((a .vf j - c) / c) := by
    dsimp only [s,shift]
    rw [eval_rvOfVF O hO power,eval_mulVF O hO power F minusOne hm hF,
      eval_subVF O hO power F minusOne hm hF,eval_invVF O hO power F minusOne hm hF,
      div_eq_mul_inv]
    rfl
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change updateBlowupPoint O j a c = b ↔
    (∀ i, b .vf i = (y i).realize 𝓜 v) ∧
      (∀ i, b .rv (.inl i) = a .rv i) ∧ b .rv (.inr ()) = s.realize 𝓜 v
  constructor
  · intro eq
    exact ⟨fun i => ((congrFun (congrFun eq .vf) i).symm.trans (hField i).symm),
      fun i => (congrFun (congrFun eq .rv) (.inl i)).symm,
      (congrFun (congrFun eq .rv) (.inr ())).symm.trans hMul.symm⟩
  · rintro ⟨hf,hr,hs⟩
    funext t i
    cases t with
    | vf => exact (hField i).symm.trans (hf i).symm
    | rv =>
      cases i with
      | inl i => exact (hr i).symm
      | inr e =>
        cases e
        exact hMul.symm.trans hs.symm

/-- The graph of a relative elementary blowup is definable over the
original base when the focus graph on the projected field tuple is. -/
theorem relative_blowup_graph_definable [Finite I] (p : Fin k → Fin n) (j : Fin n)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (A : Set (SortedAssignment (CanonicalSort O) (MixedVariables n I)))
    (hA : SortedDefinableOver 𝓜 S.carrier A)
    (D : Set (fieldAssignment k (CanonicalSort O))) (c : D → K)
    (hD : ∀ a ∈ A, projectFields p (fieldTupleAssignment (a .vf)) ∈ D)
    (cDef : DefinableRelation 𝓜 S.carrier (fun a (b : fieldAssignment 1 (CanonicalSort O)) =>
      ∃ ha : a ∈ D, c ⟨a,ha⟩ = b .vf 0)) :
    DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ A,
      updateBlowupPoint O j a (c ⟨projectFields p (fieldTupleAssignment (a .vf)),hD a ha⟩) = b) := by
  let V := SumVariables (MixedVariables n I) (MixedVariables n (I ⊕ Unit))
  let W := SumVariables V (MixedVariables 1 Empty)
  let rename : ∀ s, SumVariables (MixedVariables n Empty) (MixedVariables 1 Empty) s → W s
    | .vf => Sum.map Sum.inl id
    | .rv => Sum.elim Empty.elim Empty.elim
  have hc := (projectFields_definable p).comp cDef
  unfold DefinableRelation at hc
  have fresh := (hc.pullback_relabel rename).inter (updateBlowupGraph_definable O hO power S j F minusOne hm hF)
  have all := (hA.pullback_relabel (fun s => (Sum.inl : MixedVariables n I s → V s))).inter
    (definable_project_mixed fresh)
  unfold DefinableRelation
  convert all using 1
  ext v
  let a : SortedAssignment (CanonicalSort O) (MixedVariables n I) := fun s => v s ∘ Sum.inl
  let b : SortedAssignment (CanonicalSort O) (MixedVariables n (I ⊕ Unit)) := fun s => v s ∘ Sum.inr
  let ar := projectFields p (fieldTupleAssignment (a .vf))
  let x (y : fieldAssignment 1 (CanonicalSort O)) : fieldAssignment n (CanonicalSort O) :=
    fun s => (Sum.elim (v s) (y s) ∘ rename s) ∘ Sum.inl
  let z (y : fieldAssignment 1 (CanonicalSort O)) : fieldAssignment 1 (CanonicalSort O) :=
    fun s => (Sum.elim (v s) (y s) ∘ rename s) ∘ Sum.inr
  have hX (y) : x y = fieldTupleAssignment (a .vf) := fieldAssignment_ext (fun _ => rfl)
  have hZ (y) : z y = y := fieldAssignment_ext (fun _ => rfl)
  change (∃ ha : a ∈ A, updateBlowupPoint O j a (c ⟨ar,hD a ha⟩) = b) ↔
    a ∈ A ∧ ∃ y, (∃ d, projectFields p (x y) = d ∧ ∃ hd : d ∈ D, c ⟨d,hd⟩ = z y .vf 0) ∧
      updateBlowupPoint O j a (y .vf 0) = b
  simp only [hX,hZ, ← show ar = projectFields p (fieldTupleAssignment (a .vf)) from rfl]
  constructor
  · rintro ⟨ha,he⟩
    exact ⟨ha,fieldTupleAssignment (fun _ => c ⟨ar,hD a ha⟩),⟨ar,rfl,hD a ha,rfl⟩,he⟩
  · rintro ⟨ha,y,⟨_,rfl,hd,he⟩,hy⟩
    refine ⟨ha,?_⟩
    change updateBlowupPoint O j a (c ⟨ar,hd⟩) = b
    rw [he]
    exact hy

end GeneralizedEuler.Section5
