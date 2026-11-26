module

public import Section5.PreparedUnaryRVIndex
public import Section5.UnaryChainRules

/-! Preparing the field base transports the actual mixed set to the
pullback of the descended relative RV fibers. The old RV tuple is
unchanged and the full preparation history is retained. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {h m : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty
local notation "U" => RVVariables (Fin m)
local notation "Q" => RVVariables (Fin h)
local notation "V" => MixedVariables 1 (Fin h ⊕ Fin m)

variable (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)
local notation "line" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

@[expose] def preparedRelativePoint (a : SortedAssignment Z (SumVariables P U)) : SortedAssignment Z V
  | .vf => fun _ => ((line).map (a .vf (.inl 0))).1
  | .rv => Sum.elim (encodeHistory O cs.length ((line).label (a .vf (.inl 0))) ∘ e) (a .rv ∘ Sum.inr)

theorem preparedRelativePoint_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    DefinableRelation 𝓜 S.carrier (fun a b => preparedRelativePoint O hO power S cs e (m := m) a = b) := by
  let A := SumVariables P U
  let W := SumVariables A V
  let history : (s : TCsort) → MixedVariables 2 (HistoryIndex cs.length) s → W s
    | .vf => fun j => if j = 0 then .inl (.inl 0) else .inr 0
    | .rv => Sum.inr ∘ Sum.inl ∘ e.symm
  have prog := (preparationGraph_definable O hO power S F minusOne hm hF cs).pullback_relabel history
  have tags := SortedDefinableOver.iInter (fun i : Fin m =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := W) .rv (.inl (.inr i)) (.inr (.inr i)))
  unfold DefinableRelation
  convert prog.inter tags using 1
  ext w
  let input : SortedAssignment Z A := fun s => w s ∘ Sum.inl
  let output : SortedAssignment Z V := fun s => w s ∘ Sum.inr
  let x := input .vf (.inl 0)
  let y := output .vf 0
  let q := output .rv ∘ Sum.inl
  let T := line
  have h : T.label x = decodeHistory O cs.length (q ∘ e.symm) ↔
      encodeHistory O cs.length (T.label x) ∘ e = q := by
    constructor
    · intro h
      rw [h,encode_decode_history]
      funext i
      exact congrArg q (e.symm_apply_apply i)
    · intro h
      have h₀ : encodeHistory O cs.length (T.label x) = q ∘ e.symm := by
        funext i
        have ev := congrFun h (e.symm i)
        simpa only [Function.comp_apply,Equiv.apply_symm_apply] using ev
      rw [← h₀,decode_encode_history]
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change preparedRelativePoint O hO power S cs e input = output ↔
    T.map x = (y,decodeHistory O cs.length (q ∘ e.symm)) ∧ ∀ i, input .rv (.inr i) = output .rv (.inr i)
  constructor
  · intro eq
    refine ⟨Prod.ext (congrFun (congrFun eq .vf) 0) (h.2 ?_),fun i => congrFun (congrFun eq .rv) (.inr i)⟩
    funext i
    exact congrFun (congrFun eq .rv) (.inl i)
  · rintro ⟨eq,tag⟩
    funext s i
    cases s
    · rw [Subsingleton.elim i (0 : Fin 1)]
      exact congrArg Prod.fst eq
    · rcases i with i | i
      · exact congrFun (h.1 (congrArg Prod.snd eq)) i
      · exact tag i

theorem preparedRelativePoint_injective : Function.Injective (preparedRelativePoint O hO power S cs e (m := m)) := by
  intro a b eq
  let T := line
  let x := a .vf (.inl 0)
  let y := b .vf (.inl 0)
  have hist (i : HistoryIndex cs.length) : encodeHistory O cs.length (T.label x) i =
      encodeHistory O cs.length (T.label y) i := by
    have h := congrFun (congrFun eq .rv) (.inl (e.symm i))
    change (encodeHistory O cs.length (T.label x) ∘ e) (e.symm i) =
      (encodeHistory O cs.length (T.label y) ∘ e) (e.symm i) at h
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h
  have lead : T.label x = T.label y := by
    have h := congrArg (decodeHistory O cs.length) (funext hist)
    simpa only [decode_encode_history] using h
  have field : x = y := T.map_injective (Prod.ext (congrFun (congrFun eq .vf) 0) lead)
  funext s i
  cases s with
  | vf =>
    rcases i with i | i
    · rw [Subsingleton.elim i (0 : Fin 1)]
      exact field
    · exact i.elim
  | rv =>
    rcases i with i | i
    · exact i.elim
    · exact congrFun (congrFun eq .rv) (.inr i)

theorem prepared_relative_fiber_image
    (D : Set (SortedAssignment Z P)) (A : Set (SortedAssignment Z (SumVariables P U)))
    (constant : ∀ p p' : SortedAssignment Z P, (line).label (p .vf 0) = (line).label (p' .vf 0) →
      (p ∈ D ↔ p' ∈ D) ∧ ∀ u, appendAssignments p u ∈ A ↔ appendAssignments p' u ∈ A) :
    preparedRelativePoint O hO power S cs e '' onlyOver D A =
      {a : SortedAssignment Z V |
        let q := a .rv ∘ Sum.inl
        rv O (a .vf 0) = q (e.symm (lastIndex cs.length)) ∧
        appendAssignments (rvTupleAssignment q) (rvTupleAssignment (a .rv ∘ Sum.inr)) ∈
          descendFiberScheme (preparedHistoryRelation O hO power S cs e D) A} := by
  let T := line
  ext w
  let q := w .rv ∘ Sum.inl
  let u := rvTupleAssignment (w .rv ∘ Sum.inr)
  let history := decodeHistory O cs.length (q ∘ e.symm)
  have hlead : T.lead history = q (e.symm (lastIndex cs.length)) :=
    lead_decode_history O Subtype.val cs (q ∘ e.symm)
  constructor
  · rintro ⟨a,⟨mem,base⟩,eq⟩
    let p : SortedAssignment Z P := fun s => a s ∘ Sum.inl
    have tagEq : encodeHistory O cs.length (T.label (p .vf 0)) ∘ e = q := by
      funext i
      exact congrFun (congrFun eq .rv) (.inl i)
    have qTrans : T.label (p .vf 0) = history := by
      have he : encodeHistory O cs.length (T.label (p .vf 0)) = q ∘ e.symm := by
        funext i
        have h := congrFun tagEq (e.symm i)
        simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h
      have h := congrArg (decodeHistory O cs.length) he
      rwa [decode_encode_history] at h
    have field : (T.map (p .vf 0)).1 = w .vf 0 := congrFun (congrFun eq .vf) 0
    have uEq : u = (fun s => a s ∘ Sum.inr) := by
      funext s i
      cases s
      · exact i.elim
      · exact (congrFun (congrFun eq .rv) (.inr i)).symm
    have aEq : appendAssignments p u = a := by
      rw [uEq]
      funext s i
      cases i <;> rfl
    exact ⟨(congrArg (rv O) field).symm.trans ((T.leading _).trans ((congrArg T.lead qTrans).trans hlead)),
      p,⟨base,qTrans⟩,aEq.symm ▸ mem⟩
  · rintro ⟨lead,p,⟨hp,qTrans⟩,mem⟩
    let x := w .vf 0 + T.offset history
    let r : SortedAssignment Z P := fieldTupleAssignment (fun _ => x)
    have hx : T.label x = T.label (p .vf 0) := by
      apply T.constant_label
      rw [qTrans]
      change rv O (w .vf 0 + T.offset history - T.offset history) = T.lead history
      rw [add_sub_cancel_right,hlead]
      exact lead
    have valid := constant r p hx
    let a := appendAssignments r u
    have ma : a ∈ onlyOver D A := ⟨(valid.2 u).2 mem,(valid.1).2 hp⟩
    refine ⟨a,ma,?_⟩
    have labels : encodeHistory O cs.length (T.label x) ∘ e = q := by
      rw [hx,qTrans]
      change encodeHistory O cs.length (decodeHistory O cs.length (q ∘ e.symm)) ∘ e = q
      rw [encode_decode_history]
      funext i
      exact congrArg q (e.symm_apply_apply i)
    funext s i
    cases s
    · rw [Subsingleton.elim i (0 : Fin 1)]
      change x - T.offset (T.label x) = w .vf 0
      rw [hx,qTrans]
      exact add_sub_cancel_right _ _
    · rcases i with i | i
      · exact congrFun labels i
      · rfl

end GeneralizedEuler.Section5
