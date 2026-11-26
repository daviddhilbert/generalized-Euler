module

public import Section5.GradedLiftTotalBijections
public import Section5.RelativeRVGluing
public import Section5.ZeroBlowupObject

/-! Relative RV isomorphism schemes glue over their full index.
The gluing preserves the chosen head start. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h m n : ℕ}

local notation "P" => RVVariables (Fin h)
local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin n)

private def splitRVAssignment {r : ℕ} (x : Fin (h+r) → X .rv) :
    SortedAssignment X (SumVariables P (RVVariables (Fin r))) :=
  appendAssignments (rvTupleAssignment (x ∘ rvHead)) (rvTupleAssignment (x ∘ rvTail))

private def splitRVEquiv {r : ℕ} :
    (Fin (h+r) → X .rv) ≃ SortedAssignment X (SumVariables P (RVVariables (Fin r))) where
  toFun := splitRVAssignment
  invFun u := u .rv ∘ finSumFinEquiv.symm
  left_inv x := by
    funext i
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    change splitRVAssignment x .rv (finSumFinEquiv.symm (finSumFinEquiv i)) = x (finSumFinEquiv i)
    rw [Equiv.symm_apply_apply]
    cases i <;> rfl
  right_inv u := by
    funext s i
    rcases i with i | i
    · cases s
      · exact i.elim
      · exact congrArg (u .rv) (finSumFinEquiv.symm_apply_apply (.inl i))
    · cases s
      · exact i.elim
      · exact congrArg (u .rv) (finSumFinEquiv.symm_apply_apply (.inr i))

private theorem splitRV_mem {r : ℕ} (B : Set (Fin h → X .rv))
    (D : Set (SortedAssignment X (SumVariables P (RVVariables (Fin r)))))
    (t : Fin (h+r) → X .rv) :
    t ∈ gluedRVTags B D ↔ splitRVAssignment t ∈ onlyOver {p : SortedAssignment X P | p .rv ∈ B} D := and_comm

theorem gluedRVTags_equiv_of_fiber_schemes
    {B : Set (Fin h → X .rv)} (defB : isRVSet M S B)
    {A : Set (SortedAssignment X (SumVariables P U))} {D : Set (SortedAssignment X (SumVariables P V))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defG : SortedDefinableOver M S.carrier G)
    (valid : ∀ p : SortedAssignment X P, p .rv ∈ B → FiberBijectionScheme A D G p) :
    ∃ e : gluedRVTags B A ≃ gluedRVTags B D,
      SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)) ∧
      ∀ a : gluedRVTags B A, (e a).val ∘ rvHead = a.val ∘ rvHead := by
  let T : Set (SortedAssignment X P) := {p | p .rv ∈ B}
  obtain ⟨g,base,graph⟩ := total_bijection_of_scheme_over T defB A D defG valid
  let l : gluedRVTags B A ≃ onlyOver T A :=
    splitRVEquiv.subtypeEquiv (splitRV_mem B A)
  let r : gluedRVTags B D ≃ onlyOver T D :=
    splitRVEquiv.subtypeEquiv (splitRV_mem B D)
  let e := l.trans (g.trans r.symm)
  refine ⟨e,rvGraph_of_relation ?_,?_⟩
  · let R := SumVariables (RVVariables (Fin (h+m))) (RVVariables (Fin (h+n)))
    let relabel : (s : TCsort) → SumVariables (SumVariables P U) (SumVariables P V) s → R s
      | .vf => Sum.elim (Sum.elim PEmpty.elim PEmpty.elim) (Sum.elim PEmpty.elim PEmpty.elim)
      | .rv => Sum.map finSumFinEquiv finSumFinEquiv
    unfold DefinableRelation at graph ⊢
    convert graph.pullback_relabel relabel using 1
    ext w
    let a := w .rv ∘ Sum.inl
    let b := w .rv ∘ Sum.inr
    have leftEq : (fun s => (w s ∘ relabel s) ∘ Sum.inl) = splitRVAssignment a := by
      funext s i
      cases s with
      | vf => rcases i with i | i <;> exact i.elim
      | rv => cases i <;> rfl
    have rightEq : (fun s => (w s ∘ relabel s) ∘ Sum.inr) = splitRVAssignment b := by
      funext s i
      cases s with
      | vf => rcases i with i | i <;> exact i.elim
      | rv => cases i <;> rfl
    change (∃ x : gluedRVTags B A, x.val = a ∧ (e x).val = b) ↔
      ∃ hA : (fun s => (w s ∘ relabel s) ∘ Sum.inl) ∈ onlyOver T A,
        (g ⟨_,hA⟩).val = (fun s => (w s ∘ relabel s) ∘ Sum.inr)
    rw [leftEq,rightEq]
    constructor
    · rintro ⟨x,hx,he⟩
      have hEq := congrArg (fun y => (splitRVEquiv (h := h) (r := n)) y) he
      change splitRVEquiv (r := n) (r.symm (g (l x))).val = splitRVAssignment b at hEq
      rw [show splitRVEquiv (r := n) (r.symm (g (l x))).val = (g (l x)).val from
        congrArg Subtype.val (r.apply_symm_apply (g (l x)))] at hEq
      have hx' : (l x).val = splitRVAssignment a := congrArg splitRVAssignment hx
      have ha : splitRVAssignment a ∈ onlyOver T A := hx' ▸ (l x).property
      have lx : l x = ⟨splitRVAssignment a,ha⟩ := Subtype.ext hx'
      exact ⟨ha,lx ▸ hEq⟩
    · rintro ⟨ha,eq⟩
      let x : gluedRVTags B A := ⟨a,(splitRV_mem B A a).2 ha⟩
      refine ⟨x,rfl,?_⟩
      apply (splitRVEquiv (h := h) (r := n)).injective
      change (r (r.symm (g (l x)))).val = splitRVAssignment b
      rw [r.apply_symm_apply]
      exact eq
  · intro a
    have ha := (base (l a))
    have hp : (r (e a)).val = (g (l a)).val :=
      congrArg Subtype.val (r.apply_symm_apply (g (l a)))
    change (fun s => (g (l a)).val s ∘ Sum.inl) = (fun s => (l a).val s ∘ Sum.inl) at ha
    rw [← hp] at ha
    exact congrFun ha .rv

end GeneralizedEuler.Section5
