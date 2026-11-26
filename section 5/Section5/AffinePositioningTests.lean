module

public import Section5.PositioningBranchSchemes
public import Section5.FixedBaseCenters
public import Section2.RVMonomials

/-! RV-affineness with a specified slope is a first-order test for
a unary positioning graph on a definable branch. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {P : TCsort → Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty
local notation "R" => RVVariables (Fin 1)
local notation "V" => SumVariables P R
local notation "PVV" => SumVariables (SumVariables P U) U

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[expose] def affinePositioningSlope
    (G : Set (SortedAssignment Z PVV)) (p : SortedAssignment Z P) (u : RV0 O) : Prop :=
  ∀ (a b c d : SortedAssignment Z U),
    appendAssignments (appendAssignments p a) b ∈ G →
    appendAssignments (appendAssignments p c) d ∈ G →
      rv O (b .vf 0 - d .vf 0) = u * rv O (a .vf 0 - c .vf 0)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem affine_positioning_slope_unique
    {G : Set (SortedAssignment Z PVV)} {p : SortedAssignment Z P}
    {a b c d : SortedAssignment Z U}
    (ha : appendAssignments (appendAssignments p a) b ∈ G)
    (hc : appendAssignments (appendAssignments p c) d ∈ G)
    (different : a .vf 0 ≠ c .vf 0) {u v : RV0 O}
    (hU : affinePositioningSlope O G p u) (hV : affinePositioningSlope O G p v) : u = v := by
  have e := (hU a b c d ha hc).symm.trans (hV a b c d ha hc)
  have nz : rv O (a .vf 0 - c .vf 0) ≠ 0 := (rv_eq_zero_iff O).not.mpr (sub_ne_zero.mpr different)
  rw [mul_comm (G := RV0 O) u,mul_comm (G := RV0 O) v] at e
  exact rv_mul_left_cancel O nz e

theorem affinePositioningSlope_definable
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {G : Set (SortedAssignment Z PVV)} (defG : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier {p : SortedAssignment Z V |
      affinePositioningSlope O G (fun s => p s ∘ Sum.inl) (p .rv (.inr 0))} := by
  let T := SumVariables (SumVariables (SumVariables (SumVariables V U) U) U) U
  let pVars (s : TCsort) : P s → T s := Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl
  let aVars (s : TCsort) : U s → T s := Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr
  let bVars (s : TCsort) : U s → T s := Sum.inl ∘ Sum.inl ∘ Sum.inr
  let cVars (s : TCsort) : U s → T s := Sum.inl ∘ Sum.inr
  let dVars (s : TCsort) : U s → T s := Sum.inr
  let left (s : TCsort) : PVV s → T s := Sum.elim (Sum.elim (pVars s) (aVars s)) (bVars s)
  let right (s : TCsort) : PVV s → T s := Sum.elim (Sum.elim (pVars s) (cVars s)) (dVars s)
  let W := WithBase S.carrier T
  let field (a : U .vf → T .vf) : SortedTerm L E W .vf := .var (.inr (a 0))
  let slope : SortedTerm L E W .rv := .var (.inr (.inl (.inl (.inl (.inl (.inr 0))))))
  let lhs := rvOfVF (subVF F (field (bVars .vf)) (field (dVars .vf)))
  let rhs := rvMulTerm slope (rvOfVF (subVF F (field (aVars .vf)) (field (cVars .vf))))
  let Same := {w : SortedAssignment Z T |
    lhs.realize 𝓜 (fun s => Sum.elim Subtype.val (w s)) = rhs.realize 𝓜 (fun s => Sum.elim Subtype.val (w s))}
  have defSame : SortedDefinableOver 𝓜 S.carrier Same := ⟨.equal lhs rhs,fun _ => Iff.rfl⟩
  have both := (defG.pullback_relabel left).inter (defG.pullback_relabel right)
  have valid := definable_forall_assignments (definable_forall_assignments
    (definable_forall_assignments (definable_forall_assignments (both.compl.union defSame))))
  convert valid using 1
  ext w
  let p : SortedAssignment Z P := fun s => w s ∘ Sum.inl
  let t := w .rv (.inr 0)
  simp only [affinePositioningSlope,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_union]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun c => forall_congr' fun d => ?_
  let all : SortedAssignment Z T := appendAssignments (appendAssignments (appendAssignments (appendAssignments w a) b) c) d
  have leftEq : (fun s => all s ∘ left s) = appendAssignments (appendAssignments p a) b := by
    funext s i
    rcases i with (i | i) | i <;> rfl
  have rightEq : (fun s => all s ∘ right s) = appendAssignments (appendAssignments p c) d := by
    funext s i
    rcases i with (i | i) | i <;> rfl
  let v : (s : TCsort) → W s → Z s := fun s => Sum.elim Subtype.val (all s)
  change (appendAssignments (appendAssignments p a) b ∈ G →
    appendAssignments (appendAssignments p c) d ∈ G →
      rv O (b .vf 0 - d .vf 0) = t * rv O (a .vf 0 - c .vf 0)) ↔
      (¬ ((fun s => all s ∘ left s) ∈ G ∧ (fun s => all s ∘ right s) ∈ G) ∨
        lhs.realize 𝓜 v = rhs.realize 𝓜 v)
  rw [leftEq,rightEq]
  have l : lhs.realize 𝓜 v = rv O (b .vf 0 - d .vf 0) := by
    dsimp only [lhs]
    rw [eval_rvOfVF O hO power,eval_subVF O hO power F minusOne hm hF]
    rfl
  have r : rhs.realize 𝓜 v = t * rv O (a .vf 0 - c .vf 0) := by
    dsimp only [rhs]
    rw [realize_rvMulTerm O hO power,eval_rvOfVF O hO power,eval_subVF O hO power F minusOne hm hF]
    rfl
  rw [l,r]
  tauto

end GeneralizedEuler.Section5
