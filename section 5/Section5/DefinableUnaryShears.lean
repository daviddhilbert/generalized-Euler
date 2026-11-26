module

public import Section5.RelativeUnaryShears
public import Section5.FixedBaseCenters
public import Section5.DefinableRelations
public import Section5.VerticalCenters
import all Section5.RelativeUnaryShears

/-! The three shears in a coordinate transposition have graphs over
the original base and preserve every RV coordinate. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n : ℕ} {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Vars" => MixedVariables n I

theorem fieldSubtractionUpdates_definable
    (i j : Fin n) (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) (reflect : Bool) :
    DefinableRelation 𝓜 S.carrier (fun
      (x y : SortedAssignment (CanonicalSort O) Vars) =>
      Function.update (x .vf) i (if reflect then x .vf j - x .vf i else x .vf i - x .vf j) = y .vf ∧
        x .rv = y .rv) := by
  let V := SumVariables Vars Vars
  let W := WithBase S.carrier V
  let x (a : Fin n) : SortedTerm L E W .vf := .var (.inr (.inl a))
  let diff := if reflect then subVF F (x j) (x i) else subVF F (x i) (x j)
  let term (a : Fin n) := if a = i then diff else x a
  have field := SortedDefinableOver.iInter (fun k : Fin n =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := V) .vf (.inr k) (term k))
  have tags := SortedDefinableOver.iInter (fun k : I =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := V) .rv (.inl k) (.inr k))
  unfold DefinableRelation
  convert field.inter tags using 1
  ext w
  let a := w .vf ∘ Sum.inl
  let b := w .vf ∘ Sum.inr
  let values : (s : TCsort) → W s → CanonicalSort O s := fun s => Sum.elim Subtype.val (w s)
  let u := Function.update a i (if reflect then a j - a i else a i - a j)
  have diffVal : diff.realize 𝓜 values = (if reflect then a j - a i else a i - a j) := by
    cases reflect <;> simp only [diff,Bool.false_eq_true,ite_false,ite_true,
      eval_subVF O hO power F minusOne hm hF] <;> rfl
  have value (k : Fin n) : (term k).realize 𝓜 values = u k := by
    by_cases e : k = i
    · subst k
      simpa only [term,ite_true,Function.update_self,u] using diffVal
    · simp only [term,ite_eq_right e,u,Function.update_of_ne e]
      rfl
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change (u = b ∧ w .rv ∘ Sum.inl = w .rv ∘ Sum.inr) ↔
    (∀ k, b k = (term k).realize 𝓜 values) ∧ (∀ k, w .rv (.inl k) = w .rv (.inr k))
  simp only [value]
  exact ⟨fun ⟨h,g⟩ => ⟨fun k => congrFun h.symm k,fun k => congrFun g k⟩,
    fun ⟨h,g⟩ => ⟨(funext h).symm,funext g⟩⟩

theorem fieldAddUpdate_definable
    (i j : Fin n) (ne : j ≠ i) (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    DefinableRelation 𝓜 S.carrier (fun
      (x y : SortedAssignment (CanonicalSort O) Vars) =>
      addCoordinate i j ne (x .vf) = y .vf ∧ x .rv = y .rv) := by
  have h := (fieldSubtractionUpdates_definable O hO power S (I := I) i j F minusOne hm hF false).transpose
  apply h.congr
  intro x y
  change ((addCoordinate i j ne).symm (y .vf) = x .vf ∧ y .rv = x .rv) ↔
    addCoordinate i j ne (x .vf) = y .vf ∧ x .rv = y .rv
  exact and_congr ⟨fun e => ((addCoordinate i j ne).symm_apply_eq.1 e).symm,
    fun e => (addCoordinate i j ne).symm_apply_eq.2 e.symm⟩ eq_comm

end GeneralizedEuler.Section5
