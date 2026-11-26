module

public import Section5.DefinableTotalFunctions
public import Section5.LiftBoundaryDimension

/-! Complete a partial RV label by the zero tuple, without changing
any value on the definable domain. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

@[expose] def rvAssignment {X : TCsort → Type z} {I : Type} (rv : I → X .rv) :
    SortedAssignment X (RVVariables I)
  | .vf => PEmpty.elim
  | .rv => rv

theorem rvAssignment_eta {X : TCsort → Type z} {I : Type}
    (a : SortedAssignment X (RVVariables I)) : rvAssignment (a .rv) = a := by
  funext s i
  cases s
  · exact i.elim
  · rfl

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {P : TCsort → Type} {m : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "R" => RVVariables (Fin m)

theorem definable_total_rv_label
    (F : SortedAssignment Z P → SortedAssignment Z R → Prop)
    (defF : DefinableRelation 𝓜 S.carrier F)
    (unique : ∀ a r s, F a r → F a s → r = s) :
    ∃ label : SortedAssignment Z P → Fin m → RV0 O,
      (∀ a r, F a r → label a = r .rv) ∧
      DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment Z P) (r : SortedAssignment Z R) =>
        label a = r .rv) := by
  let W := SumVariables P R
  let z : SortedAssignment Z R := rvTupleAssignment (fun _ => 0)
  have each := SortedDefinableOver.iInter (fun i : Fin m => SortedDefinableOver.coordinate_eq_term
    (M := 𝓜) (A := S.carrier) (Var := W) .rv (.inr i) rvZeroTerm)
  have const : DefinableRelation 𝓜 S.carrier (fun (_ : SortedAssignment Z P) (b : SortedAssignment Z R) =>
      z = b) := by
    unfold DefinableRelation
    convert each using 1
    ext a
    have ev : (rvZeroTerm : SortedTerm L E (WithBase S.carrier W) .rv).realize 𝓜
        (fun s => Sum.elim Subtype.val (a s)) = 0 := realize_rvZeroTerm O hO power _
    simp only [Set.mem_iInter]
    change z = (fun s => a s ∘ Sum.inr) ↔ ∀ i : Fin m, a .rv (.inr i) =
      (rvZeroTerm : SortedTerm L E (WithBase S.carrier W) .rv).realize 𝓜 (fun s => Sum.elim Subtype.val (a s))
    rw [ev]
    constructor
    · intro e i
      exact (congrFun (congrFun e .rv) i).symm
    · intro e
      funext s i
      cases s
      · exact i.elim
      · exact (e i).symm
  obtain ⟨f,ev,df⟩ := definable_total_function F defF unique z const
  refine ⟨fun a => f a .rv,fun a r h => congrFun (ev a r h) .rv,df.congr ?_⟩
  intro a r
  exact ⟨fun h => congrFun h .rv,fun h => by funext s i; cases s; exact i.elim; exact congrFun h i⟩

end GeneralizedEuler.Section5
