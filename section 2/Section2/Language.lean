module

public import Mathlib.ModelTheory.Syntax

/-! The sorts and symbols of the reviewed language in §2.2. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w

/-- The two real sorts. The second sort includes its distinguished zero. -/
inductive TCsort
  | vf
  | rv
  deriving DecidableEq

variable (L : Language.{u, v}) (Exponent : Type w)

/-- A typed signature for the functions of the two-sorted language.
The two distinguished RV constants also serve as the residue zero and one.
The interpretation of residue symbols is total on RV, with the extension
by zero specified in §2.2. -/
inductive FunctionSymbol : List TCsort → TCsort → Type (max u w)
  | vf {n : ℕ} (f : L.Functions n) : FunctionSymbol (List.replicate n .vf) .vf
  | rvZero : FunctionSymbol [] .rv
  | rvOne : FunctionSymbol [] .rv
  | rvMul : FunctionSymbol [.rv, .rv] .rv
  | rvInv : FunctionSymbol [.rv] .rv
  | residue {n : ℕ} (f : L.Functions n) : FunctionSymbol (List.replicate n .rv) .rv
  | power (exponent : Exponent) : FunctionSymbol [.rv] .rv
  | rv : FunctionSymbol [.vf] .rv

/-- The residue field has its inherited RV order. The ordered functional
presentation of `T` uses only order as a primitive relation. -/
inductive RelationSymbol : List TCsort → Type v
  | vf {n : ℕ} (r : L.Relations n) : RelationSymbol (List.replicate n .vf)
  | residueNonzero : RelationSymbol [.rv]
  | rvLE : RelationSymbol [.rv, .rv]

end GeneralizedEuler.Section2
