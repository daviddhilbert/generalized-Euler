module

public import Section5.FixedBaseCenters

/-! Field terms for the coordinate scalings in the lifting proof. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

local notation "M" => canonicalStructure (L := L) O hO power

variable (F : FieldTerms (convexLanguage L)) {W : TCsort → Type z}

def mulVF (a b : SortedTerm L E W .vf) : SortedTerm L E W .vf :=
  liftValuedTerm (Fin.cases a (fun _ => b)) F.mul

def invVF (a : SortedTerm L E W .vf) : SortedTerm L E W .vf :=
  liftValuedTerm (fun _ => a) F.inv

def scaleVF (a b x : SortedTerm L E W .vf) : SortedTerm L E W .vf :=
  mulVF F (mulVF F b x) (invVF F a)

variable (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

include hm hF in
set_option linter.style.haveILetI false in
theorem eval_mulVF (v : ∀ s, W s → CanonicalSort O s) (a b : SortedTerm L E W .vf) :
    (mulVF F a b).realize M v = a.realize M v * b.realize M v := by
  letI := convexStructure O L
  have h := realize_liftValuedTerm M (recoveredRing M minusOne) (Fin.cases a (fun _ => b)) F.mul v
  rw [recoveredValuedStructure_canonical_eq O hO power minusOne hm] at h
  rw [mulVF, h, hF.mul]
  rfl

include hm hF in
set_option linter.style.haveILetI false in
theorem eval_invVF (v : ∀ s, W s → CanonicalSort O s) (a : SortedTerm L E W .vf) :
    (invVF F a).realize M v = (a.realize M v)⁻¹ := by
  letI := convexStructure O L
  have h := realize_liftValuedTerm M (recoveredRing M minusOne) (fun _ => a) F.inv v
  rw [recoveredValuedStructure_canonical_eq O hO power minusOne hm] at h
  rw [invVF, h, hF.inv]

include hm hF in
theorem eval_scaleVF (v : ∀ s, W s → CanonicalSort O s) (a b x : SortedTerm L E W .vf) :
    (scaleVF F a b x).realize M v = b.realize M v * x.realize M v / a.realize M v := by
  rw [scaleVF, eval_mulVF O hO power F minusOne hm hF, eval_mulVF O hO power F minusOne hm hF,
    eval_invVF O hO power F minusOne hm hF, div_eq_mul_inv]

end GeneralizedEuler.Section5
