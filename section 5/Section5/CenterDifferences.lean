module

public import Section5.VerticalCenters
public import Section2.SortedDefinability

/-! The finite tuple of ordered center differences, prepared in the
complementary field coordinates before running the head translations. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n : ℕ} {J : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Include zero among the initial centers so the same difference tuple
also controls the first translation. -/
@[expose] def centerValues
    (terms : J → SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf)
    (y : Fin n → K) : Option J → K
  | none => 0
  | some i => (terms i).realize 𝓜 (centerAssignment O hO power S y)

set_option linter.style.haveILetI false in
/-- The leading terms of all ordered differences form a fixed-base
definable tuple on the complementary VF variables. -/
theorem center_differences_definable [Finite J]
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (terms : J → SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf) :
    SortedDefinableOver 𝓜 S.carrier
      {a : ∀ s, MixedVariables n (Option J × Option J) s → CanonicalSort O s |
        ∀ i j, a .rv (i,j) = rv O (centerValues O hO power S terms (a .vf) i -
          centerValues O hO power S terms (a .vf) j)} := by
  letI := convexStructure O L
  let V := MixedVariables n (Option J × Option J)
  let rename : ∀ s, WithBase S.carrier (MixedVariables n Empty) s → WithBase S.carrier V s
    | .vf => id
    | .rv => Sum.map id Empty.elim
  let zero : SortedTerm L E (WithBase S.carrier V) .vf :=
    liftValuedTerm Empty.elim F.zero
  let center (i : Option J) : SortedTerm L E (WithBase S.carrier V) .vf :=
    i.elim zero (fun j => (terms j).relabel rename)
  have eval_center (a : ∀ s, V s → CanonicalSort O s) (i : Option J) :
      (center i).realize 𝓜 (fun s => Sum.elim Subtype.val (a s)) =
        centerValues O hO power S terms (a .vf) i := by
    let v (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → CanonicalSort O s) (a s)
    cases i with
    | none =>
      have h := realize_liftValuedTerm 𝓜 (recoveredRing 𝓜 minusOne)
        (Empty.elim : Empty → SortedTerm L E (WithBase S.carrier V) .vf) F.zero v
      rw [recoveredValuedStructure_canonical_eq O hO power minusOne hm] at h
      change zero.realize 𝓜 v = 0
      rw [h]
      have he : (fun i : Empty => (Empty.elim i : SortedTerm L E (WithBase S.carrier V) .vf).realize 𝓜 v) =
          (Empty.elim : Empty → K) := Subsingleton.elim _ _
      rw [he]
      exact hF.zero
    | some i =>
      change ((terms i).relabel rename).realize 𝓜 v = _
      rw [SortedTerm.realize_relabel]
      have h : (fun s => v s ∘ rename s) = centerAssignment O hO power S (a .vf) := by
        funext s j
        cases s with
        | vf => rfl
        | rv => rcases j with c | j; exacts [rfl, j.elim]
      rw [h]
      rfl
  let term (p : Option J × Option J) := rvOfVF (subVF F (center p.1) (center p.2))
  let test (p : Option J × Option J) : Set (∀ s, V s → CanonicalSort O s) :=
    {a | a .rv p = (term p).realize 𝓜 (fun s => Sum.elim Subtype.val (a s))}
  have htest (p) : SortedDefinableOver 𝓜 S.carrier (test p) :=
    SortedDefinableOver.coordinate_eq_term .rv p (term p)
  have h := SortedDefinableOver.iInter htest
  convert h using 1
  ext a
  simp only [Set.mem_iInter, test, Set.mem_ofPred_eq, term, eval_rvOfVF O hO power,
    eval_subVF O hO power F minusOne hm hF, eval_center]
  exact ⟨fun h p => h p.1 p.2, fun h i j => h (i,j)⟩

end GeneralizedEuler.Section5
