module

public import Section5.FirstTwoFieldSlices
public import Section5.FieldwiseContractionInduction

/-! A first-pair exchange over each fixed complementary field tuple
implies the same exchange with any common tail of contractions. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

namespace RetainedFieldFamily

theorem firstTwoSlice_swap (A : RetainedFieldFamily M S (n+2) k)
    (p : fieldAssignment n (CanonicalSort O)) :
    (A.permuteVF (Equiv.swap 0 1)).firstTwoSlice p = (A.firstTwoSlice p).permuteVF (Equiv.swap 0 1) := by
  have swapFields (x : Fin 2 → K) :
      (Fin.cons (x 0) (Fin.cons (x 1) (p .vf))) ∘ (Equiv.swap (0 : Fin (n+2)) 1).symm =
        Fin.cons (x ((Equiv.swap (0 : Fin 2) 1).symm 0))
          (Fin.cons (x ((Equiv.swap (0 : Fin 2) 1).symm 1)) (p .vf)) := by
    have e₀ (m : ℕ) : (Equiv.swap (0 : Fin (m+2)) 1).symm 0 = 1 := Equiv.swap_apply_left _ _
    have e₁ (m : ℕ) : (Equiv.swap (0 : Fin (m+2)) 1).symm 1 = 0 := Equiv.swap_apply_right _ _
    rw [e₀ 0,e₁ 0]
    let fields : Fin (n+2) → K := Fin.cons (x 0) (Fin.cons (x 1) (p .vf))
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change fields ((Equiv.swap (0 : Fin (n+2)) 1).symm 0) = x 1
      rw [e₀ n]
      rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · change fields ((Equiv.swap (0 : Fin (n+2)) 1).symm 1) = x 0
        rw [e₁ n]
        rfl
      · have n0 : (0 : Fin (n+2)) ≠ j.succ.succ := by
          intro h
          have e := congrArg Fin.val h
          simp at e
        have n1 : (1 : Fin (n+2)) ≠ j.succ.succ := by
          intro h
          have e := congrArg Fin.val h
          simp at e
        change fields (Equiv.swap (0 : Fin (n+2)) 1 j.succ.succ) = p .vf j
        rw [Equiv.swap_apply_of_ne_of_ne n0.symm n1.symm]
        rfl
  have carriers : ((A.permuteVF (Equiv.swap 0 1)).firstTwoSlice p).carrier =
      ((A.firstTwoSlice p).permuteVF (Equiv.swap 0 1)).carrier := by
    ext x
    change (((Fin.cons (x.1 0) (Fin.cons (x.1 1) (p .vf))) ∘ (Equiv.swap 0 1).symm),x.2) ∈ A.carrier ↔
      (Fin.cons (x.1 ((Equiv.swap (0 : Fin 2) 1).symm 0))
        (Fin.cons (x.1 ((Equiv.swap (0 : Fin 2) 1).symm 1)) (p .vf)),x.2) ∈ A.carrier
    rw [swapFields]
  unfold firstTwoSlice permuteVF at carriers ⊢
  congr

end RetainedFieldFamily

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

/-- The two-coordinate comparison, allowing a previously retained head
start. It compares all actual contractions of the two displayed orders. -/
@[expose] def TwoCoordinateOrderComparison (neg : rv O (-1) ∈ S₀.carrier .rv) (k : ℕ) : Prop :=
  ∀ {a b : ℕ} (A : RetainedFieldFamily 𝓜 S₀ 2 k)
    (U V : RetainedFieldFamily 𝓜 S₀ 0 (k+2)),
    HeadContractionRun A U → HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V →
    ∀ (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags), terminalCommonBlowup S₀ neg U V idx idy

theorem first_two_heads_fieldwise_commonBlowup
    (neg : rv O (-1) ∈ S₀.carrier .rv)
    {a b : ℕ} (A : RetainedFieldFamily 𝓜 S₀ (n+2) k)
    (H : HeadContractionData (n := n+1) A) (J : HeadContractionData (n := n) H.target)
    (H' : HeadContractionData (n := n+1) (A.permuteVF (Equiv.swap 0 1)))
    (J' : HeadContractionData (n := n) H'.target)
    (idx : Fin a ≃ J.target.tags) (idy : Fin b ≃ J'.target.tags)
    (pair : ∀ p : fieldAssignment n Z, TwoCoordinateOrderComparison
      ((𝓜).termGenerated (namedTuple S₀ p))
      (((𝓜).termGeneratedAssignment (namedTuple S₀ p) .rv (.inl ⟨_,neg⟩)).property) k) :
    fieldwiseCommonBlowup S₀ neg J.target J'.target idx idy := by
  intro p
  let T := (𝓜).termGenerated (namedTuple S₀ p)
  let negT : rv O (-1) ∈ T.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S₀ p) .rv (.inl ⟨_,neg⟩)).property
  let U := J.atFieldTail p
  let V := J'.atFieldTail p
  have left : HeadContractionRun (A.firstTwoSlice p) U.target :=
    .next (H.atFirstTwoSlice p) (.next U (.done _))
  have right : HeadContractionRun ((A.firstTwoSlice p).permuteVF (Equiv.swap 0 1)) V.target := by
    rw [← A.firstTwoSlice_swap p]
    exact .next (H'.atFirstTwoSlice p) (.next V (.done _))
  have common := pair p (A.firstTwoSlice p) U.target V.target left right idx idy
  exact terminalCommonBlowup_of_carriers T negT rfl rfl rfl rfl common

theorem first_two_exchange_with_tail
    (neg : rv O (-1) ∈ S₀.carrier .rv) (hyp : FieldwiseContractionHypotheses S₀)
    {a b c d l : ℕ} (A : RetainedFieldFamily 𝓜 S₀ (n+2) k)
    (H : HeadContractionData (n := n+1) A) (J : HeadContractionData (n := n) H.target)
    (H' : HeadContractionData (n := n+1) (A.permuteVF (Equiv.swap 0 1)))
    (J' : HeadContractionData (n := n) H'.target)
    (idx : Fin a ≃ J.target.tags) (idy : Fin b ≃ J'.target.tags)
    (U V : RetainedFieldFamily 𝓜 S₀ 0 l)
    (left : HeadContractionRun J.target U) (right : HeadContractionRun J'.target V)
    (ix : Fin c ≃ U.tags) (iy : Fin d ≃ V.tags)
    (pair : ∀ p : fieldAssignment n Z, TwoCoordinateOrderComparison
      ((𝓜).termGenerated (namedTuple S₀ p))
      (((𝓜).termGeneratedAssignment (namedTuple S₀ p) .rv (.inl ⟨_,neg⟩)).property) k) :
    terminalCommonBlowup S₀ neg U V ix iy :=
  fieldwise_contraction_runs_common_blowup S₀ neg hyp left right idx idy ix iy
    (first_two_heads_fieldwise_commonBlowup S₀ neg A H J H' J' idx idy pair)

end Canonical

end GeneralizedEuler.Section5
