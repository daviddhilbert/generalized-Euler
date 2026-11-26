module

public import Section5.HeadContractionFamilies

/-! A sequence of contractions retains the original head start and
adds one selected leading term for each field coordinate. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}

/-- The terminal family includes all original selected RV coordinates
and all leading terms added by head contractions. -/
inductive HeadContractionRun : {n k l : ℕ} →
    RetainedFieldFamily M S n k → RetainedFieldFamily M S 0 l → Prop
  | done (A : RetainedFieldFamily M S 0 k) : HeadContractionRun A A
  | next {A : RetainedFieldFamily M S (n+1) k} {B : RetainedFieldFamily M S 0 l}
    (H : HeadContractionData A) (tail : HeadContractionRun H.target B) :
    HeadContractionRun A B

namespace HeadContractionRun

theorem selected_count {A : RetainedFieldFamily M S n k} {B : RetainedFieldFamily M S 0 l}
    (r : HeadContractionRun A B) : l = k+n := by
  induction r with
  | done => simp
  | next _ _ ih => omega

theorem exists_run
    (head : ∀ n k (A : RetainedFieldFamily M S (n+1) k), Nonempty (HeadContractionData A))
    (A : RetainedFieldFamily M S n k) :
    ∃ B : RetainedFieldFamily M S 0 (k+n), HeadContractionRun A B := by
  have anyLength (m j : ℕ) (D : RetainedFieldFamily M S m j) :
      ∃ (l : ℕ) (B : RetainedFieldFamily M S 0 l), HeadContractionRun D B := by
    induction m generalizing j with
    | zero => exact ⟨j,D,.done D⟩
    | succ m ih =>
      obtain ⟨H⟩ := head m j D
      obtain ⟨l,B,r⟩ := ih (j+1) H.target
      exact ⟨l,B,.next H r⟩
  obtain ⟨l,B,r⟩ := anyLength n k A
  have eq := r.selected_count
  subst l
  exact ⟨B,r⟩

end HeadContractionRun

namespace RetainedFieldFamily

/-- Read the VF coordinates in the order specified by `order`.
Thus the first new coordinate is the old coordinate `order 0`. -/
@[expose] def permuteVF (A : RetainedFieldFamily M S n k) (order : Equiv.Perm (Fin n)) :
    RetainedFieldFamily M S n k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := {p | (p.1 ∘ order.symm,p.2) ∈ A.carrier}
  definable := by
    let take : (s : TCsort) → MixedVariables n A.tags s → MixedVariables n A.tags s
      | .vf => order.symm
      | .rv => id
    exact A.definable.pullback_relabel take
  finiteFibers b := A.finiteFibers (b ∘ order.symm)

end RetainedFieldFamily

end GeneralizedEuler.Section5
