module

public import Section3.DefinablePartitions
public import Section2.ValuativeInterval
public import Section2.SignedValue

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The signed-valuative conclusion of van den Dries, Proposition 4.2,
cited as Lemma 3.2. The cutoff belongs to the valuation ring. -/
def EventuallyConstantValue (O : ValuationSubring K) (hO : IsOrderConvex O)
    (f : O → K) : Prop :=
  ∃ a : O, ∀ b c : O, a < b → a < c →
    signedValue O hO (rv O (f b)) = signedValue O hO (rv O (f c))

omit [Field K] [IsStrictOrderedRing K]

/-- The three alternatives of Corollary 3.4. -/
inductive MonotonePiece (f : K → K) (A : Set K) : Prop
  | const (h : ∀ x ∈ A, ∀ y ∈ A, f x = f y)
  | increasing (h : StrictMonoOn f A)
  | decreasing (h : StrictAntiOn f A)

theorem MonotonePiece.restrict {f : K → K} {A B : Set K}
    (h : MonotonePiece f A) (hsub : B ⊆ A) : MonotonePiece f B := by
  cases h with
  | const h => exact .const (fun x hx y hy => h x (hsub hx) y (hsub hy))
  | increasing h => exact .increasing (h.mono hsub)
  | decreasing h => exact .decreasing (h.mono hsub)

/-- The definable intermediate value theorem on the pure field branch
makes the image of a convex piece convex, over any ordered field. -/
theorem image_ordConnected_of_intermediate_values {f : K → K} {A : Set K}
    (hA : A.OrdConnected)
    (hivt : ∀ x ∈ A, ∀ y ∈ A, ∀ w ∈ uIcc (f x) (f y), ∃ z ∈ uIcc x y, f z = w) :
    (f '' A).OrdConnected := by
  constructor
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ w hw
  obtain ⟨z,hz,hfz⟩ := hivt x hx y hy w (Set.Icc_subset_uIcc hw)
  exact ⟨z,hA.uIcc_subset hx hy hz,hfz⟩

/-- Corollary 3.5. A finite definable partition in 3.4 can be tagged by
distinct named RV pairs. Each tag gives precisely the corresponding
monotone piece, even if several pieces have constant images. -/
theorem constant_or_injective_tag_fibers {I R : Type*} (tag : I ↪ R × R)
    (f : K → K) (A : Set K) (part : A → I)
    (hm : ∀ i, MonotonePiece f {x | ∃ h : x ∈ A, part ⟨x,h⟩ = i})
    (t : R × R) :
    let F := {x : K | ∃ h : x ∈ A, tag (part ⟨x,h⟩) = t}
    (∀ x ∈ F, ∀ y ∈ F, f x = f y) ∨ InjOn f F := by
  intro F
  by_cases ht : t ∈ range tag
  · obtain ⟨i,rfl⟩ := ht
    have hs : F ⊆ {x | ∃ h : x ∈ A, part ⟨x,h⟩ = i} :=
      fun _ ⟨h,he⟩ => ⟨h,tag.injective he⟩
    cases (hm i).restrict hs with
    | const h => exact Or.inl h
    | increasing h => exact Or.inr h.injOn
    | decreasing h => exact Or.inr h.injOn
  · exact Or.inl (fun _ ⟨_,he⟩ => (ht ⟨_,he⟩).elim)

end GeneralizedEuler.Section3
