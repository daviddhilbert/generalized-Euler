module

public import Section5.PreparedMapSuccessor

/-! Special bijections as finite compositions with explicit translated
coordinates and foci. RV-coordinate recodings permit the tuple indices
used for the retained history. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

universe u v

variable {K : Type u} [Field K] (O : ValuationSubring K) {F : Type v}
  {I J T : Type}

@[expose] def preparationHull (A : Set (PreparationPoint O F I)) : Set (PreparationPoint O F I) :=
  preparationLabel ⁻¹' (preparationLabel '' A)

namespace CoordinatePreparation

variable (C : CoordinatePreparation O F I)

@[expose] def ValidOn (A : Set (PreparationPoint O F I)) : Prop :=
  ∀ p ∈ preparationHull O A,
    (coordinateBaseLabel O C.coord (C.splitSource p).1, rv O (C.splitSource p).2)
      ∈ C.translation.locus →
    rv O (C.splitSource p).2 ≠ 0 ∧
      rv O (C.translation.focus (C.splitSource p).1 (rv O (C.splitSource p).2)) =
        rv O (C.splitSource p).2

end CoordinatePreparation

/-- An RV recoding just lists existing auxiliary coordinates or
leading terms of the unchanged field coordinates. -/
@[expose] def regularizeBy (source : J → F ⊕ I) (x : PreparationPoint O F I) :
    PreparationPoint O F J :=
  (x.1, Sum.elim (rv O ∘ x.1) x.2 ∘ source)

theorem regularizeBy_injOn {A : Set (PreparationPoint O F I)} (source : J → F ⊕ I)
    (recover : ∀ a ∈ A, ∀ b ∈ A,
      preparationLabel (regularizeBy O source a) = preparationLabel (regularizeBy O source b) →
        a.2 = b.2) :
    Set.InjOn (regularizeBy O source) A := by
  intro a ha b hb he
  have hf : a.1 = b.1 := congrArg (fun p : PreparationPoint O F J => p.1) he
  exact Prod.ext hf (recover a ha b hb (congrArg preparationLabel he))

/-- Every nontrivial stage is either one centripetal translation or a
regularization and reindexing of retained RV coordinates. The domain
of a translation may be a subset of its locus in the RV-hull. -/
inductive SpecialChain (O : ValuationSubring K) (F : Type v) :
    {I J : Type} → Set (PreparationPoint O F I) →
      (PreparationPoint O F I → PreparationPoint O F J) → Prop
  | id {I : Type} (A : Set (PreparationPoint O F I)) : SpecialChain O F A id
  | translation {I : Type} (A : Set (PreparationPoint O F I)) (C : CoordinatePreparation O F I)
      (valid : C.ValidOn O A) : SpecialChain O F A C.map
  | regularization {I J : Type} (A : Set (PreparationPoint O F I)) (source : J → F ⊕ I)
      (recover : ∀ a ∈ A, ∀ b ∈ A,
        preparationLabel (regularizeBy O source a) = preparationLabel (regularizeBy O source b) →
          a.2 = b.2) :
      SpecialChain O F A (regularizeBy O source)
  | append {I J T : Type} {A : Set (PreparationPoint O F I)}
      {f : PreparationPoint O F I → PreparationPoint O F J}
      {g : PreparationPoint O F J → PreparationPoint O F T}
      (first : SpecialChain O F A f) (last : SpecialChain O F (f '' A) g) :
      SpecialChain O F A (g ∘ f)
  | congr {I J : Type} {A : Set (PreparationPoint O F I)}
      {f g : PreparationPoint O F I → PreparationPoint O F J}
      (hf : SpecialChain O F A f) (he : Set.EqOn f g A) : SpecialChain O F A g

variable {O} in
theorem SpecialChain.injOn {A : Set (PreparationPoint O F I)}
    {f : PreparationPoint O F I → PreparationPoint O F J}
    (h : SpecialChain O F A f) : Set.InjOn f A := by
  induction h with
  | id => exact fun _ _ _ _ he => he
  | translation _ C _ => exact C.map_injective.injOn
  | regularization _ source recover => exact regularizeBy_injOn O source recover
  | append hf hg ihf ihg =>
    intro x hx y hy he
    exact ihf hx hy (ihg (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy) he)
  | congr hf he ih =>
    intro a ha b hb eq
    exact ih ha hb ((he ha).trans (eq.trans (he hb).symm))

variable {O} in
/-- A special chain restricts to every subset of its original domain. -/
theorem SpecialChain.restrict {A B : Set (PreparationPoint O F I)}
    {f : PreparationPoint O F I → PreparationPoint O F J}
    (h : SpecialChain O F A f) (hB : B ⊆ A) : SpecialChain O F B f := by
  induction h with
  | id => exact .id B
  | translation _ C valid =>
    refine .translation B C ?_
    intro p hp hl
    apply valid p _ hl
    exact Set.image_mono hB hp
  | regularization _ source recover =>
    exact .regularization B source (fun a ha b hb => recover a (hB ha) b (hB hb))
  | append hf hg ihf ihg =>
    exact .append (ihf hB) (ihg (Set.image_mono hB))
  | congr hf he ih =>
    exact .congr (ih hB) (fun _ hx => he (hB hx))

end GeneralizedEuler.Section5
