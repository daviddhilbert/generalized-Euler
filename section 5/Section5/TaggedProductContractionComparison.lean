module

public import Section5.TaggedProductHeadRuns
public import Section5.TerminalSelectedEquivalence

/-! Products in each tagged fiber commute under contraction, even
when a factor varies with the shared tuple or is a singleton. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

private def reverseTaggedFactors (I J T : Type) : J ⊕ (I ⊕ T) ≃ I ⊕ (J ⊕ T) where
  toFun
    | .inl j => .inr (.inl j)
    | .inr (.inl i) => .inl i
    | .inr (.inr t) => .inr (.inr t)
  invFun
    | .inl i => .inr (.inl i)
    | .inr (.inl j) => .inl j
    | .inr (.inr t) => .inr (.inr t)
  left_inv := by rintro (j | (i | t)) <;> rfl
  right_inv := by rintro (i | (j | t)) <;> rfl

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem tagged_product_contraction_orders
    (A : RetainedFieldFamily 𝓜 S 2 k) (D E' : Set (K × (A.tags → RV0 O)))
    (shape : ∀ (x : Fin 2 → K) (t : A.tags → RV0 O), (x,t) ∈ A.carrier ↔
      (x 0,t) ∈ D ∧ (x 1,t) ∈ E')
    (cs ds : List (S.carrier .vf))
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (stableD : ∀ x y (t : A.tags → RV0 O),
      ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label x =
        ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label y →
      ((x,t) ∈ D ↔ (y,t) ∈ D))
    (stableE : ∀ x y (t : A.tags → RV0 O),
      ((UnaryPreparation.regularize (O := O)).prepare Subtype.val ds).label x =
        ((UnaryPreparation.regularize (O := O)).prepare Subtype.val ds).label y →
      ((x,t) ∈ E' ↔ (y,t) ∈ E'))
    (zero : S.carrier .rv) (hz : zero.val = 0) :
    ∃ (U V : RetainedFieldFamily 𝓜 S 0 (k+2)) (a b : ℕ) (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags),
      HeadContractionRun A U ∧ HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V ∧
        U.terminalGradedClass idx zero hz = V.terminalGradedClass idy zero hz := by
  let swap := Equiv.swap (0 : Fin 2) 1
  let B := A.permuteVF swap
  have rev (x : Fin 2 → K) (t : B.tags → RV0 O) :
      (x,t) ∈ B.carrier ↔ (x 0,t) ∈ E' ∧ (x 1,t) ∈ D := by
    change (x ∘ swap.symm,t) ∈ A.carrier ↔ _
    refine (shape _ _).trans ?_
    change (x (swap 0),t) ∈ D ∧ (x (swap 1),t) ∈ E' ↔ _
    rw [show swap 0 = 1 from Equiv.swap_apply_left _ _,show swap 1 = 0 from Equiv.swap_apply_right _ _]
    exact and_comm
  let H := HeadContractionData.taggedProductSecond O hO power S A D E' shape cs ds F minusOne hm hF stableD stableE
  let J := HeadContractionData.taggedProductSecond O hO power S B E' D rev ds cs F minusOne hm hF stableE stableD
  let : Finite H.target.tags := H.target.finiteTags
  let : Finite J.target.tags := J.target.finiteTags
  let ia : Fin (Nat.card H.target.tags) ≃ H.target.tags := (Finite.equivFin _).symm
  let ib : Fin (Nat.card J.target.tags) ≃ J.target.tags := (Finite.equivFin _).symm
  refine ⟨H.target,J.target,_,_,ia,ib,
    HeadContractionData.taggedProductRun O hO power S A D E' shape cs ds F minusOne hm hF stableD stableE,
    HeadContractionData.taggedProductRun O hO power S B E' D rev ds cs F minusOne hm hF stableE stableD,?_⟩
  let e : H.target.tags ≃ J.target.tags := reverseTaggedFactors (HistoryIndex cs.length) (HistoryIndex ds.length) A.tags
  let order := Equiv.swap (Fin.castSucc (Fin.last k)) (Fin.last (k+1))
  have tags (t : H.target.tags → RV0 O) :
      (Fin.elim0,t) ∈ H.target.carrier ↔ (Fin.elim0,t ∘ e.symm) ∈ J.target.carrier := by
    have a := HeadContractionData.taggedProductSecond_target_mem O hO power S A D E' shape cs ds F minusOne hm hF stableD stableE t
    have b := HeadContractionData.taggedProductSecond_target_mem O hO power S B E' D rev ds cs F minusOne hm hF stableE stableD
      (t ∘ e.symm)
    exact a.trans (and_comm.trans b.symm)
  have select (i : Fin (k+2)) : e (H.target.select i) = J.target.select (order i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have o : order (Fin.last (k+1)) = Fin.castSucc (Fin.last k) := Equiv.swap_apply_right _ _
      rw [o,H.target_select_last,J.target_select_castSucc,HeadContractionData.target_select_last]
      change e (.inl (lastIndex ds.length)) = .inr (.inl (lastIndex ds.length))
      rfl
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · have o : order (Fin.castSucc (Fin.last k)) = Fin.last (k+1) := Equiv.swap_apply_left _ _
        rw [o,H.target_select_castSucc,J.target_select_last,HeadContractionData.target_select_last]
        change e (.inr (.inl (lastIndex cs.length))) = .inl (lastIndex cs.length)
        rfl
      · have avoid₁ : Fin.castSucc (Fin.castSucc j) ≠ Fin.castSucc (Fin.last k) := fun h =>
          Fin.castSucc_ne_last j (Fin.castSucc_injective _ h)
        have avoid₂ : Fin.castSucc (Fin.castSucc j) ≠ Fin.last (k+1) := Fin.castSucc_ne_last _
        have o : order (Fin.castSucc (Fin.castSucc j)) = Fin.castSucc (Fin.castSucc j) :=
          Equiv.swap_apply_of_ne_of_ne avoid₁ avoid₂
        rw [o,H.target_select_castSucc,J.target_select_castSucc,
          HeadContractionData.target_select_castSucc,HeadContractionData.target_select_castSucc]
        change e (.inr (.inr (A.select j))) = .inr (.inr (A.select j))
        rfl
  exact H.target.terminalGradedClass_selected_equiv J.target e ia ib order tags select zero hz

theorem tagged_product_contraction_orders_of_definable_factors
    (A : RetainedFieldFamily 𝓜 S 2 k) (D E' : Set (K × (A.tags → RV0 O)))
    (shape : ∀ (x : Fin 2 → K) (t : A.tags → RV0 O), (x,t) ∈ A.carrier ↔
      (x 0,t) ∈ D ∧ (x 1,t) ∈ E')
    (defD : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 A.tags) | (a .vf 0,a .rv) ∈ D})
    (defE : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 A.tags) | (a .vf 0,a .rv) ∈ E'})
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier A.tags)
      (CenterTestAssignments S.carrier A.tags))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (zero : S.carrier .rv) (hz : zero.val = 0) :
    ∃ (U V : RetainedFieldFamily 𝓜 S 0 (k+2)) (a b : ℕ) (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags),
      HeadContractionRun A U ∧ HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V ∧
        U.terminalGradedClass idx zero hz = V.terminalGradedClass idy zero hz := by
  obtain ⟨cs,_,_,stableD,_⟩ := unary_deformation O hO power S minusOne hm F hF sat immediate D defD
  obtain ⟨ds,_,_,stableE,_⟩ := unary_deformation O hO power S minusOne hm F hF sat immediate E' defE
  exact tagged_product_contraction_orders O hO power S A D E' shape cs ds F minusOne hm hF stableD stableE zero hz

end GeneralizedEuler.Section5
