module

public import Section5.IndependentCenterHeads
public import Section5.HeadContractionIteration

/-! If each RV-tag fiber is a product, choosing the same preparation
of each factor in both orders gives terminal tags with two independent
histories and the original shared tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

namespace HeadContractionData

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 2 k)
  (D E' : Set (K × (A.tags → RV0 O)))
  (shape : ∀ (x : Fin 2 → K) (t : A.tags → RV0 O), (x,t) ∈ A.carrier ↔
    (x 0,t) ∈ D ∧ (x 1,t) ∈ E')
  (cs ds : List (S.carrier .vf))
  (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
  (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

local notation "P" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs
local notation "Q" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val ds

variable
  (stableD : ∀ x y (t : A.tags → RV0 O),
    ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label x =
       ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label y →
    ((x,t) ∈ D ↔ (y,t) ∈ D))

@[expose] def taggedProductFirst : HeadContractionData (n := 1) A :=
  .ofIndependentCenters O hO power S cs A minusOne hm F hF (by
    intro b x y t e
    change (Fin.cons x b,t) ∈ A.carrier ↔ (Fin.cons y b,t) ∈ A.carrier
    refine (shape _ _).trans (Iff.trans ?_ (shape _ _).symm)
    exact and_congr_left' (stableD x y t e))

local notation "H" => taggedProductFirst O hO power S A D E' shape cs F minusOne hm hF stableD

theorem taggedProductFirst_target_mem (y : Fin 1 → K) (t : HistoryIndex cs.length ⊕ A.tags → RV0 O) :
    (y,t) ∈ (H).target.carrier ↔
    (y 0,t ∘ Sum.inr) ∈ E' ∧
      ∃ x, (x,t ∘ Sum.inr) ∈ D ∧ (P).label x = decodeHistory O cs.length (t ∘ Sum.inl) := by
  change (∃ x, (Fin.cons x y,t ∘ Sum.inr) ∈ A.carrier ∧
    (P).label x = decodeHistory O cs.length (t ∘ Sum.inl)) ↔ _
  constructor
  · rintro ⟨x,h,he⟩
    obtain ⟨d,e⟩ := (shape (Fin.cons x y) (t ∘ Sum.inr)).1 h
    exact ⟨e,x,d,he⟩
  · rintro ⟨e,x,d,he⟩
    exact ⟨x,(shape (Fin.cons x y) (t ∘ Sum.inr)).2 ⟨d,e⟩,he⟩

variable (stableE : ∀ x y (t : A.tags → RV0 O),
    ((UnaryPreparation.regularize (O := O)).prepare Subtype.val ds).label x =
       ((UnaryPreparation.regularize (O := O)).prepare Subtype.val ds).label y →
    ((x,t) ∈ E' ↔ (y,t) ∈ E'))

@[expose] def taggedProductSecond : HeadContractionData (n := 0) (H).target :=
  .ofIndependentCenters O hO power S ds (H).target minusOne hm F hF (by
    intro b x y t e
    change (Fin.cons x b,t) ∈ (H).target.carrier ↔ (Fin.cons y b,t) ∈ (H).target.carrier
    refine (taggedProductFirst_target_mem O hO power S A D E' shape cs F minusOne hm hF stableD _ t).trans
      (Iff.trans ?_ (taggedProductFirst_target_mem O hO power S A D E' shape cs F minusOne hm hF stableD _ t).symm)
    exact and_congr_left' (stableE x y (t ∘ Sum.inr) e))

local notation "J" => taggedProductSecond O hO power S A D E' shape cs ds F minusOne hm hF stableD stableE

theorem taggedProductSecond_target_mem (t : HistoryIndex ds.length ⊕ (HistoryIndex cs.length ⊕ A.tags) → RV0 O) :
    (Fin.elim0,t) ∈ (J).target.carrier ↔
      (∃ x, (x,t ∘ Sum.inr ∘ Sum.inr) ∈ D ∧
        (P).label x = decodeHistory O cs.length (t ∘ Sum.inr ∘ Sum.inl)) ∧
      (∃ y, (y,t ∘ Sum.inr ∘ Sum.inr) ∈ E' ∧ (Q).label y = decodeHistory O ds.length (t ∘ Sum.inl)) := by
  change (∃ y, (Fin.cons y Fin.elim0,t ∘ Sum.inr) ∈ (H).target.carrier ∧
    (Q).label y = decodeHistory O ds.length (t ∘ Sum.inl)) ↔ _
  constructor
  · rintro ⟨y,h,hy⟩
    obtain ⟨e,d⟩ := (taggedProductFirst_target_mem O hO power S A D E' shape cs F minusOne hm hF stableD _ _).1 h
    exact ⟨d,y,e,hy⟩
  · rintro ⟨d,y,e,hy⟩
    exact ⟨y,(taggedProductFirst_target_mem O hO power S A D E' shape cs F minusOne hm hF stableD _ _).2 ⟨e,d⟩,hy⟩

theorem taggedProductRun : HeadContractionRun A (J).target := .next H (.next J (.done _))

end HeadContractionData

end GeneralizedEuler.Section5
