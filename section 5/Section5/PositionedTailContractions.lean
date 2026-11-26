module

public import Section5.IndependentCenterHeads

/-! After the first head the remaining field fiber has a recorded
paradigm. A preparation of its unary domain retains that paradigm. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ} {I : Type}

namespace HeadContractionData

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 1 k)
  (old : I → A.tags) (mark : A.tags) (u : (I → RV0 O) → RV0 O)
  (D : Set (K × (I → RV0 O))) (cs : List (S.carrier .vf))
  (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
  (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
  (shape : ∀ b (t : A.tags → RV0 O), (b,t) ∈ A.carrier ↔ (b 0,t ∘ old) ∈ D ∧ t mark = u (t ∘ old))
  (stable : ∀ x y (t : I → RV0 O),
    ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label x =
      ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).label y →
       ((x,t) ∈ D ↔ (y,t) ∈ D))

@[expose] def positionedTail : HeadContractionData (n := 0) A :=
  .ofIndependentCenters O hO power S cs A minusOne hm F hF (by
    intro b x y t e
    change (Fin.cons x b,t) ∈ A.carrier ↔ (Fin.cons y b,t) ∈ A.carrier
    exact (shape (Fin.cons x b) t).trans
      ((and_congr_left' (stable x y (t ∘ old) e)).trans (shape (Fin.cons y b) t).symm))

local notation "H" => positionedTail O hO power S A old mark u D cs F minusOne hm hF shape stable
local notation "P" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

theorem positionedTail_target_mem (q : HistoryIndex cs.length ⊕ A.tags → RV0 O) :
    (Fin.elim0,q) ∈ (H).target.carrier ↔
      (∃ x, (x,q ∘ Sum.inr ∘ old) ∈ D ∧ (P).label x = decodeHistory O cs.length (q ∘ Sum.inl)) ∧
        q (.inr mark) = u (q ∘ Sum.inr ∘ old) := by
  change (∃ x, (Fin.cons x Fin.elim0,q ∘ Sum.inr) ∈ A.carrier ∧
    (P).label x = decodeHistory O cs.length (q ∘ Sum.inl)) ↔ _
  constructor
  · rintro ⟨x,h,he⟩
    obtain ⟨hd,hp⟩ := (shape _ _).1 h
    exact ⟨⟨x,hd,he⟩,hp⟩
  · rintro ⟨⟨x,hd,he⟩,hp⟩
    exact ⟨x,(shape _ _).2 ⟨hd,hp⟩,he⟩

end HeadContractionData

end GeneralizedEuler.Section5
