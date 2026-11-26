module

public import Section5.VerticalTests
public import Section5.VerticalSuccessor
public import Section5.HeadTailGraphs

/-! Relate the history tuple used by the definable tail map to the
product presentation used by the geometry of the head map. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation

variable {K : Type*} [Field K] {O : ValuationSubring K} {n k : ℕ} {I J R : Type}

/-- Pack the retained history into a block of the auxiliary tuple. -/
@[expose] def packHistory :
    PreparationPoint O (Fin n) I × PreparationLabels O (RV0 O) k ≃
      PreparationPoint O (Fin n) (I ⊕ HistoryIndex k) where
  toFun p := (p.1.1, Sum.elim p.1.2 (encodeHistory O k p.2))
  invFun p := ((p.1, p.2 ∘ Sum.inl), decodeHistory O k (p.2 ∘ Sum.inr))
  left_inv p := by
    refine Prod.ext ?_ ?_
    · rfl
    · exact decode_encode_history O k p.2
  right_inv p := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext j
      cases j with
      | inl i => rfl
      | inr i => exact congrFun (encode_decode_history O k (p.2 ∘ Sum.inr)) i

/-- Both the test used in the geometric assembly and the one passed to
the definable tail map represent the same relation. -/
theorem image_succeededTailTest
    (P : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) k))
    (f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) R)
    (G : PointTests O (n+1) I J) (s : J → RV0 O) :
    packHistory '' succeededTailTest (P ∘ Prod.fst) f
      {p | ((Fin.cons p.2.1 p.1.1, p.1.2), p.2.2) ∈ G} s =
      {q | ∃ p, mapKeepingTags f p = q ∧ (p,s) ∈ descendedTest O P G} := by
  ext q
  constructor
  · rintro ⟨⟨q', t⟩, ⟨b,x,hb,ht,hG⟩, hq⟩
    refine ⟨packHistory (b,t), ?_, ?_⟩
    · change packHistory (f b,t) = q
      rw [hb]
      exact hq
    · change ∃ x, ((Fin.cons x b.1,b.2),s) ∈ G ∧
        (P b.1).label x = decodeHistory O k (encodeHistory O k t)
      exact ⟨x, hG, ht.trans (decode_encode_history O k t).symm⟩
  · rintro ⟨p, hp, htest⟩
    obtain ⟨⟨b, t⟩, rfl⟩ := (packHistory (O := O) (I := I) (k := k)).surjective p
    obtain ⟨x, hx, ht⟩ := htest
    change (P b.1).label x = decodeHistory O k (encodeHistory O k t) at ht
    rw [decode_encode_history] at ht
    exact ⟨(f b,t), ⟨b,x,rfl,ht,hx⟩, hp⟩

/-- The field head is the only coordinate separated from the tail data. -/
@[expose] def joinHead (a : PreparationPoint O (Fin n) I × K) :
    PreparationPoint O (Fin (n+1)) I :=
  (Fin.cons a.2 a.1.1, a.1.2)

theorem joinHead_separate (p : PreparationPoint O (Fin (n+1)) I) :
    joinHead (tailPoint p, p.1 0) = p := by
  refine Prod.ext ?_ rfl
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem separate_joinHead (p : PreparationPoint O (Fin n) I × K) :
    (tailPoint (joinHead p), (joinHead p).1 0) = p := rfl

theorem joinHead_injective :
    Function.Injective (joinHead (O := O) (n := n) (I := I)) := by
  intro a b h
  rw [← separate_joinHead a, ← separate_joinHead b, h]

end GeneralizedEuler.Section5
