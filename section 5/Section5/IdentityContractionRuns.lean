module

public import Section5.PullbackHeadContractions

/-! In an identity run every appended history is one leading term.
Reassemble all these terms in the original order and keep all tags. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

private def packHeadLabels (n : ℕ) (I : Type) :
    Fin (n+1) ⊕ I ≃ Fin n ⊕ (Unit ⊕ I) where
  toFun := Sum.elim (Fin.cases (.inr (.inl ())) Sum.inl) (Sum.inr ∘ Sum.inr)
  invFun
    | .inl i => .inl i.succ
    | .inr (.inl _) => .inl 0
    | .inr (.inr i) => .inr i
  left_inv := by
    rintro (i | i)
    · exact Fin.cases rfl (fun _ => rfl) i
    · rfl
  right_inv := by rintro (i | (_ | i)) <;> rfl

private def splitLastSelected (k : ℕ) : Fin (k+1) ≃ Unit ⊕ Fin k where
  toFun := Fin.lastCases (.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => Fin.last k) Fin.castSucc
  left_inv i := Fin.lastCases (by simp) (fun j => by simp) i
  right_inv := by rintro (_ | j) <;> simp

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- An identity run remembers exactly the original RV tags and the
leading terms of the input field tuple. The selected labels are the old
head start and all the new field leading terms in contraction order. -/
theorem identity_contraction_run
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    {n k : ℕ} (A : RetainedFieldFamily 𝓜 S n k) (pullback : A.IsFieldPullback O hO power S) :
    ∃ (l : ℕ) (B : RetainedFieldFamily 𝓜 S 0 l)
      (e : (Fin n ⊕ A.tags) ≃ B.tags) (order : Fin l ≃ (Fin n ⊕ Fin k)),
      HeadContractionRun A B ∧
      (∀ (t : B.tags → RV0 O) (x : Fin n → K), (∀ i, rv O (x i) = t (e (.inl i))) →
        ((Fin.elim0,t) ∈ B.carrier ↔ (x,t ∘ e ∘ Sum.inr) ∈ A.carrier)) ∧
      (∀ i, B.select i = e (Sum.map id A.select (order i))) := by
  induction n generalizing k with
  | zero =>
    let collapse (I : Type) : Fin 0 ⊕ I ≃ I :=
      { toFun := Sum.elim Fin.elim0 id
        invFun := Sum.inr
        left_inv := by rintro (j | j); exact Fin.elim0 j; rfl
        right_inv := fun _ => rfl }
    refine ⟨k,A,collapse A.tags,(collapse (Fin k)).symm,.done _,?_,fun _ => rfl⟩
    intro t x _
    rw [show x = (Fin.elim0 : Fin 0 → K) from Subsingleton.elim _ _]
    rfl
  | succ n ih =>
    let H := HeadContractionData.identityHead O hO power S A F minusOne hm hF zero hz pullback
    obtain ⟨l,B,e,order,tail,mem,selected⟩ := ih H.target
      (HeadContractionData.identityHead_target_pullback O hO power S A F minusOne hm hF zero hz pullback)
    let pack := packHeadLabels n A.tags
    let ix := pack.trans e
    let read : Fin l ≃ Fin (n+1) ⊕ Fin k :=
      (order.trans (Equiv.sumCongr (Equiv.refl _) (splitLastSelected k))).trans (packHeadLabels n (Fin k)).symm
    refine ⟨l,B,ix,read,.next H tail,?_,?_⟩
    · intro t x hx
      let b : Fin n → K := x ∘ Fin.succ
      let q : H.target.tags → RV0 O := t ∘ e ∘ Sum.inr
      have split (a : K) : (rv O ∘ (Fin.cons a b : Fin (n+1) → K)) = rv O ∘ x ↔ rv O a = rv O (x 0) := by
        constructor
        · intro d
          exact congrFun d 0
        · intro d
          funext j
          exact Fin.cases d (fun _ => rfl) j
      have old : q ∘ Sum.inr = t ∘ ix ∘ Sum.inr := rfl
      have head : q (.inl ()) = rv O (x 0) := (hx 0).symm
      rw [mem t b (fun i => hx i.succ),HeadContractionData.identityHead_target_iff]
      change (∃ a, (Fin.cons a b,q ∘ Sum.inr) ∈ A.carrier ∧ rv O a = q (.inl ())) ↔ _
      rw [old,head]
      constructor
      · rintro ⟨a,ha,he⟩
        exact (pullback (Fin.cons a b) x _ ((split a).2 he)).1 ha
      · intro h
        refine ⟨x 0,?_,rfl⟩
        exact (pullback (Fin.cons (x 0) b) x _ ((split (x 0)).2 rfl)).2 h
    · intro i
      rw [selected]
      change e (Sum.map id H.target.select (order i)) =
        e (pack (Sum.map id A.select ((packHeadLabels n (Fin k)).symm
          (Sum.map id (splitLastSelected k) (order i)))))
      apply congrArg e
      cases order i with
      | inl j => rfl
      | inr j =>
        refine Fin.lastCases ?_ (fun p => ?_) j
        · change Sum.inr (Fin.lastCases (.inl ()) (Sum.inr ∘ A.select) (Fin.last k)) =
            pack (Sum.map id A.select ((packHeadLabels n (Fin k)).symm
              (.inr (Fin.lastCases (.inl ()) Sum.inr (Fin.last k)))))
          rw [Fin.lastCases_last,Fin.lastCases_last]
          rfl
        · change Sum.inr (Fin.lastCases (.inl ()) (Sum.inr ∘ A.select) (Fin.castSucc p)) =
            pack (Sum.map id A.select ((packHeadLabels n (Fin k)).symm
              (.inr (Fin.lastCases (.inl ()) Sum.inr (Fin.castSucc p)))))
          rw [Fin.lastCases_castSucc,Fin.lastCases_castSucc]
          rfl

end GeneralizedEuler.Section5
