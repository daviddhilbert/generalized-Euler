module

public import Section5.HeadContractionIteration

/-! Reordering only the field coordinates after the first one
commutes with an actual head contraction. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

namespace FinOrder

@[expose] def keepFirst {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (Fin.succ ∘ p)
  invFun := Fin.cases 0 (Fin.succ ∘ p.symm)
  left_inv i := Fin.cases rfl (fun j => congrArg Fin.succ (p.symm_apply_apply j)) i
  right_inv i := Fin.cases rfl (fun j => congrArg Fin.succ (p.apply_symm_apply j)) i

theorem cons_keepFirst {K : Type*} {n : ℕ} (p : Equiv.Perm (Fin n)) (a : K) (x : Fin n → K) :
    (Fin.cons a x : Fin (n+1) → K) ∘ (keepFirst p).symm = Fin.cons a (x ∘ p.symm) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem eq_keepFirst_of_fixes_zero {n : ℕ} (p : Equiv.Perm (Fin (n+1))) (h : p 0 = 0) :
    ∃ tail : Equiv.Perm (Fin n), p = keepFirst tail := by
  have hz : p.symm 0 = 0 := p.symm_apply_eq.2 h.symm
  have forward (i : Fin n) : p i.succ ≠ 0 := fun e => Fin.succ_ne_zero i (p.injective (e.trans h.symm))
  have back (i : Fin n) : p.symm i.succ ≠ 0 := fun e => Fin.succ_ne_zero i (p.symm.injective (e.trans hz.symm))
  let t : Equiv.Perm (Fin n) :=
    { toFun := fun i => (p i.succ).pred (forward i)
      invFun := fun i => (p.symm i.succ).pred (back i)
      left_inv := fun i => by
        apply Fin.succ_injective _
        exact (Fin.succ_pred _ _).trans
          ((congrArg p.symm (Fin.succ_pred _ _)).trans (p.symm_apply_apply _))
      right_inv := fun i => by
        apply Fin.succ_injective _
        exact (Fin.succ_pred _ _).trans
          ((congrArg p (Fin.succ_pred _ _)).trans (p.apply_symm_apply _)) }
  exact ⟨t,Equiv.ext (fun i => Fin.cases h (fun j => (Fin.succ_pred (p j.succ) (forward j)).symm) i)⟩

end FinOrder

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

namespace RetainedFieldFamily

theorem permuteVF_refl (A : RetainedFieldFamily M S n k) : A.permuteVF (Equiv.refl _) = A := by
  have c : (A.permuteVF (Equiv.refl _)).carrier = A.carrier := by ext x; rfl
  unfold permuteVF at c ⊢
  cases A
  congr

theorem permuteVF_comp (A : RetainedFieldFamily M S n k) (p q : Equiv.Perm (Fin n)) :
    (A.permuteVF p).permuteVF q = A.permuteVF (q.trans p) := by
  have c : ((A.permuteVF p).permuteVF q).carrier = (A.permuteVF (q.trans p)).carrier := by ext x; rfl
  unfold permuteVF at c ⊢
  congr

end RetainedFieldFamily

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+1) k} (H : HeadContractionData A)
  (p : Equiv.Perm (Fin n))

local notation "Z" => CanonicalSort O

@[expose] def permuteTail : HeadContractionData (A.permuteVF (FinOrder.keepFirst p)) where
  length := H.length
  preparation b := H.preparation (b ∘ p.symm)
  mapGraph := by
    let W := HistoryGraphVariables n H.length
    let relabel : (s : TCsort) → W s → W s
      | .vf => Sum.map id p.symm
      | .rv => id
    convert H.mapGraph.pullback_relabel relabel using 1
    ext a
    rfl
  historyGraph := by
    let U := VerticalVariables n A.tags
    let V := RVVariables (HistoryIndex H.length)
    let W := SumVariables U V
    let relabel : (s : TCsort) → W s → W s
      | .vf => Sum.map (Sum.map id p.symm) id
      | .rv => id
    change DefinableRelation M S.carrier (fun (a : SortedAssignment Z U) (q : SortedAssignment Z V) =>
      (H.preparation ((a .vf ∘ Sum.inr) ∘ p.symm)).label (a .vf (.inl ())) = decodeHistory O H.length (q .rv))
    have g := H.historyGraph
    unfold DefinableRelation at g ⊢
    convert g.pullback_relabel relabel using 1
    ext a
    rfl
  constant b x y t e := by
    change ((Fin.cons x b ∘ (FinOrder.keepFirst p).symm,t) ∈ A.carrier ↔
      (Fin.cons y b ∘ (FinOrder.keepFirst p).symm,t) ∈ A.carrier)
    rw [FinOrder.cons_keepFirst,FinOrder.cons_keepFirst]
    exact H.constant (b ∘ p.symm) x y t e
  finiteOffsets b := H.finiteOffsets (b ∘ p.symm)
  finalLead b := H.finalLead (b ∘ p.symm)

theorem permuteTail_target :
    (H.permuteTail p).target = H.target.permuteVF p := by
  have car : (H.permuteTail p).target.carrier = (H.target.permuteVF p).carrier := by
    ext b
    change (∃ x, (Fin.cons x b.1 ∘ (FinOrder.keepFirst p).symm,b.2 ∘ Sum.inr) ∈ A.carrier ∧
      (H.preparation (b.1 ∘ p.symm)).label x = decodeHistory O H.length (b.2 ∘ Sum.inl)) ↔
      ∃ x, (Fin.cons x (b.1 ∘ p.symm),b.2 ∘ Sum.inr) ∈ A.carrier ∧
        (H.preparation (b.1 ∘ p.symm)).label x = decodeHistory O H.length (b.2 ∘ Sum.inl)
    simp only [FinOrder.cons_keepFirst]
  unfold HeadContractionData.target RetainedFieldFamily.permuteVF at car ⊢
  congr

end HeadContractionData

end GeneralizedEuler.Section5
