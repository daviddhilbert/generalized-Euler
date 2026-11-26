module

public import Section5.FiniteFieldPreimages
public import Section5.HeadTailGraphs

/-! The three preparation maps preserve finite field preimages. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation

variable {K : Type*} [Field K] {O : ValuationSubring K}
  {n m : ℕ} {I J H : Type}

namespace FiniteFieldPreimages

theorem keepTags {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin m) J}
    (hf : FiniteFieldPreimages f) : FiniteFieldPreimages (mapKeepingTags (H := H) f) := by
  intro y
  apply (hf y).subset
  rintro x ⟨s,hs⟩
  exact ⟨s ∘ Sum.inl, hs⟩

theorem liftTail {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J}
    (hf : FiniteFieldPreimages f) : FiniteFieldPreimages (liftTailMap f) := by
  intro y
  apply ((hf (y ∘ Fin.succ)).image (Fin.cons (y 0))).subset
  rintro x ⟨t,ht⟩
  have hhead : x 0 = y 0 := congrFun ht 0
  have htail : (f (x ∘ Fin.succ,t)).1 = y ∘ Fin.succ := by
    funext j
    exact congrFun ht j.succ
  refine ⟨x ∘ Fin.succ, ⟨t,htail⟩, ?_⟩
  funext j
  exact Fin.cases hhead.symm (fun _ => rfl) j

theorem head {k : ℕ}
    (P : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) k))
    (hfin : ∀ a, (Set.range (P a).offset).Finite) :
    FiniteFieldPreimages (headMap (I := I) P) := by
  intro y
  let b := y ∘ Fin.succ
  let g (d : K) : Fin (n+1) → K := Fin.cons (y 0 + d) b
  apply ((hfin b).image g).subset
  rintro x ⟨t,ht⟩
  have htail : x ∘ Fin.succ = b := by
    funext j
    exact congrFun ht j.succ
  have hhead : ((P (x ∘ Fin.succ)).map (x 0)).1 = y 0 := congrFun ht 0
  rw [htail] at hhead
  change x 0 - (P b).offset ((P b).label (x 0)) = y 0 at hhead
  refine ⟨_,Set.mem_range_self ((P b).label (x 0)),?_⟩
  funext j
  exact Fin.cases (eq_add_of_sub_eq hhead).symm (fun i => (congrFun htail i).symm) j

end FiniteFieldPreimages

end GeneralizedEuler.Section5
