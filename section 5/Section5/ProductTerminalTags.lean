module

public import Section5.UnaryProductContractions

/-! The terminal tags of a product run rearrange into the two
independent factor tags, with one selected coordinate from each. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}

namespace HeadContractionData

variable {A B : RetainedFieldFamily M S 1 0}
  (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B)

@[expose] def productTagPack : (H.productSecond J).target.tags ≃ H.target.tags ⊕ J.target.tags where
  toFun
    | .inl j => .inr (.inl j)
    | .inr (.inl i) => .inl (.inl i)
    | .inr (.inr (.inl a)) => .inl (.inr a)
    | .inr (.inr (.inr b)) => .inr (.inr b)
  invFun
    | .inl (.inl i) => .inr (.inl i)
    | .inl (.inr a) => .inr (.inr (.inl a))
    | .inr (.inl j) => .inl j
    | .inr (.inr b) => .inr (.inr (.inr b))
  left_inv := by rintro (j | (i | (a | b))) <;> rfl
  right_inv := by rintro ((i | a) | (j | b)) <;> rfl

theorem productSecond_target_mem (t : (H.productSecond J).target.tags → RV0 O) :
    (Fin.elim0,t) ∈ (H.productSecond J).target.carrier ↔
      (Fin.elim0,t ∘ (H.productTagPack J).symm ∘ Sum.inl) ∈ H.target.carrier ∧
      (Fin.elim0,t ∘ (H.productTagPack J).symm ∘ Sum.inr) ∈ J.target.carrier := by
  have firstTags : H.firstFactorTags (t ∘ Sum.inr) = t ∘ (H.productTagPack J).symm ∘ Sum.inl := by
    funext i
    cases i <;> rfl
  change (∃ x,
    (Fin.cons x Fin.elim0,t ∘ Sum.inr) ∈ (H.productFirst B).target.carrier ∧
    (J.preparation Fin.elim0).label x = decodeHistory O J.length (t ∘ Sum.inl)) ↔
      (Fin.elim0,t ∘ (H.productTagPack J).symm ∘ Sum.inl) ∈ H.target.carrier ∧
      ∃ x, (Fin.cons x Fin.elim0,(t ∘ (H.productTagPack J).symm ∘ Sum.inr) ∘ Sum.inr) ∈ B.carrier ∧
        (J.preparation Fin.elim0).label x = decodeHistory O J.length ((t ∘ (H.productTagPack J).symm ∘ Sum.inr) ∘ Sum.inl)
  have each (x : K) := H.productFirst_target_mem (B := B) (Fin.cons x Fin.elim0) (t ∘ Sum.inr)
  constructor
  · rintro ⟨x,h,e⟩
    obtain ⟨a,b⟩ := (each x).1 h
    refine ⟨?_,x,b,e⟩
    rwa [firstTags] at a
  · rintro ⟨a,x,b,e⟩
    refine ⟨x,(each x).2 ⟨?_,b⟩,e⟩
    rwa [firstTags]

theorem productTagPack_select_zero :
    H.productTagPack J ((H.productSecond J).target.select 0) = Sum.inl (H.target.select 0) := rfl

theorem productTagPack_select_one :
    H.productTagPack J ((H.productSecond J).target.select 1) = Sum.inr (J.target.select 0) := rfl

@[expose] def productReverseTags :
    (H.productSecond J).target.tags ≃ (J.productSecond H).target.tags :=
  (H.productTagPack J).trans ((Equiv.sumComm _ _).trans (J.productTagPack H).symm)

theorem productReverseTags_carrier (t : (H.productSecond J).target.tags → RV0 O) :
    (Fin.elim0,t) ∈ (H.productSecond J).target.carrier ↔
      (Fin.elim0,t ∘ (H.productReverseTags J).symm) ∈ (J.productSecond H).target.carrier := by
  rw [H.productSecond_target_mem J,J.productSecond_target_mem H]
  have flip₀ : (t ∘ (H.productReverseTags J).symm) ∘ (J.productTagPack H).symm ∘ Sum.inl =
      t ∘ (H.productTagPack J).symm ∘ Sum.inr := by
    funext i
    simp [productReverseTags,Function.comp_apply]
  have flip₁ : (t ∘ (H.productReverseTags J).symm) ∘ (J.productTagPack H).symm ∘ Sum.inr =
      t ∘ (H.productTagPack J).symm ∘ Sum.inl := by
    funext i
    simp [productReverseTags,Function.comp_apply]
  rw [flip₀,flip₁,and_comm]

theorem productReverseTags_select (i : Fin 2) :
    H.productReverseTags J ((H.productSecond J).target.select i) =
      (J.productSecond H).target.select (Equiv.swap (0 : Fin 2) 1 i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · apply (J.productTagPack H).injective
    simp only [productReverseTags,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.swap_apply_left]
    rw [H.productTagPack_select_zero J,J.productTagPack_select_one H]
    rfl
  · have j1 : j.succ = (1 : Fin 2) := by rw [Fin.fin_one_eq_zero j]; rfl
    rw [j1]
    apply (J.productTagPack H).injective
    simp only [productReverseTags,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.swap_apply_right]
    rw [H.productTagPack_select_one J,J.productTagPack_select_zero H]
    rfl

theorem unaryProduct_terminalClass_commutes {a b : ℕ}
    (idx : Fin a ≃ (H.productSecond J).target.tags) (idy : Fin b ≃ (J.productSecond H).target.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun i => i.elim0)) :
    (H.productSecond J).target.terminalGradedClass idx zero hz =
      (J.productSecond H).target.terminalGradedClass idy zero hz :=
  (H.productSecond J).target.terminalGradedClass_selected_equiv (J.productSecond H).target
    (H.productReverseTags J) idx idy (Equiv.swap 0 1) (H.productReverseTags_carrier J) (H.productReverseTags_select J) zero hz

end HeadContractionData

end GeneralizedEuler.Section5
