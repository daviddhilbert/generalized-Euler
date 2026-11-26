module

public import Section5.ZeroBlowupObject

/-! Appending a definably determined RV coordinate keeps the same
underlying RV set up to fixed-base definable bijection. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {I : Type} [Finite I]

theorem rv_equiv_append_label (D : Set (I → X .rv)) (defD : isRVSet M S D)
    (d : (I → X .rv) → X .rv)
    (defd : DefinableRelation M S.carrier (fun
      (a : SortedAssignment X (RVVariables I)) (b : SortedAssignment X (RVVariables (Fin 1))) =>
      d (a .rv) = b .rv 0)) :
    RVDefinablyEquivalent M S.carrier D {y : I ⊕ Fin 1 → X .rv | y ∘ Sum.inl ∈ D ∧ y (.inr 0) = d (y ∘ Sum.inl)} := by
  let B := {y : I ⊕ Fin 1 → X .rv | y ∘ Sum.inl ∈ D ∧ y (.inr 0) = d (y ∘ Sum.inl)}
  let e : D ≃ B :=
    { toFun := fun x => ⟨Sum.elim x.val (fun _ => d x.val),x.property,rfl⟩
      invFun := fun y => ⟨y.val ∘ Sum.inl,y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro y
        apply Subtype.ext
        funext i
        rcases i with i | i
        · rfl
        · rw [Subsingleton.elim i (0 : Fin 1)]
          exact y.property.2.symm }
  let V := SumVariables (RVVariables I) (RVVariables (I ⊕ Fin 1))
  let rename : ∀ s, SumVariables (RVVariables I) (RVVariables (Fin 1)) s → V s
    | .vf => Sum.elim PEmpty.elim PEmpty.elim
    | .rv => Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  have prior := defD.pullback_relabel (fun s => (Sum.inl : RVVariables I s → V s))
  have same := SortedDefinableOver.iInter (fun i : I =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V) .rv (.inl i) (.inr (.inl i)))
  unfold DefinableRelation at defd
  let graph := prior.inter (same.inter (defd.pullback_relabel rename))
  refine ⟨e,rvGraph_of_relation ?_⟩
  unfold DefinableRelation
  convert graph using 1
  ext w
  let a : I → X .rv := w .rv ∘ Sum.inl
  let b : I ⊕ Fin 1 → X .rv := w .rv ∘ Sum.inr
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  change (∃ x : D, x.val = a ∧ (e x).val = b) ↔ a ∈ D ∧
    (∀ i, a i = b (.inl i)) ∧ d a = b (.inr 0)
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨hx ▸ x.property,fun i => (congrFun hx i).symm.trans (congrFun he (.inl i)),
      (congrArg d hx).symm.trans (congrFun he (.inr 0))⟩
  · rintro ⟨ha,hb,hd⟩
    refine ⟨⟨a,ha⟩,rfl,?_⟩
    funext i
    rcases i with i | i
    · exact hb i
    · rw [Subsingleton.elim i (0 : Fin 1)]
      exact hd

theorem isRVSet_of_rvEquiv {J : Type} {D : Set (I → X .rv)} {B : Set (J → X .rv)}
    (h : RVDefinablyEquivalent M S.carrier D B) : isRVSet M S B := by
  obtain ⟨e,he⟩ := h
  have ds := definable_range_of_rvGraph (fun x => (e x).val) he
  have eq : Set.range (fun x => (e x).val) = B := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).property
    · intro hy
      obtain ⟨x,hx⟩ := e.surjective ⟨y,hy⟩
      exact ⟨x,congrArg Subtype.val hx⟩
  unfold isRVSet
  rwa [eq] at ds

end GeneralizedEuler.Section5
