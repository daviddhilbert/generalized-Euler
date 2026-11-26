module

public import Section5.UnaryChainRules

/-! A class invariant that respects relatively unary maps and definable
cuts respects a whole piecewise unary factorization. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ}

theorem MixedGraphIso.rangeOver_partition
    {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
    (f : MixedGraphIso M S A B) {q : ℕ}
    (D : Fin q → MixedCarrier X n I) (sub : ∀ i, D i ⊆ A)
    (disj : Pairwise (fun i j => Disjoint (D i) (D j))) (cover : (⋃ i, D i) = A) :
    Pairwise (fun i j => Disjoint (f.rangeOver (sub i)) (f.rangeOver (sub j))) ∧
      (⋃ i, f.rangeOver (sub i)) = B := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.2
    rintro b ⟨x,eq⟩ ⟨y,eq'⟩
    have h : (⟨x.val,sub i x.property⟩ : A) = ⟨y.val,sub j y.property⟩ :=
      f.equiv.injective (Subtype.ext (eq.trans eq'.symm))
    have hout := congrArg (fun a : A => a.val) h
    exact Set.disjoint_left.1 (disj hij) x.property (hout.symm ▸ y.property)
  · ext b
    constructor
    · intro h
      obtain ⟨i,x,rfl⟩ := Set.mem_iUnion.1 h
      exact (f.equiv ⟨x.val,sub i x.property⟩).property
    · intro hb
      let x := f.equiv.symm ⟨b,hb⟩
      have h : x.val ∈ ⋃ i, D i := cover.symm ▸ x.property
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 h
      exact Set.mem_iUnion.2 ⟨i,⟨x.val,hi⟩,congrArg Subtype.val (f.equiv.apply_symm_apply _)⟩

theorem UnaryPiecewise.eq_of_scissor_invariant {R : Type*} [AddCommMonoid R]
    (value : {I : Type} → MixedCarrier X n I → R)
    (scissors : ∀ {I : Type} {A : MixedCarrier X n I} {q : ℕ} (D : Fin q → MixedCarrier X n I),
      (∀ i, SortedDefinableOver M S.carrier (D i)) →
      Pairwise (fun i j => Disjoint (D i) (D j)) → (⋃ i, D i) = A → value A = ∑ i, value (D i))
    (fixed : ∀ {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      (f : MixedGraphIso M S A B), FixesOutside f ∅ → value A = value B)
    (unary : ∀ {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      (f : MixedGraphIso M S A B) (k : Fin n), FixesOutside f {k} → value A = value B)
    {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
    {moving : Finset (Fin n)} {f : MixedGraphIso M S A B} (h : UnaryPiecewise M S n moving f) :
    Finite I → Finite J → value A = value B := by
  induction h with
  | fixed f h => exact fun _ _ => fixed f h
  | unary f k _ h => exact fun _ _ => unary f k h
  | trans _ _ hf hg => exact fun fi fj => (hf fi inferInstance).trans (hg inferInstance fj)
  | symm _ ih => exact fun fi fj => (ih fj fi).symm
  | widen _ _ ih => exact ih
  | @partition moving I J A B f q D defD sub disj cover _ ih =>
    intro fi fj
    let := fi
    obtain ⟨disjB,coverB⟩ := f.rangeOver_partition D sub disj cover
    have defB (i : Fin q) := (f.restrict (sub i) (defD i)).target_definable (defD i)
    rw [scissors D defD disj cover,scissors (fun i => f.rangeOver (sub i)) defB disjB coverB]
    exact Finset.sum_congr rfl (fun i _ => ih i fi fj)

end GeneralizedEuler.Section5
