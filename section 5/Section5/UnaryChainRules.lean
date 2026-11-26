module

public import Section5.MixedGraphIsomorphisms
public import Section5.DefinableUnaryShears

/-! Relatively unary factorizations are closed under composition,
inversion, and passage from finitely many definable pieces to their union. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ}

abbrev MixedCarrier (X : TCsort → Type z) (n : ℕ) (I : Type) :=
  Set (SortedAssignment X (MixedVariables n I))

/-- Fixing outside a set of moving coordinates includes preservation
of all field coordinates when the set is empty. -/
@[expose] def FixesOutside {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
    (f : MixedGraphIso M S A B) (moving : Finset (Fin n)) : Prop :=
  ∀ x : A, ∀ j ∉ moving, (f.equiv x).val .vf j = x.val .vf j

inductive UnaryPiecewise (M : SortedStructure L E X) (S : SortedSubstructure M) (n : ℕ) :
    Finset (Fin n) → {I J : Type} → {A : MixedCarrier X n I} → {B : MixedCarrier X n J} →
      MixedGraphIso M S A B → Prop
  | fixed {moving : Finset (Fin n)} {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      (f : MixedGraphIso M S A B) (h : FixesOutside f ∅) : UnaryPiecewise M S n moving f
  | unary {moving : Finset (Fin n)} {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      (f : MixedGraphIso M S A B) (i : Fin n) (hi : i ∈ moving)
      (h : FixesOutside f {i}) : UnaryPiecewise M S n moving f
  | trans {moving : Finset (Fin n)} {I J T : Type} [Finite J]
      {A : MixedCarrier X n I} {B : MixedCarrier X n J} {C : MixedCarrier X n T}
      {f : MixedGraphIso M S A B} {g : MixedGraphIso M S B C}
      (hf : UnaryPiecewise M S n moving f) (hg : UnaryPiecewise M S n moving g) :
      UnaryPiecewise M S n moving (f.trans g)
  | symm {moving : Finset (Fin n)} {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      {f : MixedGraphIso M S A B} (hf : UnaryPiecewise M S n moving f) :
      UnaryPiecewise M S n moving f.symm
  | widen {small big : Finset (Fin n)} {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      {f : MixedGraphIso M S A B} (sub : small ⊆ big) (h : UnaryPiecewise M S n small f) :
      UnaryPiecewise M S n big f
  | partition {moving : Finset (Fin n)} {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
      {f : MixedGraphIso M S A B} {q : ℕ} (D : Fin q → MixedCarrier X n I)
      (defD : ∀ i, SortedDefinableOver M S.carrier (D i)) (sub : ∀ i, D i ⊆ A)
      (disj : Pairwise (fun i j => Disjoint (D i) (D j))) (cover : (⋃ i, D i) = A)
      (piece : ∀ i, UnaryPiecewise M S n moving (f.restrict (sub i) (defD i))) :
      UnaryPiecewise M S n moving f

theorem UnaryPiecewise.fixesOutside {I J : Type} {A : MixedCarrier X n I} {B : MixedCarrier X n J}
    {f : MixedGraphIso M S A B} {moving : Finset (Fin n)} (h : UnaryPiecewise M S n moving f) :
    FixesOutside f moving := by
  induction h with
  | fixed _ h =>
    exact fun x j _ => h x j (Finset.notMem_empty j)
  | unary _ i hi h =>
    intro x j hj
    exact h x j (fun hm => hj ((Finset.mem_singleton.1 hm).symm ▸ hi))
  | trans _ _ hf hg =>
    intro x i hi
    exact (hg _ i hi).trans (hf x i hi)
  | @symm _ _ _ A B f _ hf =>
    intro y i hi
    have e := hf (f.equiv.symm y) i hi
    rw [f.equiv.apply_symm_apply] at e
    exact e.symm
  | widen sub _ h =>
    exact fun x i hi => h x i (fun e => hi (sub e))
  | partition D defD sub _ cover _ ih =>
    intro x i hi
    have h : x.val ∈ ⋃ j, D j := cover.symm ▸ x.property
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 h
    exact ih j ⟨x.val,hj⟩ i hi

end GeneralizedEuler.Section5
