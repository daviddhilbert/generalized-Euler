module

public import Section3.DefinableTags
public import Section2.SeparatedSets
public import Section2.RVDefinableEquivalence
public import Section2.DimensionWithBot
public import Mathlib.Order.Fin.Finset

/-! Objects in the four categories and the finite-fiber enumeration. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder

variable {L : Language} {E : Type*} {Z : TCsort → Type*}
variable (M : SortedStructure L E Z) (S : SortedSubstructure M)

@[expose] def isRVSet {I : Type} (D : Set (I → Z .rv)) : Prop :=
  SortedDefinableOver M S.carrier {a : ∀ s, RVVariables I s → Z s | a .rv ∈ D}

structure RVObject (k : ℕ) where
  arity : ℕ
  carrier : Set (Fin arity → Z .rv)
  definable : isRVSet M S carrier
  label : carrier → Fin k → Z .rv
  graph : SortedDefinableOver M S.carrier (rvGraph label)
  nonzero : ∀ x j, label x j ≠ M.funMap .rvZero (fun i => i.elim0)
  finiteFibers : ∀ y, (label ⁻¹' {y}).Finite

def RVObject.Isomorphic {k : ℕ} (U V : RVObject M S k) : Prop :=
  RVDefinablyEquivalent M S.carrier U.carrier V.carrier

def RVObject.IsResidue {Γ : Type*} (value : Z .rv → Γ) {k : ℕ} (U : RVObject M S k) : Prop :=
  (Set.range (fun x : U.carrier => value ∘ x.val)).Finite

structure ValueObject {Γ : Type*} (definable : ∀ k, Set (Fin k → Γ) → Prop) (k : ℕ) where
  tags : ℕ
  piece : Fin tags → Set (Fin k → Γ)
  isDefinable : ∀ i, definable k (piece i)

def ValueObject.IsFinite {Γ : Type*} {P : ∀ k, Set (Fin k → Γ) → Prop} {k}
    (A : ValueObject P k) : Prop := ∀ i, (A.piece i).Finite

structure FieldObject [TopologicalSpace (Z .vf)] (k : ℕ) where
  vfArity : ℕ
  rvArity : ℕ
  carrier : Set (∀ s, MixedVariables vfArity (Fin rvArity) s → Z s)
  definable : SortedDefinableOver M S.carrier carrier
  dimension : vfDimension (mixedTuple '' carrier) ≤ k
  finiteFibers : ∀ b : Fin vfArity → Z .vf,
    {r : Fin rvArity → Z .rv | (b,r) ∈ mixedTuple '' carrier}.Finite

section Enumeration
variable {A B : Type*} [LinearOrder A] (f : A → B)
  (fib : B → Finset A) (hf : ∀ x y, x ∈ fib y ↔ f x = y)
  {N : ℕ} (bound : ∀ y, (fib y).card ≤ N)

private def tagOf (x : A) : Fin N :=
  Fin.castLE (bound (f x)) ((fib (f x)).orderIsoOfFin rfl |>.symm ⟨x, (hf x _).mpr rfl⟩)

private theorem tagOf_val (x : A) (y : B) (h : f x = y) :
    (tagOf f fib hf bound x).val =
    (((fib y).orderIsoOfFin rfl).symm ⟨x,(hf x y).mpr h⟩).val := by
  subst y
  rfl

/-- The tag records the position in the ordered fiber. No ambient zero is
introduced, including when the structure map has target arity zero. -/
def enumerateFibers :
    A ≃ {p : Fin N × B // p.1.val < (fib p.2).card} where
  toFun x := ⟨(tagOf f fib hf bound x, f x), (((fib (f x)).orderIsoOfFin rfl).symm ⟨x,(hf x _).mpr rfl⟩).isLt⟩
  invFun p := ((fib p.val.2).orderIsoOfFin rfl ⟨p.val.1.val,p.property⟩).val
  left_inv x := by
    change ((fib (f x)).orderIsoOfFin rfl (((fib (f x)).orderIsoOfFin rfl).symm _)).val = _
    rw [OrderIso.apply_symm_apply]
  right_inv p := by
    rcases p with ⟨⟨i,y⟩,hi⟩
    let x := (fib y).orderIsoOfFin rfl ⟨i.val,hi⟩
    have hx : f x.val = y := (hf _ _).mp x.property
    apply Subtype.ext
    refine Prod.ext (Fin.ext ?_) hx
    change (tagOf f fib hf bound x.val).val = i.val
    rw [tagOf_val f fib hf bound x.val y hx]
    exact congrArg Fin.val ((fib y).orderIsoOfFin rfl |>.symm_apply_apply ⟨i.val,hi⟩)

end Enumeration

/-- Finite separated rectangles give finitely many distinct fibers (4.17).
The fiber is constant on each membership pattern of the residue factors. -/
theorem finite_value_fibers {A B : Type*} {P : Set A → Prop} {Q : Set B → Prop}
    {D : Set (A × B)} (h : SeparatedSets P Q D) :
    (Set.range fun a => {b | (a,b) ∈ D}).Finite := by
  induction h with
  | empty =>
    apply (Set.finite_singleton (∅ : Set B)).subset
    rintro _ ⟨a,rfl⟩
    rfl
  | @insert U V D _ _ _ ih =>
    let fibers := Set.range fun a => {b | (a,b) ∈ D}
    apply (ih.union (ih.image (fun s => V ∪ s))).subset
    rintro _ ⟨a,rfl⟩
    by_cases ha : a ∈ U
    · right
      exact ⟨_,⟨a,rfl⟩,Set.ext fun b => by simp [ha]⟩
    · left
      exact ⟨a,Set.ext fun b => by simp [ha]⟩

end GeneralizedEuler.Section4
