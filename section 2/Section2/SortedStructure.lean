module

public import Section2.Language
public import Section2.LeadingTermPower
public import Section2.ResidueOrder

/-! Two-sorted structures and the canonical interpretation of the
reviewed VF and RV symbols. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

/-- A tuple indexed by a list of argument sorts. -/
abbrev SortedArgs (X : TCsort → Type z) (ss : List TCsort) :=
  (i : Fin ss.length) → X (ss.get i)

def homogeneousArgs {X : TCsort → Type z} {s : TCsort} {n : ℕ}
    (xs : SortedArgs X (List.replicate n s)) (i : Fin n) : X s := by
  let j : Fin (List.replicate n s).length := ⟨i.val, by simp⟩
  have h : (List.replicate n s).get j = s := by simp [List.get_eq_getElem]
  exact h ▸ xs j

theorem homogeneousArgs_map {X : TCsort → Type*} {Y : TCsort → Type*}
    {s : TCsort} {n : ℕ} (f : ∀ t, X t → Y t)
    (xs : SortedArgs X (List.replicate n s)) :
    homogeneousArgs (fun i => f _ (xs i)) = f s ∘ homogeneousArgs xs := by
  have commute {a b : TCsort} (h : a = b) (x : X a) :
      (h ▸ f a x : Y b) = f b (h ▸ x) := by cases h; rfl
  funext i
  exact commute _ _

theorem homogeneousArgs_const {A : Type*} {s : TCsort} {n : ℕ}
    (xs : Fin (List.replicate n s).length → A) (i : Fin n) :
    homogeneousArgs (X := fun _ => A) (s := s) xs i =
      xs (Fin.cast (List.length_replicate).symm i) := by
  simp only [homogeneousArgs, eq_rec_constant]
  rfl

/-- Turn a homogeneous tuple into the list-indexed arguments of a symbol. -/
def expandHomogeneousArgs {X : TCsort → Type*} {s : TCsort} {n : ℕ}
    (xs : Fin n → X s) (j : Fin (List.replicate n s).length) : X ((List.replicate n s).get j) := by
  have h : (List.replicate n s).get j = s := by simp [List.get_eq_getElem]
  exact h.symm ▸ xs (Fin.cast List.length_replicate j)

theorem homogeneousArgs_expand {X : TCsort → Type*} {s : TCsort} {n : ℕ}
    (xs : Fin n → X s) : homogeneousArgs (expandHomogeneousArgs xs) = xs := by
  have undo {t s : TCsort} (h : t = s) (x : X s) : h ▸ (h.symm ▸ x : X t) = x := by
    cases h
    rfl
  funext i
  simp only [homogeneousArgs, expandHomogeneousArgs, undo]
  rfl

structure SortedStructure (L : Language.{u, v}) (E : Type w) (X : TCsort → Type z) where
  funMap : ∀ {ss s}, FunctionSymbol L E ss s → SortedArgs X ss → X s
  relMap : ∀ {ss}, RelationSymbol L ss → SortedArgs X ss → Prop

/-- The field and leading-term carriers of the canonical expansion. -/
abbrev CanonicalSort {K : Type z} [Field K] (O : ValuationSubring K) : TCsort → Type z
  | .vf => K
  | .rv => RV0 O

section

variable {K : Type z} [Field K] (O : ValuationSubring K)

/-- Extend a residue-field operation to RV₀ by returning zero when any
argument lies outside the embedded residue field. -/
def extendResidueOperation {n : ℕ} (f : (Fin n → Residue O) → Residue O)
    (a : Fin n → RV0 O) : RV0 O := by
  classical
  exact if ∀ i, a i ∈ Set.range (residueRV O) then residueRV O (f (rvResidue O ∘ a)) else 0

theorem extendResidueOperation_of_mem_range {n : ℕ}
    (f : (Fin n → Residue O) → Residue O) {a : Fin n → RV0 O}
    (h : ∀ i, a i ∈ Set.range (residueRV O)) :
    extendResidueOperation O f a = residueRV O (f (rvResidue O ∘ a)) := by
  classical
  exact ite_eq_left h

theorem extendResidueOperation_on_residue {n : ℕ} (f : (Fin n → Residue O) → Residue O)
    (a : Fin n → Residue O) :
    extendResidueOperation O f (residueRV O ∘ a) = residueRV O (f a) := by
  classical
  have h : ∀ i, (residueRV O ∘ a) i ∈ Set.range (residueRV O) := fun i => ⟨a i, rfl⟩
  rw [extendResidueOperation, ite_eq_left h]
  congr 2
  funext i
  exact rvResidue_residueRV O (a i)

theorem extendResidueOperation_off_residue {n : ℕ} (f : (Fin n → Residue O) → Residue O)
    {a : Fin n → RV0 O} (h : ∃ i, a i ∉ Set.range (residueRV O)) :
    extendResidueOperation O f a = 0 := by
  classical
  obtain ⟨i, hi⟩ := h
  exact ite_eq_right (fun hall => hi (hall i))

variable {L : Language.{u, v}} [L.Structure K] [L.Structure (Residue O)]
  [LinearOrder K] [IsStrictOrderedRing K] {E : Type w}

/-- The two-sorted interpretation associated to a convex valuation ring,
its chosen residue T-structure, and the descended power operations. -/
@[expose]
def canonicalStructure (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O) :
    SortedStructure L E (CanonicalSort O) where
  funMap
    | .vf f, xs => Language.Structure.funMap f (homogeneousArgs xs)
    | .rvZero, _ => 0
    | .rvOne, _ => 1
    | .rvMul, xs => @Mul.mul (RV0 O) inferInstance (xs 0) (xs 1)
    | .rvInv, xs => @Inv.inv (RV0 O) inferInstance (xs 0)
    | .residue f, xs => extendResidueOperation O (Language.Structure.funMap f) (homogeneousArgs xs)
    | .power e, xs => P e (xs 0)
    | .rv, xs => rv O (xs 0)
  relMap
    | .vf r, xs => Language.Structure.RelMap r (homogeneousArgs xs)
    | .residueNonzero, xs => unsignedValue O (xs 0) = 1
    | .rvLE, xs => (rvLinearOrder O hO).le (xs 0) (xs 1)

end

end GeneralizedEuler.Section2
