module

public import Section4.FixedBasePartitions

/-! Transport definable RV sets along automorphisms of the RV reduct.
Only the parameters in the RV sort have to be fixed. -/
public section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
universe z a
variable {L : Language} {E : Type*} {Z : TCsort → Type z} (M : SortedStructure L E Z)

def actOnSort (g : Z .rv ≃ Z .rv) : ∀ s, Z s → Z s
  | .vf => id
  | .rv => g

structure PreservesRVReduct (g : Z .rv ≃ Z .rv) : Prop where
  op : ∀ {ss} (f : FunctionSymbol L E ss .rv) (_ : ∀ i : Fin ss.length, ss.get i = .rv)
    (u : SortedArgs Z ss), g (M.funMap f u) = M.funMap f (fun i => actOnSort g _ (u i))
  unitRel : ∀ u, M.relMap .residueNonzero (fun i => actOnSort g _ (u i)) ↔
    M.relMap .residueNonzero u
  orderRel : ∀ u, M.relMap .rvLE (fun i => actOnSort g _ (u i)) ↔ M.relMap .rvLE u

namespace PreservesRVReduct
variable {M} {g : Z .rv ≃ Z .rv} (h : PreservesRVReduct M g)
  {Var : TCsort → Type a} (x : ∀ s, Var s → Z s)

include h

theorem term {s} {t : SortedTerm L E Var s} (ht : t.IsRVOnly) :
    t.realize M (fun s => actOnSort g s ∘ x s) = actOnSort g s (t.realize M x) := by
  induction ht with
  | var => rfl
  | app f ts ht ih =>
    exact (congrArg (M.funMap f) (funext ih)).trans ((h.op f (fun i => (ht i).sort_eq) _).symm)

theorem formula {φ : SortedFormula L E Var} (hφ : φ.IsRVOnly) :
    φ.realize M (fun s => actOnSort g s ∘ x s) ↔ φ.realize M x := by
  induction hφ with
  | falsum => rfl
  | equal ht hu =>
    change _ = _ ↔ _ = _
    rw [h.term x ht,h.term x hu]
    exact g.injective.eq_iff
  | residueNonzero ht =>
    exact (congrArg (M.relMap .residueNonzero) (funext fun i => h.term x (ht i))).to_iff.trans (h.unitRel _)
  | rvLE ht =>
    exact (congrArg (M.relMap .rvLE) (funext fun i => h.term x (ht i))).to_iff.trans (h.orderRel _)
  | imp _ _ ih ik => exact imp_congr ih ik

/-- Apply fixed-base quantifier elimination before transport. The field
components of the substructure need no action. -/
theorem setInvariant {I : Type} (S : SortedSubstructure M)
    (fixed : ∀ a : S.carrier .rv, g a.val = a.val)
    (qe : ∀ φ : SortedFormula L E (FullRVVariables S I),
      ∃ q : SortedFormula L E (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    {U : Set (I → Z .rv)} (hu : isRVSet M S U) (t : I → Z .rv) :
    g ∘ t ∈ U ↔ t ∈ U := by
  let ass (t : I → Z .rv) : ∀ s, RVVariables I s → Z s
    | .vf => PEmpty.elim
    | .rv => t
  obtain ⟨φ,hφ,spec⟩ := exists_rv_formula_of_definable S hu qe
  have action : reductRVAssignment S (g ∘ t) =
      (fun s => actOnSort g s ∘ reductRVAssignment S t s) := by
    funext s i
    cases s with
    | vf => exact i.elim
    | rv =>
      rcases i with a | j
      · exact (fixed a).symm
      · rfl
  apply (spec (ass (g ∘ t))).trans
  change φ.realize M (reductRVAssignment S (g ∘ t)) ↔ t ∈ U
  rw [action]
  exact (h.formula (reductRVAssignment S t) hφ).trans (spec (ass t)).symm

end PreservesRVReduct

section Canonical
variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A multiplicative automorphism fixing the residue field commutes with every
residue language function, including its extension by zero off the domain. -/
theorem commutes_residue_operation (g : RV0 O ≃* RV0 O)
    (fixed : ∀ r, g (residueRV O r) = residueRV O r)
    {n : ℕ} (f : (Fin n → Residue O) → Residue O) (u : Fin n → RV0 O) :
    g (extendResidueOperation O f u) = extendResidueOperation O f (g ∘ u) := by
  classical
  by_cases hu : ∀ i, u i ∈ Set.range (residueRV O)
  · choose r hr using hu
    have he : u = residueRV O ∘ r := (funext hr).symm
    have hg : g ∘ u = u := by
      funext i; change g (u i) = u i; rw [← hr i]; exact fixed _
    rw [hg,he,extendResidueOperation_on_residue,fixed]
  · push Not at hu
    obtain ⟨i,hi⟩ := hu
    have ho : (g ∘ u) i ∉ Set.range (residueRV O) := by
      rintro ⟨r,hr⟩
      exact hi ⟨r,g.injective ((fixed r).trans hr)⟩
    rw [extendResidueOperation_off_residue O f ⟨i,hi⟩,
      extendResidueOperation_off_residue O f ⟨i,ho⟩,map_zero]

theorem preserves_canonical_reduct (g : RV0 O ≃* RV0 O)
    (fixed : ∀ r, g (residueRV O r) = residueRV O r)
    (powers : ∀ e t, g (P e t) = P e (g t))
    (value : ∀ t, unsignedValue O (g t) = unsignedValue O t)
    (order : ∀ t u, (rvLinearOrder O hO).le (g t) (g u) ↔ (rvLinearOrder O hO).le t u) :
    PreservesRVReduct (canonicalStructure (L := L) O hO P) g.toEquiv where
  op := by
    intro ss f hs u
    cases f with
    | rvZero => exact map_zero g
    | rvOne => exact map_one g
    | rvMul => exact map_mul g _ _
    | rvInv => exact map_inv₀ g _
    | power e => exact powers e _
    | rv => cases hs 0
    | residue f =>
      change g (extendResidueOperation O _ (homogeneousArgs u)) =
        extendResidueOperation O _ (homogeneousArgs (fun i => actOnSort g.toEquiv _ (u i)))
      rw [homogeneousArgs_map]
      exact commutes_residue_operation O g fixed _ _
  unitRel := fun u => by
    change unsignedValue O (g (u 0)) = 1 ↔ unsignedValue O (u 0) = 1
    rw [value]
  orderRel := fun u => order _ _
end Canonical

end GeneralizedEuler.Section4
