module

public import Section2.LeadingTermPresentation
public import Section2.GeneratedSubstructure

/-! Identifying a presented RV expansion with the canonical expansion. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z

abbrev PresentedSort (K R : Type z) : TCsort → Type z
  | .vf => K
  | .rv => R

variable {K R : Type z} [Field K] [CommGroupWithZero R] (O : ValuationSubring K)
  (p : LeadingTermPresentation (R := R) O)

theorem LeadingTermPresentation.equiv_zero : p.equiv O 0 = 0 := by
  calc
    p.equiv O 0 = p.equiv O (rv O 0) := congrArg (p.equiv O) (map_zero (rv O)).symm
    _ = p.projection 0 := p.equiv_rv O 0
    _ = 0 := map_zero p.projection

theorem LeadingTermPresentation.equiv_inv (x : RV0 O) : p.equiv O x⁻¹ = (p.equiv O x)⁻¹ := by
  obtain ⟨a, rfl⟩ := rv_surjective O x
  rw [← rv_inv, p.equiv_rv, p.equiv_rv, map_inv₀]

/-- Compatibility with the residue map on units fixes the embedding of
the residue field into any presented RV sort. -/
theorem LeadingTermPresentation.equiv_residue (ι : Residue O ↪ R) (hZero : ι 0 = 0)
    (hred : ∀ x : O, IsLocalRing.residue O x ≠ 0 →
      ι (IsLocalRing.residue O x) = p.projection x.val) (r : Residue O) :
    p.equiv O (residueRV O r) = ι r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [residueRV_zero, p.equiv_zero O, hZero]
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective r
  rw [← hx, residueRV_residue_of_ne_zero O x (hx.trans_ne hr), p.equiv_rv]
  exact (hred x (hx.trans_ne hr)).symm

variable {L : Language.{u, v}} {E : Type w} [L.Structure K] [L.Structure (Residue O)]
  [LinearOrder R]

/-- In a presented RV sort the operations are the group operations, the
named powers, and the residue functions extended by zero. -/
def presentedStructure (ι : Residue O ↪ R) (reduce : R → Residue O) (Q : E → R → R) :
    SortedStructure L E (PresentedSort K R) where
  funMap
    | .vf f, a => Structure.funMap f (homogeneousArgs a)
    | .rvZero, _ => 0
    | .rvOne, _ => 1
    | .rvMul, a => @Mul.mul R inferInstance (a 0) (a 1)
    | .rvInv, a => @Inv.inv R inferInstance (a 0)
    | .residue f, a => by
      classical
      let x := homogeneousArgs a
      exact if ∀ i, x i ∈ Set.range ι then ι (Structure.funMap (L := L) f (reduce ∘ x)) else 0
    | .power e, a => Q e (a 0)
    | .rv, a => p.projection (a 0)
  relMap
    | .vf r, a => Structure.RelMap r (homogeneousArgs a)
    | .rvLE, a => @LE.le R inferInstance (a 0) (a 1)
    | .residueNonzero, a => a 0 ∈ Set.range ι ∧ a 0 ≠ (0 : R)

variable [LinearOrder K] [IsStrictOrderedRing K]

set_option linter.style.haveILetI false in
/-- Positive representative formulas and the extension by zero force
the same power operation in the presented and canonical quotients. -/
theorem LeadingTermPresentation.equiv_power_of_representatives (hO : IsOrderConvex O)
    (hord : ∀ x y : K, p.projection x < p.projection y ↔
      x < y ∧ p.projection x ≠ p.projection y)
    (g : PositiveField K →* PositiveField K) (P : RV0 O → RV0 O) (Q : R → R)
    (hP : AgreesWithFieldPower O g P) (hP₀ : ∀ t, ¬IsPositiveRV O t → P t = 0)
    (hQ : ∀ x : PositiveField K, Q (p.projection x.val) = p.projection (g x).val)
    (hQ₀ : ∀ t, t ≤ 0 → Q t = 0) (t : RV0 O) : p.equiv O (P t) = Q (p.equiv O t) := by
  letI := rvLinearOrder O hO
  obtain ⟨x, rfl⟩ := rv_surjective O t
  by_cases hx : 0 < x
  · let y : PositiveField K := ⟨x, hx⟩
    rw [hP y, p.equiv_rv, p.equiv_rv]
    exact (hQ y).symm
  · have hrv : rv O x ≤ 0 := not_lt.mp (fun h => hx ((zero_lt_rv_iff O hO).mp h))
    have hq := (p.equiv_strictMono O hO hord).monotone hrv
    rw [p.equiv_rv, p.equiv_zero O] at hq
    rw [hP₀ _ ((isPositiveRV_rv_iff O hO).not.mpr hx), p.equiv_zero O,
      p.equiv_rv, hQ₀ _ hq]

private def presentedSortEquiv (s : TCsort) : CanonicalSort O s ≃ PresentedSort K R s :=
  match s with
  | .vf => Equiv.refl K
  | .rv => (p.equiv O).toEquiv

set_option linter.style.haveILetI false in
/-- The identification of the quotient respects the entire sorted
signature as soon as the residue and power interpretations agree on
representatives. -/
def canonicalIsomorphismToPresentation (hO : IsOrderConvex O)
    (ι : Residue O ↪ R) (reduce : R → Residue O) (hreduce : Function.LeftInverse reduce ι)
    (hι : ∀ r, p.equiv O (residueRV O r) = ι r)
    (hord : ∀ x y : K, p.projection x < p.projection y ↔
      x < y ∧ p.projection x ≠ p.projection y)
    (P : E → RV0 O → RV0 O) (Q : E → R → R)
    (hP : ∀ e t, p.equiv O (P e t) = Q e (p.equiv O t)) :
    SortedIsomorphism (canonicalStructure (L := L) O hO P) (presentedStructure O p ι reduce Q) := by
  classical
  letI := rvLinearOrder O hO
  have range_iff (t : RV0 O) : p.equiv O t ∈ Set.range ι ↔ t ∈ Set.range (residueRV O) := by
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, (p.equiv O).injective ((hι r).trans hr)⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, (hι r).symm⟩
  have reduction (t : RV0 O) (ht : t ∈ Set.range (residueRV O)) :
      reduce (p.equiv O t) = rvResidue O t := by
    obtain ⟨r, rfl⟩ := ht
    rw [hι, rvResidue_residueRV, hreduce]
  have hnonzero (t : RV0 O) :
      (p.equiv O t ∈ Set.range ι ∧ p.equiv O t ≠ 0) ↔ unsignedValue O t = 1 := by
    rw [range_iff, range_residueRV, Set.mem_ofPred_eq]
    by_cases ht : t = 0
    · simp only [ht, p.equiv_zero O, map_zero, ne_eq, not_true_eq_false, and_false, zero_ne_one]
    · have ht' : p.equiv O t ≠ 0 := fun h => ht ((p.equiv O).injective (h.trans (p.equiv_zero O).symm))
      simp only [ht, false_or]
      exact ⟨And.left, fun h => ⟨h, ht'⟩⟩
  let e (s : TCsort) := presentedSortEquiv O p s
  let applySort (s : TCsort) : CanonicalSort O s → PresentedSort K R s := (e s).toFun
  refine { toEmbedding := fun s => (e s).toEmbedding, surjective := fun s => (e s).surjective
           map_fun := ?_, map_rel := ?_ }
  · intro ss s f a
    cases f with
    | vf f =>
      change Structure.funMap f (homogeneousArgs a) =
        Structure.funMap f (homogeneousArgs (fun i => applySort _ (a i)))
      rw [homogeneousArgs_map applySort]
      rfl
    | rvZero => exact p.equiv_zero O
    | rvOne => exact map_one (p.equiv O)
    | rvMul => exact map_mul (p.equiv O) _ _
    | rvInv => exact p.equiv_inv O _
    | rv => exact p.equiv_rv O _
    | power i => exact hP i _
    | residue f =>
      let x := homogeneousArgs a
      change p.equiv O (extendResidueOperation O (Structure.funMap f) x) =
        if ∀ i, (homogeneousArgs (fun j => applySort _ (a j))) i ∈ Set.range ι then
          ι (Structure.funMap f (reduce ∘ homogeneousArgs (fun j => applySort _ (a j)))) else 0
      rw [homogeneousArgs_map applySort]
      change p.equiv O (extendResidueOperation O (Structure.funMap f) x) =
        if ∀ i, p.equiv O (x i) ∈ Set.range ι then
          ι (Structure.funMap f (reduce ∘ (p.equiv O) ∘ x)) else 0
      by_cases hx : ∀ i, x i ∈ Set.range (residueRV O)
      · have h' := fun i => (range_iff (x i)).mpr (hx i)
        rw [ite_eq_left h', extendResidueOperation_of_mem_range O _ hx, hι]
        have he : reduce ∘ (p.equiv O) ∘ x = rvResidue O ∘ x :=
          funext fun i => reduction (x i) (hx i)
        rw [he]
      · obtain ⟨i, hi⟩ := not_forall.mp hx
        rw [ite_eq_right (fun h => hi ((range_iff _).mp (h i)))]
        rw [extendResidueOperation_off_residue O _ ⟨i, hi⟩, p.equiv_zero O]
  · intro ss r a
    cases r with
    | vf r =>
      change Structure.RelMap r (homogeneousArgs (fun i => applySort _ (a i))) ↔
        Structure.RelMap r (homogeneousArgs a)
      rw [homogeneousArgs_map applySort]
      rfl
    | residueNonzero => exact hnonzero _
    | rvLE => exact (p.equiv_strictMono O hO hord).le_iff_le

/-- Over the given field, the residue and power matching conditions
produce an isomorphism with the canonical expansion. -/
def canonicalIsomorphismOfMatching (hO : IsOrderConvex O)
    (ι : Residue O ↪ R) (hZero : ι 0 = 0) (reduce : R → Residue O)
    (hreduce : Function.LeftInverse reduce ι)
    (hred : ∀ x : O, IsLocalRing.residue O x ≠ 0 →
      ι (IsLocalRing.residue O x) = p.projection x.val)
    (hord : ∀ x y : K, p.projection x < p.projection y ↔
      x < y ∧ p.projection x ≠ p.projection y)
    (g : E → PositiveField K →* PositiveField K)
    (P : E → RV0 O → RV0 O) (Q : E → R → R)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hP₀ : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hQ : ∀ e (x : PositiveField K), Q e (p.projection x.val) = p.projection (g e x).val)
    (hQ₀ : ∀ e t, t ≤ 0 → Q e t = 0) :
    SortedIsomorphism (canonicalStructure (L := L) O hO P) (presentedStructure O p ι reduce Q) :=
  canonicalIsomorphismToPresentation O p hO ι reduce hreduce (p.equiv_residue O ι hZero hred) hord P Q
    (fun e => p.equiv_power_of_representatives O hO hord (g e) (P e) (Q e)
      (hP e) (hP₀ e) (hQ e) (hQ₀ e))

/-- An embedding that fixes the field must agree pointwise with the
canonical identification on RV. -/
theorem embedding_eq_quotientOnRV_of_fixed_field (hO : IsOrderConvex O)
    (ι : Residue O ↪ R) (reduce : R → Residue O)
    (P : E → RV0 O → RV0 O) (Q : E → R → R)
    (e : SortedEmbedding (canonicalStructure (L := L) O hO P) (presentedStructure O p ι reduce Q))
    (hVF : ∀ x : K, e.toEmbedding .vf x = x) (t : RV0 O) : e.toEmbedding .rv t = p.equiv O t := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  let args : SortedArgs (CanonicalSort O) [.vf] := fun i => by
    have hi : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
    subst i
    exact x
  have h := e.map_fun .rv args
  change e.toEmbedding .rv (rv O x) = p.projection (e.toEmbedding .vf x) at h
  rw [hVF] at h
  exact h.trans (p.equiv_rv O x).symm

end GeneralizedEuler.Section2
