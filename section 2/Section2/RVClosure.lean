module

public import Section2.RVReduct
public import Section2.RVVectorSpace
public import Section2.PositiveRVMonomials

/-! Definable closure of the RV base by elementary substructures and
the intersection of the two one-generator value extensions. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

variable {L : Language.{u, v}} {E : Type w}
  {X : TCsort → Type (max u v w z)} (M : SortedStructure L E X)

/-- Being definably closed on RV says that a unique RV point defined
using only the given RV parameters already belongs to the base. -/
def RVDefinablyClosed (W : Set (X .rv)) : Prop :=
  ∀ t, SortedDefinableOver M (fun s => match s with
      | .vf => ∅
      | .rv => W)
    {x : ∀ s, RVVariables Unit s → X s | x .rv () = t} → t ∈ W

/-- An elementary sorted substructure contains every point defined by
a unique RV solution over its RV parameters. -/
theorem rvDefinablyClosed_of_models_of_QE (T : SortedTheory L E)
    (hqe : ∀ {Var : TCsort → Type (max u v w z)} (φ : SortedFormula L E Var),
      ∃ ψ, ψ.IsQF ∧ ∀ P : T.PointedModel Var, P.realizes φ ↔ P.realizes ψ)
    (S : SortedSubstructure M) (hM : ∀ φ ∈ T, φ.realize M)
    (hS : ∀ φ ∈ T, φ.realize S.structureOn)
    (hNonempty : ∀ s, Nonempty (S.carrier s)) : RVDefinablyClosed M (S.carrier .rv) := by
  intro t ht
  let A : ∀ s, Set (X s)
    | .vf => ∅
    | .rv => S.carrier .rv
  change SortedDefinableOver M A {x : ∀ s, RVVariables Unit s → X s | x .rv () = t} at ht
  obtain ⟨φ, hφ⟩ := ht
  let p (s : TCsort) : A s → S.carrier s := fun x => ⟨x.val, by
    cases s
    · exact (Set.notMem_empty _ x.property).elim
    · exact x.property⟩
  let rename (s : TCsort) : (A s : Type (max u v w z)) ⊕ RVVariables Unit s →
      AddSortedVar (fun s => (A s : Type (max u v w z))) .rv s :=
    Sum.map id (by
      cases s
      · exact PEmpty.elim
      · exact fun _ => ⟨rfl⟩)
  let θ := φ.relabel rename
  let χ := (SortedFormula.all .rv θ.neg).neg
  let q : T.PointedModel (fun s => (A s : Type (max u v w z))) :=
    ⟨fun s => S.carrier s, S.structureOn, p, hNonempty, hS⟩
  let r : T.PointedModel (fun s => (A s : Type (max u v w z))) :=
    ⟨X, M, fun _ => Subtype.val, fun s => (hNonempty s).map Subtype.val, hM⟩
  have hθ (y : X .rv) :
      θ.realize M (extendSortedAssignment r.point y) ↔ y = t := by
    let x (s : TCsort) : RVVariables Unit s → X s := by
      cases s
      · exact PEmpty.elim
      · exact fun _ => y
    change (φ.relabel rename).realize M _ ↔ _
    rw [φ.realize_relabel]
    have he : (fun s => extendSortedAssignment r.point y s ∘ rename s) =
        (fun s => Sum.elim Subtype.val (x s)) := by
      funext s i
      cases s <;> rcases i with c | i
      · rfl
      · exact i.elim
      · rfl
      · rfl
    rw [he]
    exact (hφ x).symm
  have hr : r.realizes χ := by
    change χ.realize M r.point
    rw [SortedFormula.realize_neg]
    intro h
    exact (θ.realize_neg M (extendSortedAssignment r.point t)).mp (h t) ((hθ t).mpr rfl)
  obtain ⟨ψ, hψ, hχ⟩ := hqe χ
  have hmap : S.inclusion.mapAssignment q.point = r.point := by
    funext s i
    rw [SortedEmbedding.mapAssignment_apply, SortedSubstructure.inclusion_apply]
  have hqψ : q.realizes ψ := by
    have h := S.inclusion.realize_qf hψ q.point
    rw [hmap] at h
    exact h.mp ((hχ r).mp hr)
  have hq := (hχ q).mpr hqψ
  change χ.realize S.structureOn q.point at hq
  rw [SortedFormula.realize_neg] at hq
  by_contra hn
  apply hq
  intro y
  apply (θ.realize_neg S.structureOn (extendSortedAssignment q.point y)).mpr
  intro hy
  obtain ⟨ρ, hρ, hθρ⟩ := hqe θ
  let q' := q.extend .rv y
  let r' := r.extend .rv y.val
  have hq' : q'.realizes ρ := (hθρ q').mp hy
  have hmap' : S.inclusion.mapAssignment q'.point = r'.point := by
    change S.inclusion.mapAssignment (extendSortedAssignment q.point y) =
      extendSortedAssignment r.point y.val
    funext s i
    rw [SortedEmbedding.mapAssignment_apply, SortedSubstructure.inclusion_apply]
    rcases i with v | i
    · rfl
    · cases i with
      | up e =>
        cases e
        rfl
  have hr' : r'.realizes ρ := by
    have h := S.inclusion.realize_qf hρ q'.point
    rw [hmap'] at h
    exact h.mpr hq'
  exact hn ((hθ y.val).mp ((hθρ r').mpr hr') ▸ y.property)

/-- Definable closure passes to intersections. This applies to
the two elementary extensions used in the trivial-value case. -/
theorem RVDefinablyClosed.inter {U V : Set (X .rv)}
    (hU : RVDefinablyClosed M U) (hV : RVDefinablyClosed M V) : RVDefinablyClosed M (U ∩ V) := by
  intro t ht
  exact ⟨hU t (ht.mono (fun s => by cases s; exacts [Set.Subset.rfl, Set.inter_subset_left])),
    hV t (ht.mono (fun s => by cases s; exacts [Set.Subset.rfl, Set.inter_subset_right]))⟩

section Monomials

variable {K E' : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field E']
  (O : ValuationSubring K) (g : E' → PositiveField K →* PositiveField K)
  (P : E' → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

/-- The old RV coefficients multiplied by powers of a new positive
leading term. The separate RV zero remains in the set. -/
def rvOneGeneratorMonomials (W : Set (RV0 O)) (t : RV0 O) : Set (RV0 O) :=
  {x | x = 0 ∨ ∃ u ∈ W, u ≠ 0 ∧ ∃ e, x = u * P e t}

set_option linter.style.haveILetI false in
/-- If the old values are trivial and the new values are linearly
independent, the intersection of the two monomial extensions is the
old RV set. -/
theorem rvOneGeneratorMonomials_inter (W : Set (RV0 O)) (hW₀ : 0 ∈ W)
    (hW : ∀ u ∈ W, u ≠ 0 → unsignedValue O u = 1) (a b : PositiveField K)
    (hab :
      letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
      LinearIndependent E' (![positiveFieldValue O a, positiveFieldValue O b])) :
    rvOneGeneratorMonomials O P W (rv O a) ∩ rvOneGeneratorMonomials O P W (rv O b) = W := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  let hp := unsignedValue_namedPower O g P hP hzero hone hadd hmul hunit
  have h0 (x : PositiveField K) : P 0 (rv O (x : K)) = 1 := by
    rw [hP 0 x, hzero]
    exact map_one (rv O)
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · exact iff_of_true ⟨Or.inl rfl, Or.inl rfl⟩ hW₀
  constructor
  · rintro ⟨hxa, hxb⟩
    obtain ⟨u, hu, hune, e, he⟩ := hxa.resolve_left hx
    obtain ⟨v, hv, hvne, d, hd⟩ := hxb.resolve_left hx
    have hValA : unsignedValue O x = ((e • positiveFieldValue O a).toMul : O.ValueGroup) := by
      rw [he, map_mul (unsignedValue O), hW u hu hune, one_mul, hp]
    have hValB : unsignedValue O x = ((d • positiveFieldValue O b).toMul : O.ValueGroup) := by
      rw [hd, map_mul (unsignedValue O), hW v hv hvne, one_mul, hp]
    have hEq : e • positiveFieldValue O a = d • positiveFieldValue O b :=
      Additive.toMul.injective (Units.ext (hValA.symm.trans hValB))
    have hLin := linearIndependent_fin2.mp hab
    have he₀ : e = 0 := by
      by_contra hne
      have h := congrArg (e⁻¹ • ·) hEq
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hne, one_smul] at h
      exact hLin.2 (e⁻¹ * d) h.symm
    rw [he, he₀, h0, mul_one (M := RV0 O)]
    exact hu
  · intro hw
    exact ⟨Or.inr ⟨x, hw, hx, 0, by rw [h0, mul_one (M := RV0 O)]⟩,
      Or.inr ⟨x, hw, hx, 0, by rw [h0, mul_one (M := RV0 O)]⟩⟩

include hP hzero hone hadd hmul in
/-- A new leading term is recovered from any monomial using a
nonzero power of it. This is the new-value exchange calculation. -/
theorem recover_rv_of_monomial {t u x : RV0 O}
    (ht : IsPositiveRV O t) (hu : u ≠ 0) {e : E'} (he : e ≠ 0)
    (hx : x = u * P e t) : P e⁻¹ (x / u) = t := by
  have hL := leadingTermPower_scalarLaws O hP hzero hone hadd hmul ht
  have hdiv : x / u = P e t := by
    rw [hx, mul_comm (G := RV0 O) u, div_eq_mul_inv (G := RV0 O), mul_assoc (G := RV0 O),
      mul_inv_cancel₀ (G₀ := RV0 O) hu, mul_one (M := RV0 O)]
  rw [hdiv, ← hL.2.2.2, inv_mul_cancel₀ he, hL.2.1]

section Adjoin

variable {J : Language.{u, v}} [J.Structure K] [J.Structure (Residue O)]
  (hO : IsOrderConvex O) (hclamp : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

private theorem mem_sorted_cast {Y : TCsort → Type*} (D : ∀ s, Set (Y s))
    {s t : TCsort} (h : s = t) (x : Y s) : (h ▸ x : Y t) ∈ D t ↔ x ∈ D s := by
  cases h
  rfl

/-- Adjoining a positive RV generator with a new value. The residue
operations contribute only old coefficients, because a monomial of
unit value has exponent zero. -/
def adjoinNewValueRV (t : RV0 O) (ht : IsPositiveRV O t)
    (hnew : ∀ u ∈ S.carrier .rv, u ≠ 0 → ∀ e,
      unsignedValue O (u * P e t) = 1 → e = 0) :
    SortedSubstructure (canonicalStructure (L := J) O hO P) := by
  classical
  let W := S.carrier .rv
  let V := rvOneGeneratorMonomials O P W t
  let carrier (s : TCsort) : Set (CanonicalSort O s) := match s with
    | .vf => S.carrier .vf
    | .rv => V
  have hL := leadingTermPower_scalarLaws O hP hzero hone hadd hmul ht
  have old (u : RV0 O) (hu : u ∈ W) : u ∈ V := by
    rcases eq_or_ne u 0 with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ⟨u, hu, h, 0, by rw [hL.1, mul_one (M := RV0 O)]⟩
  have h0 : 0 ∈ W := S.closed .rvZero (fun i => i.elim0) (fun i => i.elim0)
  have h1 : 1 ∈ W := S.closed .rvOne (fun i => i.elim0) (fun i => i.elim0)
  have hip (e : E') : IsPositiveRV O (P e t) := leadingTermPower_pos O (hP e) ht
  have mulOld (x y : RV0 O) (hx : x ∈ W) (hy : y ∈ W) : x * y ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv, .rv] :=
      Fin.cases x (Fin.cases y (fun i => i.elim0))
    exact S.closed .rvMul args (fun i => Fin.cases hx (Fin.cases hy (fun j => j.elim0)) i)
  have powOld (e : E') (x : RV0 O) (hx : x ∈ W) : P e x ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases x (fun i => i.elim0)
    exact S.closed (.power e) args (fun i => Fin.cases hx (fun j => j.elim0) i)
  have invOld (x : RV0 O) (hx : x ∈ W) : x⁻¹ ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases x (fun i => i.elim0)
    exact S.closed .rvInv args (fun i => Fin.cases hx (fun j => j.elim0) i)
  have residueOld {x : RV0 O} (hx : x ∈ V) (hr : x ∈ Set.range (residueRV O)) : x ∈ W := by
    rcases hx with h | ⟨u, hu, hn, e, rfl⟩
    · exact h.symm ▸ h0
    rw [range_residueRV] at hr
    rcases hr with hr | hr
    · exact hr.symm ▸ h0
    · rw [hnew u hu hn e hr, hL.1, mul_one (M := RV0 O)]
      exact hu
  refine ⟨carrier, ?_⟩
  intro ss s f xs hxs
  cases f with
  | vf f =>
    apply S.closed (.vf f) xs
    intro i
    have hi : (List.replicate _ TCsort.vf).get i = .vf := by simp [List.get_eq_getElem]
    exact (mem_sorted_cast S.carrier hi (xs i)).mp
      ((mem_sorted_cast carrier hi (xs i)).mpr (hxs i))
  | rvZero => exact Or.inl rfl
  | rvOne => exact old _ h1
  | rv =>
    apply old _
    apply S.closed .rv xs
    intro i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst i
    exact hxs 0
  | rvMul =>
    let x : RV0 O := xs 0
    let y : RV0 O := xs 1
    change x * y ∈ V
    have hx : x ∈ V := hxs 0
    have hy : y ∈ V := hxs 1
    rcases hx with hx | ⟨u, hu, hune, e, he⟩
    · exact Or.inl (by rw [hx, zero_mul (M₀ := RV0 O)])
    rcases hy with hy | ⟨v, hv, hvne, d, hd⟩
    · exact Or.inl (by rw [hy, mul_zero (M₀ := RV0 O)])
    refine Or.inr ⟨u * v, mulOld u v hu hv, mul_ne_zero hune hvne, e + d, ?_⟩
    rw [he, hd, hL.2.2.1, mul_mul_mul_comm (G := RV0 O)]
  | rvInv =>
    let x : RV0 O := xs 0
    change x⁻¹ ∈ V
    have hx : x ∈ V := hxs 0
    rcases hx with hx | ⟨u, hu, hune, e, he⟩
    · exact Or.inl (by rw [hx, inv_zero (G₀ := RV0 O)])
    refine Or.inr ⟨u⁻¹, invOld u hu, inv_ne_zero (G₀ := RV0 O) hune, -e, ?_⟩
    have heq := (hL.2.2.1 (-e) e).symm
    rw [neg_add_cancel, hL.1] at heq
    have hp := (mul_eq_one_iff_eq_inv₀ (G₀ := RV0 O) (IsPositiveRV.ne_zero O (hip e))).mp heq
    rw [he, hp, mul_inv (α := RV0 O)]
  | power d =>
    change P d (xs 0) ∈ V
    by_cases hx : IsPositiveRV O (xs 0)
    · have h : xs 0 ∈ V := hxs 0
      obtain ⟨u, hu, hune, e, he⟩ := h.resolve_left (IsPositiveRV.ne_zero O hx)
      have huPos : IsPositiveRV O u := by
        obtain ⟨p, rfl⟩ := rv_surjective O u
        obtain ⟨q, hq⟩ := hip e
        rw [he, ← hq, ← map_mul (rv O)] at hx
        exact (isPositiveRV_rv_iff O hO).mpr
          (pos_of_mul_pos_left ((isPositiveRV_rv_iff O hO).mp hx) q.property.le)
      refine Or.inr ⟨P d u, powOld d u hu, IsPositiveRV.ne_zero O (leadingTermPower_pos O (hP d) huPos),
        d * e, ?_⟩
      rw [he, leadingTermPower_mul O (hP d) huPos (hip e), hL.2.2.2]
    · exact Or.inl (hclamp d _ hx)
  | residue f =>
    let fn : (Fin _ → Residue O) → Residue O := FirstOrder.Language.Structure.funMap f
    change extendResidueOperation O fn (homogeneousArgs xs) ∈ V
    by_cases h : ∀ i, homogeneousArgs xs i ∈ Set.range (residueRV O)
    · apply old
      apply S.closed (.residue f) xs
      intro i
      have hi : (List.replicate _ TCsort.rv).get i = .rv := by simp [List.get_eq_getElem]
      have hs : (hi ▸ xs i : CanonicalSort O .rv) ∈ V :=
        (mem_sorted_cast carrier hi (xs i)).mpr (hxs i)
      have hCast : homogeneousArgs xs (Fin.cast List.length_replicate i) = (hi ▸ xs i : CanonicalSort O .rv) := by
        unfold homogeneousArgs
        rfl
      have hr := h (Fin.cast List.length_replicate i)
      rw [hCast] at hr
      exact (mem_sorted_cast S.carrier hi (xs i)).mp (residueOld hs hr)
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [extendResidueOperation_off_residue O fn ⟨i, hi⟩]
      exact Or.inl rfl

end Adjoin

end Monomials

section TrivialValueBase

variable {K : Type (max u v w z)} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
  [Field E] (g : E → PositiveField K →* PositiveField K)
  (P : E → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (hclamp : ∀ e t, ¬IsPositiveRV O t → P e t = 0)

set_option linter.style.haveILetI false in
include hclamp in
/-- The closure assertion in Remark 2.27 follows from the fixed-RV
enlargements that give models at nontrivial value bases. At a trivial
value base, adjoining each of two independent values gives nontrivial
bases whose RV sorts intersect in the original base. -/
theorem rvDefinablyClosed_of_fixedRV_model_extensions (T : SortedTheory L E)
    (hqe : ∀ {Var : TCsort → Type (max u v w z)} (φ : SortedFormula L E Var),
      ∃ ψ, ψ.IsQF ∧ ∀ N : T.PointedModel Var, N.realizes φ ↔ N.realizes ψ)
    (hM : ∀ φ ∈ T, φ.realize (canonicalStructure O hO P))
    (hExt : ∀ A : SortedSubstructure (canonicalStructure (L := L) O hO P),
      (∃ t ∈ A.carrier .rv, t ≠ 0 ∧ unsignedValue O t ≠ 1) →
      ∃ B : SortedSubstructure (canonicalStructure (L := L) O hO P),
        B.carrier .rv = A.carrier .rv ∧ (∀ φ ∈ T, φ.realize B.structureOn) ∧
          ∀ s, Nonempty (B.carrier s))
    (a b : PositiveField K)
    (hab :
      letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
      LinearIndependent E (![positiveFieldValue O a, positiveFieldValue O b]))
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P)) :
    RVDefinablyClosed (canonicalStructure (L := L) O hO P) (S.carrier .rv) := by
  let M := canonicalStructure (L := L) O hO P
  have extend (A : SortedSubstructure M) (hA : ∃ t ∈ A.carrier .rv, t ≠ 0 ∧ unsignedValue O t ≠ 1) :
      RVDefinablyClosed M (A.carrier .rv) := by
    obtain ⟨B, hB, hBT, hBN⟩ := hExt A hA
    rw [← hB]
    exact rvDefinablyClosed_of_models_of_QE M T hqe B hM hBT hBN
  by_cases h : ∃ t ∈ S.carrier .rv, t ≠ 0 ∧ unsignedValue O t ≠ 1
  · exact extend S h
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  have hOld (t : RV0 O) (ht : t ∈ S.carrier .rv) (hn : t ≠ 0) : unsignedValue O t = 1 :=
    not_not.mp (fun hv => h ⟨t, ht, hn, hv⟩)
  have hW₀ : 0 ∈ S.carrier .rv := S.closed .rvZero (fun i => i.elim0) (fun i => i.elim0)
  have hW₁ : 1 ∈ S.carrier .rv := S.closed .rvOne (fun i => i.elim0) (fun i => i.elim0)
  have hNew (c : PositiveField K) (hc : positiveFieldValue O c ≠ 0) (u : RV0 O)
      (hu : u ∈ S.carrier .rv) (hun : u ≠ 0) (e : E)
      (hv : unsignedValue O (u * P e (rv O c)) = 1) : e = 0 := by
    rw [map_mul (unsignedValue O), hOld u hu hun, one_mul,
      unsignedValue_namedPower O g P hP hzero hone hadd hmul hunit] at hv
    have hz : e • positiveFieldValue O c = 0 := Additive.toMul.injective (Units.ext hv)
    exact (smul_eq_zero.mp hz).resolve_right hc
  have closed (c : PositiveField K) (hc : positiveFieldValue O c ≠ 0) :
      RVDefinablyClosed M (rvOneGeneratorMonomials O P (S.carrier .rv) (rv O c)) := by
    let hcPos : IsPositiveRV O (rv O c) := ⟨c, rfl⟩
    let B := adjoinNewValueRV O g P hP hzero hone hadd hmul hO hclamp S (rv O c) hcPos (hNew c hc)
    have hcMem : rv O c ∈ B.carrier .rv := by
      have hn : (1 : RV0 O) ≠ 0 := by
        rw [← map_one (rv O)]
        exact (rv_eq_zero_iff O).not.mpr one_ne_zero
      refine Or.inr ⟨1, hW₁, hn, 1, ?_⟩
      rw [(leadingTermPower_scalarLaws O hP hzero hone hadd hmul hcPos).2.1, one_mul (M := RV0 O)]
    have hv : unsignedValue O (rv O c) ≠ 1 := by
      rw [unsignedValue_rv, ← positiveFieldValue_coe]
      exact fun hv => hc (Additive.toMul.injective (Units.ext hv))
    exact extend B ⟨rv O c, hcMem, IsPositiveRV.ne_zero O hcPos, hv⟩
  have hL := linearIndependent_fin2.mp hab
  have ha : positiveFieldValue O a ≠ 0 := by
    intro hh
    exact hL.2 0 (by rw [zero_smul]; exact hh.symm)
  have hb : positiveFieldValue O b ≠ 0 := hL.1
  have heq := rvOneGeneratorMonomials_inter O g P hP hzero hone hadd hmul hunit
    (S.carrier .rv) hW₀ hOld a b hab
  rw [← heq]
  exact (closed a ha).inter M (closed b hb)

end TrivialValueBase

end GeneralizedEuler.Section2
