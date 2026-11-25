module

public import Section2.RVExchange
public import Section2.FieldOperations

/-! The generated RV extension when the new point has an old value. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z

variable {L : Language.{u, v}} {E : Type w} {K : Type z}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O)

@[expose]
def rvResidueProducts (W : Set (RV0 O)) (D : Set (Residue O)) : Set (RV0 O) :=
  {t | ∃ u ∈ W, ∃ r ∈ D, t = u * residueRV O r}

private theorem mem_homogeneous_cast {X : TCsort → Type*}
    (A : ∀ s, Set (X s)) {s t : TCsort} (he : s = t) (x : X s) :
    (he ▸ x : X t) ∈ A t ↔ x ∈ A s := by
  cases he
  rfl

set_option linter.style.haveILetI false in
/-- Adjoining a residue field to a base with its old value group gives
a sorted substructure whose RV elements are products of old terms and
residues in the adjoined field. -/
def adjoinResidueRV (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (D : L.Substructure (Residue O)) (terms : OrderedFieldTerms L)
    (hD : letI := residueLinearOrder O hO; InterpretsOrderedFieldTerms (A := Residue O) terms)
    (minusIn : rv O (-1) ∈ S.carrier .rv)
    (oldResidues : ∀ r, residueRV O r ∈ S.carrier .rv → r ∈ D)
    (g : E → PositiveField K →* PositiveField K)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hOff : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hResiduePowers : ∀ e r, r ∈ D → IsPositiveRV O (residueRV O r) →
      ∃ q ∈ D, P e (residueRV O r) = residueRV O q) :
    SortedSubstructure (canonicalStructure (L := L) O hO P) := by
  classical
  letI := residueLinearOrder O hO
  let F := subfieldOfFieldSubstructure terms hD D
  let W := S.carrier .rv
  let V := rvResidueProducts O W D
  let carrier : ∀ s, Set (CanonicalSort O s)
    | .vf => S.carrier .vf
    | .rv => V
  have hF (r : Residue O) : r ∈ F ↔ r ∈ D := mem_subfieldOfFieldSubstructure terms hD D r
  have hOne : 1 ∈ W := S.closed .rvOne (fun i => i.elim0) (fun i => i.elim0)
  have hZero : 0 ∈ W := S.closed .rvZero (fun i => i.elim0) (fun i => i.elim0)
  have old (u : RV0 O) (hu : u ∈ W) : u ∈ V := by
    exact ⟨u, hu, 1, (hF 1).mp F.one_mem, by rw [residueRV_one, mul_one (M := RV0 O)]⟩
  have mulOld (u v : RV0 O) (hu : u ∈ W) (hv : v ∈ W) : u * v ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv, .rv] :=
      Fin.cases u (Fin.cases v (fun i => i.elim0))
    exact S.closed .rvMul args (fun i => Fin.cases hu (Fin.cases hv (fun j => j.elim0)) i)
  have invOld (u : RV0 O) (hu : u ∈ W) : u⁻¹ ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases u (fun i => i.elim0)
    exact S.closed .rvInv args (fun i => Fin.cases hu (fun j => j.elim0) i)
  have powerOld (e : E) (u : RV0 O) (hu : u ∈ W) : P e u ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases u (fun i => i.elim0)
    exact S.closed (.power e) args (fun i => Fin.cases hu (fun j => j.elim0) i)
  have hResidue {t : RV0 O} (ht : t ∈ V) (hr : t ∈ Set.range (residueRV O)) :
      rvResidue O t ∈ D := by
    by_cases h0 : t = 0
    · rw [h0, ← residueRV_zero O, rvResidue_residueRV]
      exact (hF 0).mp F.zero_mem
    obtain ⟨u, hu, r, hrD, he⟩ := ht
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, residueRV_zero, mul_zero (M₀ := RV0 O)] at he
      exact h0 he
    rw [range_residueRV] at hr
    have hv := hr.resolve_left h0
    rw [he, map_mul (unsignedValue O), unsignedValue_residueRV_of_ne_zero O hr0, mul_one] at hv
    have huv : u ∈ Set.range (residueRV O) := by
      rw [range_residueRV]
      exact Or.inr hv
    obtain ⟨q, hq⟩ := huv
    have hqD : q ∈ D := oldResidues q (hq.symm ▸ hu)
    rw [he, ← hq, ← residueRV_mul, rvResidue_residueRV]
    exact (hF _).mp (F.mul_mem ((hF q).mpr hqD) ((hF r).mpr hrD))
  have positive_factors {t : RV0 O} (ht : t ∈ V) (hPos : IsPositiveRV O t) :
      ∃ u ∈ W, ∃ r ∈ D, t = u * residueRV O r ∧
        IsPositiveRV O u ∧ IsPositiveRV O (residueRV O r) := by
    obtain ⟨u, hu, r, hr, he⟩ := ht
    obtain ⟨c, hc⟩ := rv_surjective O u
    obtain ⟨d, hd⟩ := rv_surjective O (residueRV O r)
    have hcd : rv O (c * d) = t := (map_mul (rv O) c d).trans
      ((congrArg₂ (fun a b : RV0 O => a * b) hc hd).trans he.symm)
    have hm : 0 < c * d := (isPositiveRV_rv_iff O hO).mp (hcd.symm ▸ hPos)
    rcases mul_pos_iff.mp hm with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨u, hu, r, hr, he, hc ▸ (isPositiveRV_rv_iff O hO).mpr hp,
        hd ▸ (isPositiveRV_rv_iff O hO).mpr hq⟩
    · have hc' : rv O (-c) = rv O (-1) * u := by rw [← neg_one_mul c, map_mul, hc]
      have hd' : rv O (-d) = residueRV O (-r) := by
        rw [← neg_one_mul d, map_mul, hd, residueRV_neg]
      refine ⟨rv O (-c), hc'.symm ▸ mulOld _ _ minusIn hu, -r,
        (hF _).mp (F.neg_mem ((hF r).mpr hr)), ?_,
        (isPositiveRV_rv_iff O hO).mpr (neg_pos.mpr hp),
        hd' ▸ (isPositiveRV_rv_iff O hO).mpr (neg_pos.mpr hq)⟩
      rw [← hd', ← map_mul, neg_mul_neg]
      exact hcd.symm
  refine ⟨carrier, ?_⟩
  intro ss s f xs hxs
  cases f with
  | vf f =>
    apply S.closed (.vf f) xs
    intro j
    have hj : (List.replicate _ TCsort.vf).get j = .vf := by simp [List.get_eq_getElem]
    exact (mem_homogeneous_cast S.carrier hj _).mp ((mem_homogeneous_cast carrier hj _).mpr (hxs j))
  | rvZero => exact old _ hZero
  | rvOne => exact old _ hOne
  | rv =>
    apply old
    apply S.closed .rv xs
    intro j
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst j
    exact hxs 0
  | rvMul =>
    let x : RV0 O := xs 0
    let y : RV0 O := xs 1
    have hx : x ∈ V := hxs 0
    have hy : y ∈ V := hxs 1
    obtain ⟨u, hu, r, hr, he⟩ := hx
    obtain ⟨v, hv, q, hq, hf⟩ := hy
    change x * y ∈ V
    refine ⟨u * v, mulOld u v hu hv, r * q,
      (hF _).mp (F.mul_mem ((hF _).mpr hr) ((hF _).mpr hq)), ?_⟩
    rw [he, hf, residueRV_mul, mul_mul_mul_comm (G := RV0 O)]
  | rvInv =>
    let x : RV0 O := xs 0
    have hx : x ∈ V := hxs 0
    obtain ⟨u, hu, r, hr, he⟩ := hx
    change x⁻¹ ∈ V
    refine ⟨u⁻¹, invOld u hu, r⁻¹, (hF _).mp (F.inv_mem ((hF _).mpr hr)), ?_⟩
    rw [he, residueRV_inv, mul_inv (α := RV0 O)]
  | power e =>
    change P e (xs 0) ∈ V
    by_cases hp : IsPositiveRV O (xs 0)
    · obtain ⟨u, hu, r, hr, he, hPos, hPosR⟩ := positive_factors (hxs 0) hp
      obtain ⟨q, hq, hqP⟩ := hResiduePowers e r hr hPosR
      exact ⟨P e u, powerOld e u hu, q, hq,
        (congrArg (P e) he).trans
          ((leadingTermPower_mul O (hP e) hPos hPosR).trans (congrArg (P e u * ·) hqP))⟩
    · rw [hOff e _ hp]
      exact old _ hZero
  | @residue n f =>
    let fn : (Fin _ → Residue O) → Residue O := Structure.funMap f
    let a := homogeneousArgs xs
    change extendResidueOperation O fn a ∈ V
    by_cases h : ∀ i, a i ∈ Set.range (residueRV O)
    · rw [extendResidueOperation_of_mem_range O fn h]
      refine ⟨1, hOne, fn (rvResidue O ∘ a), D.fun_mem f _ ?_, (one_mul (M := RV0 O) _).symm⟩
      intro j
      let i : Fin (List.replicate n TCsort.rv).length := ⟨j.val, by
        simpa only [List.length_replicate] using j.isLt⟩
      have hi : (List.replicate n TCsort.rv).get i = .rv := by simp [List.get_eq_getElem]
      have hm := (mem_homogeneous_cast carrier hi (xs i)).mpr (hxs i)
      exact hResidue hm (h j)
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [extendResidueOperation_off_residue O fn ⟨i, hi⟩]
      exact old _ hZero

theorem adjoinResidueRV_rv_carrier
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (D : L.Substructure (Residue O)) (terms : OrderedFieldTerms L)
    (hD : letI := residueLinearOrder O hO; InterpretsOrderedFieldTerms (A := Residue O) terms)
    (minusIn : rv O (-1) ∈ S.carrier .rv)
    (oldResidues : ∀ r, residueRV O r ∈ S.carrier .rv → r ∈ D)
    (g : E → PositiveField K →* PositiveField K) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hOff : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hResiduePowers : ∀ e r, r ∈ D → IsPositiveRV O (residueRV O r) →
      ∃ q ∈ D, P e (residueRV O r) = residueRV O q) :
    (adjoinResidueRV O hO P S D terms hD minusIn oldResidues g hP hOff hResiduePowers).carrier .rv =
      rvResidueProducts O (S.carrier .rv) D := by rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Leading terms of the same nonzero value differ by a residue factor. -/
theorem exists_residue_factor_of_same_value {t u : RV0 O}
    (ht : t ≠ 0) (hVal : unsignedValue O t = unsignedValue O u) :
    u ≠ 0 ∧ ∃ r : Residue O, t = u * residueRV O r := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  obtain ⟨y, rfl⟩ := rv_surjective O u
  rw [unsignedValue_rv, unsignedValue_rv] at hVal
  have hx : x ≠ 0 := (rv_eq_zero_iff O).not.mp ht
  have hy : O.valuation y ≠ 0 := hVal ▸ (map_ne_zero O.valuation).mpr hx
  have hU : rv O y ≠ 0 := (rv_eq_zero_iff O).not.mpr ((map_ne_zero O.valuation).mp hy)
  have hv : rv O x / rv O y ∈ Set.range (residueRV O) := by
    rw [range_residueRV, ← map_div₀ (G₀ := K) (G₀' := RV0 O) (rv O)]
    exact Or.inr (by rw [unsignedValue_rv, map_div₀, hVal, div_self hy])
  obtain ⟨r, hr⟩ := hv
  refine ⟨hU, r, ?_⟩
  rw [hr, div_eq_mul_inv (G := RV0 O), ← mul_assoc (G := RV0 O),
    mul_comm (G := RV0 O) (rv O y) (rv O x), mul_assoc (G := RV0 O),
    mul_inv_cancel₀ (G₀ := RV0 O) hU, mul_one (M := RV0 O)]

set_option linter.style.haveILetI false in
/-- Exchange for an RV point of old value uses the actual enlarged
RV substructure. Any point defined from the new generator lies in
its residue products, by definable closure on RV. -/
theorem definable_rv_exchange_at_old_value {T : L.Theory} [T.IsUniversal] [Residue O ⊨ T]
    (hQE : EliminatesQuantifiers T) (terms : OrderedFieldTerms L)
    (hResidueTerms : letI := residueLinearOrder O hO; InterpretsOrderedFieldTerms (A := Residue O) terms)
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (minusIn : rv O (-1) ∈ S.carrier .rv)
    (g : E → PositiveField K →* PositiveField K)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hOff : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hResiduePowers : ∀ (D : L.Substructure (Residue O)) e r, r ∈ D → IsPositiveRV O (residueRV O r) →
      ∃ q ∈ D, P e (residueRV O r) = residueRV O q)
    (hDcl : ∀ C : SortedSubstructure (canonicalStructure (L := L) O hO P),
      RVDefinablyClosed (canonicalStructure (L := L) O hO P) (C.carrier .rv))
    {t x : RV0 O} (ht : t ≠ 0) (hNew : x ∉ S.carrier .rv)
    (hOldValue : ∃ u ∈ S.carrier .rv, unsignedValue O t = unsignedValue O u)
    (hDef : SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => insert t (S.carrier .rv))
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = x})
    (B : Matroid (Residue O))
    (hLoops : B.closure ∅ ⊆ {r | residueRV O r ∈ S.carrier .rv})
    (hGen : ∀ r, (Substructure.closure L (insert r {s | residueRV O s ∈ S.carrier .rv}) : Set (Residue O)) ⊆
      B.closure {r})
    (hClosure :
      let old : Set (Residue O) := {s | residueRV O s ∈ S.carrier .rv}
      ∀ z y, y ∈ B.closure {z} → ∃ φ : L.Formula ((old ⊕ Unit) ⊕ Unit),
        ∀ s : Residue O, φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => z)) (fun _ => s)) ↔ s = y) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => insert x (S.carrier .rv))
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = t} := by
  let W := S.carrier .rv
  let old : Set (Residue O) := {s | residueRV O s ∈ W}
  obtain ⟨c, hc, hv⟩ := hOldValue
  obtain ⟨_, r, hr⟩ := exists_residue_factor_of_same_value O ht hv
  let D := Substructure.closure L (insert r old)
  have hBase (s : Residue O) (hs : residueRV O s ∈ W) : s ∈ D :=
    Substructure.subset_closure (Set.mem_insert_of_mem _ hs)
  let C := adjoinResidueRV O hO P S D terms hResidueTerms minusIn hBase g hP hOff (hResiduePowers D)
  have hCarrier : C.carrier .rv = rvResidueProducts O W D :=
    adjoinResidueRV_rv_carrier O hO P S D terms hResidueTerms minusIn hBase g hP hOff (hResiduePowers D)
  have hOld (u : RV0 O) (hu : u ∈ W) : u ∈ C.carrier .rv := by
    rw [hCarrier]
    letI := residueLinearOrder O hO
    have hOne : (1 : Residue O) ∈ D := (mem_subfieldOfFieldSubstructure terms hResidueTerms D 1).mp
      (subfieldOfFieldSubstructure terms hResidueTerms D).one_mem
    exact ⟨_, hu, 1, hOne, by rw [residueRV_one, mul_one (M := RV0 O)]⟩
  have htC : t ∈ C.carrier .rv := by
    rw [hCarrier]
    exact ⟨c, hc, r, Substructure.subset_closure (Set.mem_insert _ _), hr⟩
  have hxC : x ∈ C.carrier .rv := hDcl C x (hDef.mono (fun s => by
    cases s with
    | vf => exact Set.Subset.rfl
    | rv =>
      intro u hu
      rcases hu with rfl | hu
      · exact htC
      · exact hOld u hu))
  rw [hCarrier] at hxC
  obtain ⟨u, hu, q, hq, hx⟩ := hxC
  have hMul (u : RV0 O) (hu : u ∈ W) (v : RV0 O) (hv : v ∈ W) : u * v ∈ W := by
    let args : SortedArgs (CanonicalSort O) [.rv, .rv] :=
      Fin.cases u (Fin.cases v (fun i => i.elim0))
    exact S.closed .rvMul args (fun i => Fin.cases hu (Fin.cases hv (fun j => j.elim0)) i)
  have hu0 : u ≠ 0 := by
    intro he
    rw [he, zero_mul (M₀ := RV0 O)] at hx
    exact hNew (hx.symm ▸ S.closed .rvZero (fun i => i.elim0) (fun i => i.elim0))
  exact definable_rv_exchange_of_residue O hO P hQE W hMul hu hc hu0 hNew r q hr hx
    old (fun _ => Iff.rfl) B hLoops (hGen r hq) hClosure

end GeneralizedEuler.Section2
