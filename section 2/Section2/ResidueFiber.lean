module

public import Section2.ResidueOrder

/-! Multiplicative translation of a nonzero value fiber to residues,
as in Remark 2.30. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

private theorem unsignedValue_ne_zero_iff {t : RV0 O} :
    unsignedValue O t ≠ 0 ↔ t ≠ 0 :=
  map_ne_zero (G₀ := RV0 O) (M₀' := O.ValueGroup) (unsignedValue O)

private theorem div_mem_residueRV_of_same_value {s t : RV0 O} (ht : t ≠ 0)
    (hv : unsignedValue O s = unsignedValue O t) :
    s / t ∈ Set.range (residueRV O) := by
  rw [range_residueRV]
  right
  rw [map_div₀ (G₀ := RV0 O) (G₀' := O.ValueGroup) (unsignedValue O) s t, hv,
    div_self ((unsignedValue_ne_zero_iff O).mpr ht)]

theorem div_mem_residueRV_of_equal_unsignedValue {s t : RV0 O}
    (hv : unsignedValue O s = unsignedValue O t) : s / t ∈ Set.range (residueRV O) := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [div_zero (G₀ := RV0 O)]
    exact ⟨0, residueRV_zero O⟩
  · exact div_mem_residueRV_of_same_value O ht hv

/-- Equality of unsigned values is visible in the RV reduct, including
the separate zero class. -/
theorem unsignedValue_eq_iff_div_residue (s t : RV0 O) :
    unsignedValue O s = unsignedValue O t ↔
      (s = 0 ∧ t = 0) ∨ unsignedValue O (s / t) = 1 := by
  by_cases ht : t = 0
  · subst t
    rw [div_zero (G₀ := RV0 O) s]
    simp only [map_zero, map_eq_zero, zero_ne_one, and_true, or_false]
  have hvt : unsignedValue O t ≠ 0 := (unsignedValue_ne_zero_iff O).mpr ht
  rw [map_div₀ (G₀ := RV0 O) (G₀' := O.ValueGroup) (unsignedValue O), div_eq_one_iff_eq hvt]
  simp only [ht, and_false, false_or]

/-- Dividing by a nonzero representative of the value identifies its
entire unsigned value fiber with the nonzero residue field. -/
def valueFiberResidueEquiv (t : RV0 O) (ht : t ≠ 0) :
    {s : RV0 O // unsignedValue O s = unsignedValue O t} ≃ {r : Residue O // r ≠ 0} where
  toFun s := ⟨rvResidue O ((s : RV0 O) / t), by
    have hs : (s : RV0 O) ≠ 0 := (unsignedValue_ne_zero_iff O).mp
      (s.property.trans_ne ((unsignedValue_ne_zero_iff O).mpr ht))
    obtain ⟨r, hr⟩ := div_mem_residueRV_of_same_value O ht s.property
    rw [← hr, rvResidue_residueRV]
    exact fun hr₀ => (div_ne_zero (G₀ := RV0 O) hs ht)
      (hr.symm.trans (hr₀ ▸ residueRV_zero O))⟩
  invFun r := ⟨residueRV O r * t, by
    rw [map_mul, unsignedValue_residueRV_of_ne_zero O r.property, one_mul]⟩
  left_inv s := by
    apply Subtype.ext
    change residueRV O (rvResidue O ((s : RV0 O) / t)) * t = (s : RV0 O)
    obtain ⟨r, hr⟩ := div_mem_residueRV_of_same_value O ht s.property
    rw [← hr, rvResidue_residueRV, hr, div_mul_cancel₀ (G₀ := RV0 O) _ ht]
  right_inv r := by
    apply Subtype.ext
    change rvResidue O (residueRV O (r : Residue O) * t / t) = (r : Residue O)
    rw [div_eq_mul_inv (residueRV O (r : Residue O) * t) t,
      mul_assoc (residueRV O (r : Residue O)) t t⁻¹,
      mul_inv_cancel₀ (G₀ := RV0 O) ht, mul_one (residueRV O (r : Residue O)), rvResidue_residueRV]

/-- The charts for tuples of leading terms are products of the
coordinatewise residue charts. -/
def valueTupleFiberResidueEquiv {n : ℕ} (t : Fin n → RV0 O) (ht : ∀ i, t i ≠ 0) :
    {s : Fin n → RV0 O // ∀ i, unsignedValue O (s i) = unsignedValue O (t i)} ≃
      (Fin n → {r : Residue O // r ≠ 0}) where
  toFun s i := valueFiberResidueEquiv O (t i) (ht i) ⟨s.val i, s.property i⟩
  invFun r := ⟨fun i => ((valueFiberResidueEquiv O (t i) (ht i)).symm (r i)).val,
    fun i => ((valueFiberResidueEquiv O (t i) (ht i)).symm (r i)).property⟩
  left_inv s := Subtype.ext (funext fun i => congrArg Subtype.val
    ((valueFiberResidueEquiv O (t i) (ht i)).symm_apply_apply ⟨s.val i, s.property i⟩))
  right_inv r := funext fun i => (valueFiberResidueEquiv O (t i) (ht i)).apply_symm_apply (r i)

/-- In the unchanged-value case, each leading term is the product of
an old representative of its value and a nonzero residue. -/
theorem rv_factor_residue_of_same_value {x y : K} (hy : y ≠ 0)
    (hval : O.valuation x = O.valuation y) :
    ∃ r : Residue O, r ≠ 0 ∧ rv O x = rv O y * residueRV O r := by
  let s : {t : RV0 O // unsignedValue O t = unsignedValue O (rv O y)} :=
    ⟨rv O x, by rw [unsignedValue_rv, unsignedValue_rv, hval]⟩
  let e := valueFiberResidueEquiv O (rv O y) ((rv_eq_zero_iff O).not.mpr hy)
  let r := e s
  have h := congrArg Subtype.val (e.symm_apply_apply s)
  change residueRV O (r : Residue O) * rv O y = rv O x at h
  exact ⟨r, r.property, h.symm.trans (mul_comm (residueRV O r) (rv O y))⟩

/-- A value label and residue coordinates identify the points of a set
of nonzero leading-term tuples. The chart takes its representative for
each label from the corresponding fiber of the set. -/
def valueTupleResidueEmbedding {n : ℕ} (D : Set (Fin n → RV0 O))
    (hD : ∀ x ∈ D, ∀ i, x i ≠ 0) :
    D ↪ Set.range (fun x : D => unsignedValue O ∘ x.val) ×
      (Fin n → {r : Residue O // r ≠ 0}) := by
  let Labels := Set.range (fun x : D => unsignedValue O ∘ x.val)
  let label (x : D) : Labels := ⟨unsignedValue O ∘ x.val, ⟨x, rfl⟩⟩
  let representative (a : Labels) : D := a.property.choose
  have hrep (a : Labels) : unsignedValue O ∘ (representative a).val = a.val :=
    a.property.choose_spec
  let Norm := Fin n → {r : Residue O // r ≠ 0}
  let chart (a : Labels) : {x : D // label x = a} ↪ Norm := by
    let r := representative a
    let e := valueTupleFiberResidueEquiv O r.val (hD r.val r.property)
    let lift (x : {x : D // label x = a}) :
        {s : Fin n → RV0 O // ∀ i, unsignedValue O (s i) = unsignedValue O (r.val i)} :=
      ⟨x.val.val, fun i => congrFun
        ((congrArg Subtype.val x.property).trans (hrep a).symm) i⟩
    refine ⟨e ∘ lift, ?_⟩
    intro x y h
    have hl : lift x = lift y := e.injective h
    have hv : (lift x).val = (lift y).val :=
      congrArg (fun z : {s : Fin n → RV0 O //
        ∀ i, unsignedValue O (s i) = unsignedValue O (r.val i)} => z.val) hl
    exact Subtype.ext (Subtype.ext (show x.val.val = y.val.val from hv))
  exact (Equiv.sigmaFiberEquiv label).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl Labels) chart).trans
      (Equiv.sigmaEquivProd Labels Norm).toEmbedding)

theorem rv_eq_of_equal_normalized_residues {s t u : RV0 O}
    (hs : unsignedValue O s = unsignedValue O u)
    (ht : unsignedValue O t = unsignedValue O u)
    (h : rvResidue O (s / u) = rvResidue O (t / u)) : s = t := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [map_zero, map_eq_zero] at hs ht
    exact hs.trans ht.symm
  have h' := congrArg (residueRV O) h
  rw [residueRV_rvResidue_of_mem_range O (div_mem_residueRV_of_same_value O hu hs),
    residueRV_rvResidue_of_mem_range O (div_mem_residueRV_of_same_value O hu ht)] at h'
  have hm := congrArg (fun a : RV0 O => a * u) h'
  simpa only [div_mul_cancel₀ (G₀ := RV0 O) _ hu] using hm

/-- A value label and normalized residues recover a tuple with arbitrary
zero coordinates. Each zero coordinate contributes the zero residue. -/
def valueTupleResidueEmbeddingWithZeros {n : ℕ} (D : Set (Fin n → RV0 O)) :
    D ↪ Set.range (fun x : D => unsignedValue O ∘ x.val) × (Fin n → Residue O) := by
  let Labels := Set.range (fun x : D => unsignedValue O ∘ x.val)
  let label (x : D) : Labels := ⟨unsignedValue O ∘ x.val, ⟨x, rfl⟩⟩
  let representative (a : Labels) : D := a.property.choose
  have hrep (a : Labels) : unsignedValue O ∘ (representative a).val = a.val :=
    a.property.choose_spec
  let norm (x : D) (i : Fin n) := rvResidue O (x.val i / (representative (label x)).val i)
  refine ⟨fun x => (label x, norm x), ?_⟩
  intro x y h
  have hlabel : label x = label y := congrArg Prod.fst h
  have hnorm : norm x = norm y := congrArg Prod.snd h
  apply Subtype.ext
  funext i
  let u := (representative (label x)).val i
  have hx : unsignedValue O (x.val i) = unsignedValue O u := (congrFun (hrep (label x)) i).symm
  have hy : unsignedValue O (y.val i) = unsignedValue O u :=
    (congrFun (hrep (label y)) i).symm.trans
      (congrArg (fun a : Labels => unsignedValue O ((representative a).val i)) hlabel.symm)
  have hi := congrFun hnorm i
  change rvResidue O (x.val i / u) = rvResidue O (y.val i / (representative (label y)).val i) at hi
  rw [← hlabel] at hi
  exact rv_eq_of_equal_normalized_residues O hx hy hi

section Order

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- A finite collection of value fibers can be tagged inside the residue
field itself. This gives the normalization used before applying the
o-minimal classification in Theorem 2.31. -/
def finiteValueResidueEmbedding (hO : IsOrderConvex O) {n : ℕ}
    (D : Set (Fin n → RV0 O)) [Finite (Set.range (fun x : D => unsignedValue O ∘ x.val))] :
    D ↪ Residue O × (Fin n → Residue O) := by
  letI := residueLinearOrder O hO
  letI := residue_isOrderedRing O hO
  let Labels := Set.range (fun x : D => unsignedValue O ∘ x.val)
  letI := Fintype.ofFinite Labels
  let tag : Labels ↪ Residue O :=
    ⟨fun a => ((Fintype.equivFin Labels a).val : Residue O), fun _ _ h =>
      (Fintype.equivFin Labels).injective (Fin.ext (Nat.cast_injective h))⟩
  let f := valueTupleResidueEmbeddingWithZeros O D
  refine ⟨fun x => (tag (f x).1, (f x).2), ?_⟩
  intro x y h
  have hnorm : (f x).2 = (f y).2 := congrArg (fun p : Residue O × (Fin n → Residue O) => p.2) h
  exact f.injective (Prod.ext (tag.injective (congrArg Prod.fst h)) hnorm)

set_option linter.style.haveILetI false in
/-- A positive representative makes the residue chart an order
isomorphism on its unsigned value fiber. -/
def residueOrderIsoValueFiber (hO : IsOrderConvex O) (t : RV0 O)
    (ht : letI := rvLinearOrder O hO; 0 < t) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    {r : Residue O // r ≠ 0} ≃o {s : RV0 O // unsignedValue O s = unsignedValue O t} := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  refine { toEquiv := (valueFiberResidueEquiv O t ht.ne').symm
           map_rel_iff' := ?_ }
  intro r s
  change residueRV O (r : Residue O) * t ≤ residueRV O (s : Residue O) * t ↔
    (r : Residue O) ≤ (s : Residue O)
  rw [mul_comm (residueRV O (r : Residue O)) t, mul_comm (residueRV O (s : Residue O)) t]
  exact ((rv_mul_left_strictMono O hO ht).comp (residueRV_strictMono O hO)).le_iff_le

set_option linter.style.haveILetI false in
/-- On the positive branch, unequal unsigned values determine the order.
On a common value fiber the order is that of the normalized residues. -/
theorem positive_rv_le_iff_value_residue_lex (hO : IsOrderConvex O)
    (lift : O.ValueGroup → RV0 O)
    (hlift : letI := rvLinearOrder O hO
      ∀ γ, γ ≠ 0 → unsignedValue O (lift γ) = γ ∧ 0 < lift γ)
    {s t : RV0 O}
    (hs : letI := rvLinearOrder O hO; 0 < s)
    (ht : letI := rvLinearOrder O hO; 0 < t) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    s ≤ t ↔ unsignedValue O s < unsignedValue O t ∨
      (unsignedValue O s = unsignedValue O t ∧
        rvResidue O (s / lift (unsignedValue O s)) ≤
          rvResidue O (t / lift (unsignedValue O t))) := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  have equal_case (h : unsignedValue O s = unsignedValue O t) :
      s ≤ t ↔ rvResidue O (s / lift (unsignedValue O s)) ≤
        rvResidue O (t / lift (unsignedValue O t)) := by
    let q := lift (unsignedValue O t)
    obtain ⟨hq, hqpos⟩ := hlift _ ((unsignedValue_ne_zero_iff O).mpr ht.ne')
    have factor (x : RV0 O) (hx : unsignedValue O x = unsignedValue O t) :
        q * residueRV O (rvResidue O (x / q)) = x := by
      have hmem : x / q ∈ Set.range (residueRV O) :=
        div_mem_residueRV_of_same_value O hqpos.ne' (hx.trans hq.symm)
      rw [residueRV_rvResidue_of_mem_range O hmem, mul_comm q (x / q),
        div_mul_cancel₀ (G₀ := RV0 O) _ hqpos.ne']
    rw [h]
    have hcmp := ((rv_mul_left_strictMono O hO hqpos).comp
      (residueRV_strictMono O hO)).le_iff_le
      (a := rvResidue O (s / q)) (b := rvResidue O (t / q))
    change (q * residueRV O (rvResidue O (s / q)) ≤
      q * residueRV O (rvResidue O (t / q))) ↔ _ at hcmp
    rw [factor s h, factor t rfl] at hcmp
    exact hcmp
  rcases lt_trichotomy (unsignedValue O s) (unsignedValue O t) with hlt | heq | hgt
  · exact iff_of_true (rv_lt_of_value_lt_positive O hO ht hlt).le (Or.inl hlt)
  · rw [equal_case heq]
    exact ⟨fun h => Or.inr ⟨heq, h⟩,
      fun h => h.elim (fun h => (h.ne heq).elim) And.right⟩
  · exact iff_of_false (rv_lt_of_value_lt_positive O hO hs hgt).not_ge
      (fun h => h.elim hgt.not_gt (fun h => hgt.ne h.1.symm))

end Order

end GeneralizedEuler.Section2
