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

end GeneralizedEuler.Section2
