module

public import Section2.LeadingTermMap
public import Section2.SortedStructure

/-! Compatibility of residue maps and leading-term maps. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K F : Type*} [Field K] [Field F] (O : ValuationSubring K) (P : ValuationSubring F)
  (f : K →+* F) (hf : RespectsValuationRing O P f)

include hf in
theorem map_mem_nonunits_iff (x : K) : f x ∈ P.nonunits ↔ x ∈ O.nonunits := by
  rw [P.mem_nonunits_iff_or, O.mem_nonunits_iff_or, ← map_inv₀ f, hf, map_eq_zero]

/-- The induced map of valuation rings. -/
@[expose]
def mapValuationRing : O →+* P :=
  (f.comp O.subtype).codRestrict P.toSubring (fun x => (hf x).mpr x.property)

@[simp] theorem coe_mapValuationRing (x : O) :
    (mapValuationRing O P f hf x : F) = f (x : K) := rfl

/-- The induced map of residue fields. -/
@[expose]
def mapResidue : Residue O →+* Residue P :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O)
    ((IsLocalRing.residue P).comp (mapValuationRing O P f hf)) (by
      intro x hx
      apply (IsLocalRing.residue_eq_zero_iff _).mpr
      apply P.coe_mem_nonunits_iff.mp
      exact (map_mem_nonunits_iff O P f hf (x : K)).mpr (O.coe_mem_nonunits_iff.mpr hx))

@[simp] theorem mapResidue_residue (x : O) :
    mapResidue O P f hf (IsLocalRing.residue O x) =
      IsLocalRing.residue P (mapValuationRing O P f hf x) := rfl

theorem mapRV_residueRV (r : Residue O) :
    mapRV O P f hf (residueRV O r) = residueRV P (mapResidue O P f hf r) := by
  by_cases hr : r = 0
  · rw [hr, map_zero, residueRV_zero, residueRV_zero, mapRV_zero]
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective r
  have hres : IsLocalRing.residue P (mapValuationRing O P f hf x) ≠ 0 := by
    rw [← mapResidue_residue, hx, map_ne_zero]
    exact hr
  rw [← hx, residueRV_residue_of_ne_zero O x (hx.trans_ne hr),
    mapRV_rv, mapResidue_residue, residueRV_residue_of_ne_zero P _ hres, coe_mapValuationRing]

theorem mapRV_in_residue_iff (t : RV0 O) :
    mapRV O P f hf t ∈ Set.range (residueRV P) ↔ t ∈ Set.range (residueRV O) := by
  rw [range_residueRV, range_residueRV]
  change mapRV O P f hf t = 0 ∨ unsignedValue P (mapRV O P f hf t) = 1 ↔
    t = 0 ∨ unsignedValue O t = 1
  rw [mapRV_value_one_iff]
  exact or_congr_left (by
    rw [← mapRV_zero O P f hf]
    exact (mapRV O P f hf).injective.eq_iff)

theorem rvResidue_mapRV (t : RV0 O) :
    rvResidue P (mapRV O P f hf t) = mapResidue O P f hf (rvResidue O t) := by
  by_cases ht : t ∈ Set.range (residueRV O)
  · obtain ⟨r, rfl⟩ := ht
    rw [mapRV_residueRV, rvResidue_residueRV, rvResidue_residueRV]
  · rw [rvResidue_eq_zero_of_not_mem_range O ht, map_zero]
    exact rvResidue_eq_zero_of_not_mem_range P ((mapRV_in_residue_iff O P f hf t).not.mpr ht)

/-- A compatible residue operation commutes with the induced RV map,
including arguments outside the residue field. -/
theorem mapRV_extendResidueOperation {n : ℕ}
    (g : (Fin n → Residue O) → Residue O) (g' : (Fin n → Residue P) → Residue P)
    (hg : ∀ x, mapResidue O P f hf (g x) = g' (mapResidue O P f hf ∘ x))
    (a : Fin n → RV0 O) :
    mapRV O P f hf (extendResidueOperation O g a) =
      extendResidueOperation P g' (mapRV O P f hf ∘ a) := by
  classical
  by_cases h : ∀ i, a i ∈ Set.range (residueRV O)
  · have h' : ∀ i, (mapRV O P f hf ∘ a) i ∈ Set.range (residueRV P) :=
      fun i => (mapRV_in_residue_iff O P f hf _).mpr (h i)
    rw [extendResidueOperation_of_mem_range O g h, extendResidueOperation_of_mem_range P g' h',
      mapRV_residueRV, hg]
    congr 2
    funext i
    exact (rvResidue_mapRV O P f hf (a i)).symm
  · rw [not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [extendResidueOperation_off_residue O g ⟨i, hi⟩,
      extendResidueOperation_off_residue P g' ⟨i, (mapRV_in_residue_iff O P f hf _).not.mpr hi⟩,
      mapRV_zero]

end GeneralizedEuler.Section2
