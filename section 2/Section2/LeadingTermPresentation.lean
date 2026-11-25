module

public import Section2.LeadingTermOrder
public import Section2.Residue

/-! Uniqueness of the leading-term quotient in Proposition 2.13. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K R : Type*} [Field K] [CommGroupWithZero R] (O : ValuationSubring K)

/-- A presentation of the leading-term quotient with the prescribed
maximal-ideal test. -/
structure LeadingTermPresentation where
  projection : K →*₀ R
  surjective : Function.Surjective projection
  eq_iff {x y : K} (hy : y ≠ 0) :
    projection x = projection y ↔ (x - y) / y ∈ O.nonunits

namespace LeadingTermPresentation

/-- The residue compatibility and unit test in Ax. 4–6 force the kernel
of the augmented leading-term map to be the corresponding principal units. -/
def ofResidueEmbedding (projection : K →*₀ R) (hsurj : Function.Surjective projection)
    (ι : Residue O ↪ R) (hOne : ι 1 = 1)
    (hunit : ∀ x : K, O.valuation x = 1 ↔ ∃ r : Residue O, r ≠ 0 ∧ ι r = projection x)
    (hred : ∀ x : O, IsLocalRing.residue O x ≠ 0 →
      ι (IsLocalRing.residue O x) = projection x.val) : LeadingTermPresentation (R := R) O where
  projection := projection
  surjective := hsurj
  eq_iff := by
    intro x y hy
    have unitEq (z : K) : projection z = 1 ↔ rv O z = 1 := by
      have matchUnit (hz : O.valuation z = 1) : projection z = 1 ↔ rv O z = 1 := by
        let u : O := ⟨z, (O.valuation_le_one_iff z).mp hz.le⟩
        let r := IsLocalRing.residue O u
        have hr : r ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr
          ((O.valuation_eq_one_iff u).mpr hz)
        have hu : ι r = projection z := hred u hr
        have hurv : residueRV O r = rv O z := residueRV_residue_of_ne_zero O u hr
        calc
          projection z = 1 ↔ ι r = ι 1 := by rw [hu, hOne]
          _ ↔ r = 1 := ι.injective.eq_iff
          _ ↔ residueRV O r = residueRV O 1 := (residueRV_injective O).eq_iff.symm
          _ ↔ rv O z = 1 := by rw [hurv, residueRV_one]
      constructor
      · intro h
        have hz := (hunit z).mpr ⟨1, one_ne_zero, hOne.trans h.symm⟩
        exact (matchUnit hz).mp h
      · intro h
        have hz := congrArg (unsignedValue O) h
        rw [unsignedValue_rv, map_one] at hz
        exact (matchUnit hz).mpr h
    have hyP : projection y ≠ 0 := (map_ne_zero projection).mpr hy
    have hyO : rv O y ≠ 0 := (rv_eq_zero_iff O).not.mpr hy
    calc
      projection x = projection y ↔ projection (x / y) = 1 := by
        rw [map_div₀ projection, div_eq_one_iff_eq hyP]
      _ ↔ rv O (x / y) = 1 := unitEq _
      _ ↔ rv O x = rv O y := by
        rw [map_div₀ (G₀' := RV0 O) (rv O), div_eq_one_iff_eq hyO]
      _ ↔ (x - y) / y ∈ O.nonunits := rv_eq_rv_iff O hy

variable (p : LeadingTermPresentation (R := R) O)

theorem projection_eq_iff (x y : K) :
    p.projection x = p.projection y ↔ rv O x = rv O y := by
  by_cases hy : y = 0
  · simp only [hy, map_zero, map_eq_zero, rv_eq_zero_iff]
  exact (p.eq_iff hy).trans (rv_eq_rv_iff O hy).symm

/-- The unique multiplicative identification of the canonical RV sort with
another presentation of the same quotient. -/
def equiv : RV0 O ≃* R := by
  let lift : RV0 O → R := fun t => p.projection (Classical.choose (rv_surjective O t))
  have hLift (x : K) : lift (rv O x) = p.projection x :=
    (p.projection_eq_iff O _ _).mpr (Classical.choose_spec (rv_surjective O (rv O x)))
  refine { Equiv.ofBijective lift ⟨?_, ?_⟩ with map_mul' := ?_ }
  · intro s t h
    obtain ⟨x, rfl⟩ := rv_surjective O s
    obtain ⟨y, rfl⟩ := rv_surjective O t
    rw [hLift, hLift] at h
    exact (p.projection_eq_iff O x y).mp h
  · intro r
    obtain ⟨x, rfl⟩ := p.surjective r
    exact ⟨rv O x, hLift x⟩
  · intro s t
    obtain ⟨x, rfl⟩ := rv_surjective O s
    obtain ⟨y, rfl⟩ := rv_surjective O t
    change lift (rv O x * rv O y) = lift (rv O x) * lift (rv O y)
    rw [← map_mul (rv O), hLift, hLift, hLift, map_mul]

@[simp] theorem equiv_rv (x : K) : p.equiv O (rv O x) = p.projection x :=
  (p.projection_eq_iff O _ _).mpr (Classical.choose_spec (rv_surjective O (rv O x)))

theorem equiv_unique {f : RV0 O → R} (h : ∀ x, f (rv O x) = p.projection x) :
    f = p.equiv O := by
  funext t
  obtain ⟨x, rfl⟩ := rv_surjective O t
  rw [h, equiv_rv]

variable [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder R]

/-- Uniqueness also preserves the signed order if the second presentation
orders RV by its field fibers. -/
theorem equiv_strictMono (hO : IsOrderConvex O)
    (hr : ∀ x y : K, p.projection x < p.projection y ↔
      x < y ∧ p.projection x ≠ p.projection y) :
    letI := rvLinearOrder O hO
    StrictMono (p.equiv O) := by
  intro s t h
  obtain ⟨x, rfl⟩ := rv_surjective O s
  obtain ⟨y, rfl⟩ := rv_surjective O t
  rw [equiv_rv, equiv_rv, hr, ne_eq, p.projection_eq_iff O]
  exact (rv_lt_rv_iff O hO).mp h

end LeadingTermPresentation

end GeneralizedEuler.Section2
