module

public import Section2.LeadingTermOrder

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
