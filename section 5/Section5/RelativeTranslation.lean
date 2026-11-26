module

public import Section5.UnaryPreparation

/-! A centripetal transformation in one coordinate of a pullback.
The other VF coordinates and original tags are kept in the first component. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) {X U : Type*}

/-- The labels of the other coordinates are read by `baseLabel`. The
locus depends only on the full old RV label, while the focus may depend
on all the other field coordinates. -/
structure RelativeTranslation (baseLabel : X → U) where
  locus : Set (U × RV0 O)
  focus : X → RV0 O → K

namespace RelativeTranslation

variable {O} {baseLabel : X → U} (T : RelativeTranslation O baseLabel)

/-- The translation is the identity on each fiber outside its locus. -/
@[expose] def offset (x : X) (t : RV0 O) : K := by
  classical
  exact if (baseLabel x, t) ∈ T.locus then T.focus x t else 0

/-- Retain the old leading term as an auxiliary coordinate. The new
leading term is given by applying `rv` to the translated field coordinate. -/
@[expose] def map (a : X × K) : X × (K × RV0 O) :=
  (a.1, a.2 - T.offset a.1 (rv O a.2), rv O a.2)

theorem map_injective : Function.Injective T.map := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ eq
  obtain ⟨hx, hpair⟩ := Prod.mk.inj eq
  obtain ⟨hy, ht⟩ := Prod.mk.inj hpair
  change x = x' at hx
  subst x'
  change rv O y = rv O y' at ht
  change y - T.offset x (rv O y) = y' - T.offset x (rv O y') at hy
  rw [ht] at hy
  exact Prod.ext rfl (sub_left_inj.mp hy)

private theorem focus_translation_iff {c y : K} {t : RV0 O}
    (ht : t ≠ 0) (hc : rv O c = t) :
    rv O (y + c) = t ↔ O.valuation y < unsignedValue O t := by
  have hn : c ≠ 0 := (rv_eq_zero_iff O).not.mp (hc ▸ ht)
  rw [← hc, rv_eq_rv_iff_valuation O hn, add_sub_cancel_right, unsignedValue_rv]

/-- The image condition is expressed entirely in the old and new
leading terms. On the locus the new value is smaller in multiplicative
order, and away from it the leading term is unchanged. -/
theorem image_pullback (A : Set (U × RV0 O))
    (hfocus : ∀ x t, (baseLabel x, t) ∈ A → (baseLabel x, t) ∈ T.locus →
      t ≠ 0 ∧ rv O (T.focus x t) = t) :
    T.map '' {a : X × K | (baseLabel a.1, rv O a.2) ∈ A} =
      {b : X × (K × RV0 O) | (baseLabel b.1, b.2.2) ∈ A ∧
        (((baseLabel b.1, b.2.2) ∈ T.locus ∧
            unsignedValue O (rv O b.2.1) < unsignedValue O b.2.2) ∨
          ((baseLabel b.1, b.2.2) ∉ T.locus ∧ rv O b.2.1 = b.2.2))} := by
  classical
  ext b
  rcases b with ⟨x, y, t⟩
  change (∃ a : X × K, (baseLabel a.1, rv O a.2) ∈ A ∧ T.map a = (x, y, t)) ↔
    (baseLabel x, t) ∈ A ∧
      (((baseLabel x, t) ∈ T.locus ∧ unsignedValue O (rv O y) < unsignedValue O t) ∨
        ((baseLabel x, t) ∉ T.locus ∧ rv O y = t))
  constructor
  · rintro ⟨⟨x', z⟩, hz, hzxy⟩
    obtain ⟨hx, hpair⟩ := Prod.mk.inj hzxy
    obtain ⟨hy, ht⟩ := Prod.mk.inj hpair
    change x' = x at hx
    subst x'
    change rv O z = t at ht
    change (baseLabel x, rv O z) ∈ A at hz
    change z - T.offset x (rv O z) = y at hy
    rw [ht] at hz hy
    refine ⟨hz, ?_⟩
    by_cases hl : (baseLabel x, t) ∈ T.locus
    · obtain ⟨hn, hc⟩ := hfocus x t hz hl
      refine Or.inl ⟨hl, ?_⟩
      rw [unsignedValue_rv]
      have hz' : z = y + T.focus x t :=
        eq_add_of_sub_eq (by simpa [offset, hl] using hy)
      exact (focus_translation_iff hn hc).1 (hz' ▸ ht)
    · have hzy : z = y := by simpa [offset, hl] using hy
      exact Or.inr ⟨hl, hzy ▸ ht⟩
  · rintro ⟨htA, hcond⟩
    let z := y + T.offset x t
    have hz : rv O z = t := by
      rcases hcond with ⟨hl, hv⟩ | ⟨hl, hr⟩
      · obtain ⟨hn, hc⟩ := hfocus x t htA hl
        rw [unsignedValue_rv] at hv
        simpa [z, offset, hl] using (focus_translation_iff hn hc).2 hv
      · simpa [z, offset, hl] using hr
    refine ⟨(x, z), ?_, ?_⟩
    · change (baseLabel x, rv O z) ∈ A
      rwa [hz]
    · change (x, z - T.offset x (rv O z), rv O z) = (x, y, t)
      rw [hz]
      simp only [z, add_sub_cancel_right]

end RelativeTranslation

end GeneralizedEuler.Section5
