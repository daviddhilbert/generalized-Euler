module

public import Section2.AdjunctionPowers
public import Section2.RelativeValueSubspace
public import Section2.FieldDefinableClosure
public import Section2.PrescribedLift

/-! Consequences of the one-generator Wilkie inequality used in the
reviewed proof of Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w} [Field E]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  {graph : E → L.Formula (Fin 2)} (g : NamedFieldPowers K graph)
  (O : ValuationSubring K) (p : NamedRVPowers O g.pow)
  (A : Subfield K) (hStable : ∀ e (x : PositiveField K), (x : K) ∈ A → (g.pow e x : K) ∈ A)

set_option linter.style.haveILetI false in
/-- The one-generator form of the Wilkie inequality, from van den
Dries (1997), Corollary 5.6. The matroid is the relative residue
pregeometry over the old residue field. -/
@[expose]
def OneGeneratorWilkieInequality (M : Matroid (Residue O)) : Prop :=
  letI := unsignedValueModule O g.pow p.pow p.agrees g.zero g.one g.add g.mul p.units
  let U := oldValueSubspace O g.pow g.zero g.one g.add g.mul A hStable p.pow p.agrees p.units
  ∃ (_ : FiniteDimensional E (Additive (O.ValueGroupˣ) ⧸ U)),
    (Module.finrank E (Additive (O.ValueGroupˣ) ⧸ U) : ℕ∞) + M.eRk M.E ≤ 1

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem residue_rank_ge_one {M : Matroid (Residue O)} (r : Residue O) (hr : M.IsNonloop r) :
    1 ≤ M.eRk M.E := by
  rw [← hr.eRk_eq]
  exact M.eRk_mono (Set.singleton_subset_iff.mpr hr.mem_ground)

set_option linter.style.haveILetI false in
/-- A fresh leading term with old value gives a nonloop residue.
A fresh value has nonzero relative value rank. The Wilkie inequality
rules out both kinds of rank growth at once. -/
theorem wilkie_value_and_residue_alternatives
    (a : PositiveField K) (hFresh : rv O a.val ∉ rv O '' (A : Set K))
    (M : Matroid (Residue O))
    (hNonloop : ∀ r, residueRV O r ∉ rv O '' (A : Set K) → M.IsNonloop r)
    (bound : OneGeneratorWilkieInequality g O p A hStable M) :
    RelativeValueRankLEOne O g.pow g.zero g.one g.add g.mul A hStable p.pow p.agrees p.units ∧
      (O.valuation a.val ∈ O.valuation '' (A : Set K) →
        ∀ x : K, O.valuation x ∈ O.valuation '' (A : Set K)) ∧
      (O.valuation a.val ∉ O.valuation '' (A : Set K) →
        ∀ x : K, O.valuation x = 1 → rv O x ∈ rv O '' (A : Set K)) ∧
      M.eRk M.E ≤ 1 := by
  letI := unsignedValueModule O g.pow p.pow p.agrees g.zero g.one g.add g.mul p.units
  let U := oldValueSubspace O g.pow g.zero g.one g.add g.mul A hStable p.pow p.agrees p.units
  obtain ⟨hFin, hBound⟩ := bound
  let : FiniteDimensional E (_ ⧸ U) := hFin
  let n := Module.finrank E (Additive (O.ValueGroupˣ) ⧸ U)
  change (n : ℕ∞) + M.eRk M.E ≤ 1 at hBound
  have hValueRank : n ≤ 1 := by
    apply ENat.natCast_le_natCast.mp
    rw [ENat.natCast_one]
    exact (le_add_of_nonneg_right (show (0 : ℕ∞) ≤ M.eRk M.E from zero_le)).trans hBound
  have hResidueRank : M.eRk M.E ≤ 1 :=
    (le_add_of_nonneg_left (show (0 : ℕ∞) ≤ (n : ℕ∞) from zero_le)).trans hBound
  have lower_value_rank {z : Additive (O.ValueGroupˣ)} (hz : z ∉ U) : 1 ≤ (n : ℕ∞) := by
    have hq : U.mkQ z ≠ 0 := fun h => hz ((Submodule.Quotient.mk_eq_zero U).mp h)
    let : Nontrivial (Additive (O.ValueGroupˣ) ⧸ U) := ⟨⟨U.mkQ z, 0, hq⟩⟩
    have hn : 1 ≤ n := Nat.succ_le_of_lt (Module.finrank_pos (R := E))
    rw [← ENat.natCast_one]
    exact ENat.natCast_le_natCast.mpr hn
  have incompatible (hn : 1 ≤ (n : ℕ∞)) (hr : 1 ≤ M.eRk M.E) : False := by
    have h := (add_le_add hn hr).trans hBound
    norm_num at h
  refine ⟨⟨hFin, hValueRank⟩, ?_, ?_, hResidueRank⟩
  · intro hOld x
    obtain ⟨_, _, _, r, _, hr⟩ := exists_new_residue_of_old_value O hOld hFresh
    have hAtLeast := residue_rank_ge_one O r (hNonloop r hr)
    by_cases hx : x = 0
    · exact ⟨0, A.zero_mem, congrArg O.valuation hx.symm⟩
    · let b : PositiveField K := ⟨|x|, abs_pos.mpr hx⟩
      have hm : positiveFieldValue O b ∈ U :=
        Classical.byContradiction fun h => incompatible (lower_value_rank h) hAtLeast
      have h := (mem_oldValueSubspace_iff O g.pow g.zero g.one g.add g.mul
        A hStable p.pow p.agrees p.units _).mp hm
      rwa [positiveFieldValue_coe, valuation_abs] at h
  · intro hNew x hx
    have ha : positiveFieldValue O a ∉ U := by
      intro ha
      have h := (mem_oldValueSubspace_iff O g.pow g.zero g.one g.add g.mul
        A hStable p.pow p.agrees p.units _).mp ha
      rw [positiveFieldValue_coe] at h
      exact hNew h
    have hmem : rv O x ∈ Set.range (residueRV O) := by
      rw [range_residueRV]
      exact Or.inr ((unsignedValue_rv O x).trans hx)
    obtain ⟨r, hr⟩ := hmem
    rw [← hr]
    exact Classical.byContradiction fun h =>
      incompatible (lower_value_rank ha) (residue_rank_ge_one O r (hNonloop r h))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The relative residue pregeometry over the residues of the old
field. Its nonloops are the new residues. The singleton closure
records definability over the old residues and that singleton. -/
structure ResiduePregeometryData (L : Language.{u, v}) [L.Structure (Residue O)] where
  matroid : Matroid (Residue O)
  ground : matroid.E = Set.univ
  nonloop : ∀ r, residueRV O r ∉ rv O '' (A : Set K) → matroid.IsNonloop r
  closure : ∀ r x, x ∈ matroid.closure {r} →
    ∃ φ : L.Formula (({s : Residue O | residueRV O s ∈ rv O '' (A : Set K)} ⊕ Unit) ⊕ Unit),
      ∀ y : Residue O, φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => r)) (fun _ => y)) ↔ y = x

/-- The valued-group and residue conclusions for a specific
one-generator adjunction. -/
structure AdjunctionRankData [L.Structure (Residue O)] (a : PositiveField K) where
  residue : ResiduePregeometryData O A L
  valueRank : RelativeValueRankLEOne O g.pow g.zero g.one g.add g.mul A hStable p.pow p.agrees p.units
  oldValues : O.valuation a.val ∈ O.valuation '' (A : Set K) →
    ∀ x : K, O.valuation x ∈ O.valuation '' (A : Set K)
  oldResidues : O.valuation a.val ∉ O.valuation '' (A : Set K) →
    ∀ x : K, O.valuation x = 1 → rv O x ∈ rv O '' (A : Set K)
  residueRank : O.valuation a.val ∈ O.valuation '' (A : Set K) →
    residue.matroid.eRk residue.matroid.E ≤ 1

/-- Specialization of the relative inequality to the representative
adjunction. -/
theorem nonempty_adjunctionRankData_of_wilkie [L.Structure (Residue O)]
    (a : PositiveField K) (ha : rv O a.val ∉ rv O '' (A : Set K))
    (residue : ResiduePregeometryData O A L)
    (bound : OneGeneratorWilkieInequality g O p A hStable residue.matroid) :
    Nonempty (AdjunctionRankData g O p A hStable a) := by
  obtain ⟨hR, hV, hK, hD⟩ :=
    wilkie_value_and_residue_alternatives g O p A hStable a ha residue.matroid residue.nonloop bound
  exact ⟨⟨residue, hR, hV, hK, fun _ => hD⟩⟩

end GeneralizedEuler.Section2
