module

public import Section2.LeadingTermMap
public import Section2.LeadingTermPower

/-! The order and agreement calculations for a prescribed RV lift in
Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  (O : ValuationSubring K) (P : ValuationSubring F)

set_option linter.style.haveILetI false in
/-- A named leading term determines the cut of its representative over the
old field. Only the RV elements named in the old substructure are needed. -/
theorem prescribedLift_sameCut_on (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (W : Set (RV0 O)) (e : W ↪ RV0 P)
    (horder : ∀ u v : W, (rvLinearOrder O hO).lt u v ↔ (rvLinearOrder P hP).lt (e u) (e v))
    {A : Set K} (f : A → F) {a : K} {b : F}
    (ha : rv O a ∉ rv O '' A) (ht : rv O a ∈ W)
    (hb : e ⟨rv O a, ht⟩ = rv P b)
    (hW : ∀ x : A, rv O (x : K) ∈ W)
    (hbase : ∀ x : A, e ⟨rv O (x : K), hW x⟩ = rv P (f x)) :
    ∀ x : A, ((x : K) < a ↔ f x < b) ∧ (a < (x : K) ↔ b < f x) := by
  letI := rvLinearOrder O hO
  letI := rvLinearOrder P hP
  intro x
  let t : W := ⟨rv O a, ht⟩
  let u : W := ⟨rv O (x : K), hW x⟩
  have hna : rv O a ≠ rv O (x : K) := fun h => ha ⟨x, x.property, h.symm⟩
  have hnb : rv P b ≠ rv P (f x) := by
    rw [← hb, ← hbase]
    exact fun h => hna (congrArg Subtype.val (e.injective h))
  have cutLeft : rv O (x : K) < rv O a ↔ rv P (f x) < rv P b := by
    rw [← hb, ← hbase]
    exact horder u t
  have cutRight : rv O a < rv O (x : K) ↔ rv P b < rv P (f x) := by
    rw [← hb, ← hbase]
    exact horder t u
  rw [rv_lt_rv_iff O hO, rv_lt_rv_iff P hP, and_iff_left hna.symm, and_iff_left hnb.symm]
    at cutLeft
  rw [rv_lt_rv_iff O hO, rv_lt_rv_iff P hP, and_iff_left hna, and_iff_left hnb]
    at cutRight
  exact ⟨cutLeft, cutRight⟩

set_option linter.style.haveILetI false in
/-- The cut comparison for a map defined on the whole RV sort. -/
theorem prescribedLift_sameCut (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (e : RV0 O ↪ RV0 P)
    (horder : letI := rvLinearOrder O hO; letI := rvLinearOrder P hP; StrictMono e)
    {A : Subfield K} (f : A → F) {a : K} {b : F}
    (ha : rv O a ∉ rv O '' (A : Set K))
    (hb : e (rv O a) = rv P b)
    (hbase : ∀ x : A, e (rv O (x : K)) = rv P (f x)) :
    ∀ x : A, ((x : K) < a ↔ f x < b) ∧ (a < (x : K) ↔ b < f x) := by
  letI := rvLinearOrder O hO
  letI := rvLinearOrder P hP
  let e' : (Set.univ : Set (RV0 O)) ↪ RV0 P :=
    (Function.Embedding.subtype _).trans e
  exact prescribedLift_sameCut_on O P hO hP Set.univ e'
    (fun _ _ => horder.lt_iff_lt.symm) f ha (Set.mem_univ _) hb
    (fun _ => Set.mem_univ _) hbase

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- If the leading term of a quotient is represented in the old field, its
residue coefficient can be absorbed into the old factor. -/
theorem rv_absorb_coefficient {A : Subfield K} {x c y : K}
    (hc : c ∈ A) (hcy : c * y ≠ 0)
    (h : rv O (x / (c * y)) ∈ rv O '' (A : Set K)) :
    ∃ d ∈ A, rv O x = rv O d * rv O y := by
  obtain ⟨b, hb, hrep⟩ := h
  refine ⟨b * c, A.mul_mem hb hc, ?_⟩
  calc
    rv O x = rv O ((x / (c * y)) * (c * y)) :=
      congrArg (rv O) (div_mul_cancel₀ x hcy).symm
    _ = rv O (x / (c * y)) * (rv O c * rv O y) := by
      rw [map_mul (rv O) (x / (c * y)) (c * y), map_mul (rv O) c y]
    _ = (rv O b * rv O c) * rv O y := by
      rw [← hrep]
      exact (mul_assoc (rv O b) (rv O c) (rv O y)).symm
    _ = _ := by rw [map_mul (rv O) b c]

end GeneralizedEuler.Section2
