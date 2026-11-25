module

public import Section2.ValuedFieldFormulas
public import Section2.ConvexRingComparison
public import Section2.LeadingTermMap
public import Mathlib.ModelTheory.Substructures

/-! Field terms on a generated substructure and transport of its convex ring. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v

variable {L : Language.{u, v}} {K F : Type*} [Field K] [Field F]
  [LinearOrder K] [LinearOrder F] [L.Structure K] [L.Structure F]
  (terms : OrderedFieldTerms L)

private theorem fieldOperations_finCases_one {A : Type*} (a b : A) :
    (Fin.cases a (fun _ => b) : Fin 2 → A) 1 = b := by rfl

/-- Field-language embeddings preserve the named ring operations. -/
def ringHomOfFieldEmbedding (hK : InterpretsOrderedFieldTerms (A := K) terms)
    (hF : InterpretsOrderedFieldTerms (A := F) terms) (e : K ↪[L] F) : K →+* F := by
  have mapsZero : e 0 = 0 := by
    have h := (HomClass.realize_term e (t := terms.zero) (v := (Empty.elim : Empty → K))).symm
    rwa [hK.zero, Subsingleton.elim (e ∘ Empty.elim) (Empty.elim : Empty → F), hF.zero] at h
  have mapsSub (x y : K) : e (x - y) = e x - e y := by
    have h := (HomClass.realize_term e (t := terms.sub) (v := Fin.cases x (fun _ => y))).symm
    simpa only [hK.sub, hF.sub, Function.comp_apply, Fin.cases_zero, fieldOperations_finCases_one] using h
  refine { toFun := e, map_zero' := mapsZero, map_one' := ?_, map_mul' := ?_, map_add' := ?_ }
  · have h := (HomClass.realize_term e (t := terms.one) (v := (Empty.elim : Empty → K))).symm
    rwa [hK.one, Subsingleton.elim (e ∘ Empty.elim) (Empty.elim : Empty → F), hF.one] at h
  · intro x y
    have h := (HomClass.realize_term e (t := terms.mul) (v := Fin.cases x (fun _ => y))).symm
    simpa only [hK.mul, hF.mul, Function.comp_apply, Fin.cases_zero, fieldOperations_finCases_one] using h
  · intro x y
    change e (x + y) = e x + e y
    calc
      e (x + y) = e (x - (0 - y)) := by rw [zero_sub, sub_neg_eq_add]
      _ = e x - e (0 - y) := mapsSub x (0 - y)
      _ = e x + e y := by rw [mapsSub, mapsZero, zero_sub, sub_neg_eq_add]

theorem strictMono_ringHomOfFieldEmbedding (hK : InterpretsOrderedFieldTerms (A := K) terms)
    (hF : InterpretsOrderedFieldTerms (A := F) terms) (e : K ↪[L] F) :
    StrictMono (ringHomOfFieldEmbedding terms hK hF e) := by
  intro x y hxy
  have h := e.map_rel terms.le (Fin.cases x (fun _ => y))
  have hle : e x ≤ e y := by
    simpa only [hF.le, Function.comp_apply, Fin.cases_zero, fieldOperations_finCases_one] using
      (h.mpr ((hK.le _).mpr hxy.le))
  exact lt_of_le_of_ne hle (fun heq => hxy.ne (e.injective heq))

/-- An L-substructure has the same carrier as a subfield once the
ordered-field operations are named by terms. -/
def subfieldOfFieldSubstructure (hK : InterpretsOrderedFieldTerms (A := K) terms)
    (B : L.Substructure K) : Subfield K := by
  have hsub {x y : K} (hx : x ∈ B) (hy : y ∈ B) : x - y ∈ B := by
    have h := terms.sub.realize_mem (S := B) (Fin.cases x (fun _ => y)) (Fin.cases hx (fun _ => hy))
    simpa only [hK.sub, Fin.cases_zero, fieldOperations_finCases_one] using h
  have hzero : (0 : K) ∈ B := by
    have h := terms.zero.realize_mem (S := B) Empty.elim (fun i => i.elim)
    rwa [hK.zero] at h
  have hone : (1 : K) ∈ B := by
    have h := terms.one.realize_mem (S := B) Empty.elim (fun i => i.elim)
    rwa [hK.one] at h
  have hmul {x y : K} (hx : x ∈ B) (hy : y ∈ B) : x * y ∈ B := by
    have h := terms.mul.realize_mem (S := B) (Fin.cases x (fun _ => y)) (Fin.cases hx (fun _ => hy))
    simpa only [hK.mul, Fin.cases_zero, fieldOperations_finCases_one] using h
  have hinv {x : K} (hx : x ∈ B) : x⁻¹ ∈ B := by
    have h := terms.inv.realize_mem (S := B) (fun _ => x) (fun _ => hx)
    rwa [hK.inv] at h
  have hneg {x : K} (hx : x ∈ B) : -x ∈ B := by
    simpa only [zero_sub] using hsub hzero hx
  have hadd {x y : K} (hx : x ∈ B) (hy : y ∈ B) : x + y ∈ B := by
    simpa only [zero_sub, sub_neg_eq_add] using hsub hx (hsub hzero hy)
  exact
    { carrier := B
      zero_mem' := hzero
      one_mem' := hone
      mul_mem' := hmul
      add_mem' := hadd
      inv_mem' := fun x hx => hinv (x := x) hx
      neg_mem' := hneg }

@[simp] theorem mem_subfieldOfFieldSubstructure (hK : InterpretsOrderedFieldTerms (A := K) terms)
    (B : L.Substructure K) (x : K) : x ∈ subfieldOfFieldSubstructure terms hK B ↔ x ∈ B := by
  rfl

section Transport

variable [IsStrictOrderedRing K]
  (O : ValuationSubring K) (P : ValuationSubring F) (f : K →+* F)

omit [IsStrictOrderedRing K] in
/-- Pulling a convex valuation ring back along an ordered field
embedding gives a convex valuation ring on the same source field. -/
theorem convex_comap_valuationRing (hP : IsOrderConvex P) (hf : Monotone f) :
    IsOrderConvex (P.comap f) := by
  constructor
  intro x hx y hy z hz
  exact ValuationSubring.mem_comap.mpr (hP.out (ValuationSubring.mem_comap.mp hx)
    (ValuationSubring.mem_comap.mp hy) ⟨hf hz.1, hf hz.2⟩)

/-- The field embedding given by a matching cut respects the valuation
ring when the cut of the old ring is omitted in the field extension. -/
theorem respectsValuationRing_of_no_cut (hO : IsOrderConvex O) (hP : IsOrderConvex P) (hf : Monotone f)
    {A : Set K} (hA : ∀ x ∈ A, x ∈ O ↔ f x ∈ P)
    (hn : ∀ x, ¬RealizesValuationRingCut O A x) : RespectsValuationRing O P f := by
  have hEq := eq_convexValuationRing_of_no_cut O (P.comap f) hO
    (convex_comap_valuationRing P f hP hf) (fun x hx => (hA x hx).trans ValuationSubring.mem_comap.symm) hn
  intro x
  rw [hEq]
  exact ValuationSubring.mem_comap.symm

/-- When the cut is realized, the classifications of the two convex rings
and agreement on the chosen cut realization give a valued-field embedding. -/
theorem respectsValuationRing_of_cut_membership (hO : IsOrderConvex O) (hP : IsOrderConvex P) (hf : Monotone f)
    {A : Set K} (hA : ∀ x ∈ A, x ∈ O ↔ f x ∈ P) (a : K)
    (hOcut : ∀ x, RealizesValuationRingCut O A x → (x ∈ O ↔ a ∈ O))
    (hPcut : ∀ x, RealizesValuationRingCut O A x → (f x ∈ P ↔ f a ∈ P))
    (ha : a ∈ O ↔ f a ∈ P) : RespectsValuationRing O P f := by
  have hEq := eq_convexValuationRing_of_cut_membership O (P.comap f) hO
    (convex_comap_valuationRing P f hP hf)
    (fun x hx => (hA x hx).trans ValuationSubring.mem_comap.symm) a hOcut
    (fun x hx => ValuationSubring.mem_comap.trans ((hPcut x hx).trans ValuationSubring.mem_comap.symm))
    (ha.trans ValuationSubring.mem_comap.symm)
  intro x
  rw [hEq]
  exact ValuationSubring.mem_comap.symm

end Transport

end GeneralizedEuler.Section2
