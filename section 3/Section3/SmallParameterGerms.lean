module

public import Section3.ImaginaryValueChoice
public import Section3.ValueGerms
public import Section3.ClosedDiscPoints
public import Section3.AtomicParameters
import all Section2.WeakOminimal

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  {I X : Type*}

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Saturation over one representative of each bound produces a positive
value strictly below the entire small family in multiplicative notation. -/
theorem positive_value_below_family [DenselyOrdered O.ValueGroup] {L : Language} [L.Structure K]
    (F : FieldTerms (convexLanguage L)) (b : I → O.ValueGroup) (pos : ∀ i, 0 < b i) :
    letI := convexStructure O L
    InterpretsFieldTerms (K := K) F → RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K (Option I) →
    ∃ β, 0 < β ∧ ∀ i, β < b i := by
  let := convexStructure O L
  intro hF sat
  classical
  by_cases empty : IsEmpty I
  · exact ⟨1,zero_lt_one,fun i => (empty.false i).elim⟩
  obtain ⟨j⟩ := not_isEmpty_iff.mp empty
  choose name hn using fun i => O.valuation_surjective (b i)
  let p : Option I → K := (Option.elim · 0 name)
  let J := convexLanguage L
  let z : J.Term (Option I ⊕ Unit) := .var (.inr ())
  let old (i : Option I) : J.Term (Option I ⊕ Unit) := .var (.inl i)
  let req (i : I) := (valuationLEFormula F z (old none)).not ⊓ (valuationLEFormula F (old (some i)) z).not
  have evaluate (i : I) (x : K) : (req i).Realize (Sum.elim p (fun _ => x)) ↔
      0 < O.valuation x ∧ O.valuation x < b i := by
    simp [req,realize_valuationLEFormula O hF,z,old,p,hn,pos_iff_ne_zero]
  obtain ⟨x,hx⟩ := sat p (range req) (by
    intro T hT
    rw [←image_univ] at hT
    obtain ⟨U,_,rfl⟩ := Finset.subset_set_image_iff.mp hT
    obtain ⟨i,_,least⟩ := Finset.exists_min_image (insert j U) b (Finset.insert_nonempty j U)
    obtain ⟨t,pt,ti⟩ := exists_between (pos i)
    obtain ⟨w,hw⟩ := O.valuation_surjective t
    refine ⟨w,fun φ hφ => ?_⟩
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hφ
    exact (evaluate k w).mpr ⟨hw ▸ pt,hw ▸ ti.trans_le (least k (Finset.mem_insert_of_mem hk))⟩)
  have allBounds (i : I) := (evaluate i x).mp (hx _ (mem_range_self i))
  exact ⟨_,(allBounds j).1,fun i => (allBounds i).2⟩

/-- A sign has constant truth value on a punctured interval at zero.
Only weak o-minimality of the truth set and its complement is used. -/
private theorem small_order_germ (Q : K → Prop) (cells : ∀ v : Bool,
    FiniteConvexUnion {t ∈ Ioo (0 : K) 1 | (Q t ↔ v = true)}) :
    ∃ d > (0 : K), ∃ truth : Prop, ∀ t ∈ Ioo 0 d, Q t ↔ truth := by
  classical
  let g (t : K) := decide (Q t)
  obtain ⟨v,d,hd,h⟩ := finite_range_germ zero_lt_one g (Set.toFinite _) (fun w _ => by
    convert cells w using 1
    ext t; cases w <;> simp [g])
  exact ⟨d,hd,v = true,fun t ht => by rw [←h t ht]; simp [g]⟩

/-- The two signed germs of a field formula at zero have one nonzero
valuative radius. This also works for formulas with imaginary parameters. -/
theorem signed_valuative_germ (hO : IsOrderConvex O) (Q : K → Prop) (cells : ∀ (s w : Bool),
    FiniteConvexUnion {t ∈ Ioo (0 : K) 1 | (Q (if s then -t else t) ↔ w = true)}) :
    ∃ b : O.ValueGroup, 0 < b ∧ ∃ pos neg : Prop, ∀ e, O.valuation e < b → e ≠ 0 →
      (Q e ↔ if 0 < e then pos else neg) := by
  classical
  choose d hd truth ht using fun s => small_order_germ (fun t => Q (if s then -t else t)) (cells s)
  let b := min (O.valuation (d false)) (O.valuation (d true))
  have both (s : Bool) : b ≤ O.valuation (d s) := by
    cases s
    · exact min_le_left ..
    · exact min_le_right ..
  have positive s : 0 < O.valuation (d s) := pos_iff_ne_zero.mpr ((map_ne_zero _).mpr (hd s).ne')
  refine ⟨b,lt_min (positive false) (positive true),truth false,truth true,fun e he hn => ?_⟩
  have small (s : Bool) : |e| < d s := by
    by_contra! no
    have bad := valuation_le_of_nonneg_le O hO (hd s).le no
    rw [valuation_abs] at bad
    exact (he.trans_le (both s)).not_ge bad
  by_cases p : 0 < e
  · simpa [p] using ht false e ⟨p,by simpa [abs_of_pos p] using small false⟩
  · have neg := lt_of_le_of_ne (le_of_not_gt p) hn
    simpa [p] using ht true (-e) ⟨neg_pos.mpr neg,by simpa [abs_of_neg neg] using small true⟩

/-- Lemma 3.18 over the disc code. Weak o-minimality yields the two
germs at a single point. Lemma 3.12 transfers the bounded germ test,
and field saturation realizes one bound for the whole formula family. -/
theorem saturated_small_parameter_atomicity [DenselyOrdered O.ValueGroup] {L : Language} [L.Structure K]
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : letI := convexStructure O L; RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K (Option I))
    (hO : IsOrderConvex O) (A : Set X) (ne : A.Nonempty) (Q : I → X → K → Prop)
    (cells : ∀ i x, x ∈ A → ∀ (s w : Bool),
      FiniteConvexUnion {t ∈ Ioo (0 : K) 1 | (Q i x (if s then -t else t) ↔ w = true)})
    (namedValue : O.ValueGroup → Set (Set X)) (atomValue : ∀ b, AtomicOver (namedValue b) A)
    (defGerm : ∀ i b (p n : Prop), {x | ∀ e, O.valuation e < b → e ≠ 0 →
      (Q i x e ↔ if 0 < e then p else n)} ∈ namedValue b)
    (named : K → Set (Set X)) (dA : ∀ e, A ∈ named e)
    (tests : ∀ e B, B ∈ named e → ∃ i, ∀ x ∈ A, x ∈ B ↔ Q i x e) :
    ∃ β : O.ValueGroup, 0 < β ∧ ∀ e, O.valuation e < β → e ≠ 0 → AtomicOver (named e) A := by
  classical
  obtain ⟨a,ha⟩ := ne
  choose b bp pos neg hg using fun i => signed_valuative_germ O hO (Q i a) (cells i a ha)
  obtain ⟨β,βp,below⟩ := positive_value_below_family O F b bp hF sat
  refine ⟨β,βp,fun e he hn => ⟨dA e,⟨a,ha⟩,?_⟩⟩
  intro B hB x hx y hy
  obtain ⟨i,hi⟩ := tests e B hB
  have atPoint z (hz : z ∈ A) : Q i z e ↔ if 0 < e then pos i else neg i :=
    ((atomValue (b i)).2.uniform _ (defGerm i (b i) (pos i) (neg i)) a ha z hz).mp
      (hg i) e (he.trans (below i)) hn
  exact (hi x hx).trans ((atPoint x hx).trans ((atPoint y hy).symm.trans (hi y hy).symm))

end GeneralizedEuler.Section3
