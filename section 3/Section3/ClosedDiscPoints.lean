module

public import Section3.DefinablePoints
public import Section3.ImmediateDiscs
public import Mathlib.Data.Fintype.Lattice

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Cardinal Set
universe u v w
variable {L : Language.{u,v}}

set_option linter.style.haveILetI false in
/-- Realize the cut between the radius and all the old distances by a
field representative. Finite satisfiability uses only density of values. -/
theorem exists_radius_below_old_distances {K : Type*} [Field K] [L.Structure K]
    (O : ValuationSubring K) (F : FieldTerms (convexLanguage L)) {D : Set K}
    (hD : D.Nonempty) {b : K} {r : O.ValueGroup} [DenselyOrdered O.ValueGroup]
    (hfar : ∀ c ∈ D, r < O.valuation (b-c)) :
    letI := convexStructure O L
    InterpretsFieldTerms (K := K) F →
    RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K (D ⊕ Bool) →
    ∃ s, r < s ∧ ∀ c ∈ D, s < O.valuation (b-c) := by
  letI := convexStructure O L
  intro hF hSat
  classical
  obtain ⟨q,hq⟩ := O.valuation_surjective r
  let p : D ⊕ Bool → K := Sum.elim Subtype.val (fun flag => if flag then q else b)
  let fresh : (convexLanguage L).Term ((D ⊕ Bool) ⊕ Unit) := .var (.inr ())
  let name (i : D ⊕ Bool) : (convexLanguage L).Term ((D ⊕ Bool) ⊕ Unit) := .var (.inl i)
  let req (c : D) := (valuationLEFormula F fresh (name (.inr true))).not ⊓
    (discMemberFormula F true (name (.inr false)) (name (.inl c)) fresh).not
  have evaluate (c : D) (x : K) : (req c).Realize (Sum.elim p (fun _ => x)) ↔
      r < O.valuation x ∧ O.valuation x < O.valuation (b-c.val) := by
    simp [req,realize_valuationLEFormula O hF,realize_discMemberFormula O hF,
      p,name,fresh,hq,closedDisc]
  obtain ⟨c,hc⟩ := hD
  let old : D := ⟨c,hc⟩
  have fin (U : Finset ((convexLanguage L).Formula ((D ⊕ Bool) ⊕ Unit)))
      (hU : (U : Set _) ⊆ range req) :
      ∃ x : K, ∀ φ ∈ U, φ.Realize (Sum.elim p (fun _ => x)) := by
    rw [← image_univ] at hU
    obtain ⟨V,_,rfl⟩ := Finset.subset_set_image_iff.mp hU
    let C := insert old V
    obtain ⟨c₀,hc₀,hmin⟩ := Finset.exists_min_image C (fun z : D => O.valuation (b-z.val))
      (Finset.insert_nonempty old V)
    obtain ⟨s,hrs,hs⟩ := exists_between (hfar _ c₀.property)
    obtain ⟨x,hx⟩ := O.valuation_surjective s
    refine ⟨x,?_⟩
    intro φ hφ
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hφ
    exact (evaluate z x).mpr ⟨hx ▸ hrs,hx ▸ hs.trans_le (hmin z (Finset.mem_insert_of_mem hz))⟩
  obtain ⟨x,hx⟩ := hSat p (range req) fin
  have hits (c : D) := (evaluate c x).mp (hx _ (mem_range_self c))
  exact ⟨_,(hits old).1,fun c hc => (hits ⟨c,hc⟩).2⟩


/-- A fixed-base unary predicate has identical truth values at two
points interchanged by an automorphism fixing the named parameters. -/
theorem unary_mem_iff_of_automorphism {E : Type*} {Z : TCsort → Type*}
    {M : SortedStructure L E Z} {P : ∀ s, Set (Z s)} {A : Set (Z .vf)}
    (hA : SortedDefinableOver M P {v : ∀ s, UnaryVFVariables s → Z s | v .vf 0 ∈ A})
    (e : SortedIsomorphism M M) (hP : ∀ s x, x ∈ P s → e.toEmbedding s x = x)
    (x : Z .vf) : x ∈ A ↔ e.toEmbedding .vf x ∈ A := by
  obtain ⟨φ,hφ⟩ := hA
  let atPoint (a : Z .vf) : ∀ s, UnaryVFVariables s → Z s
    | .vf => fun _ => a
    | .rv => Empty.elim
  have he : e.toSortedEmbedding.mapAssignment (fun s => Sum.elim Subtype.val (atPoint x s)) =
      (fun s => Sum.elim (Subtype.val (p := (· ∈ P s))) (atPoint (e.toEmbedding .vf x) s)) := by
    funext s j
    rw [SortedEmbedding.mapAssignment_apply]
    cases j with
    | inl j => exact hP s j.val j.property
    | inr j => cases s with
      | vf => rfl
      | rv => exact j.elim
  have h := e.realize_iff φ (fun s => Sum.elim Subtype.val (atPoint x s))
  rw [he] at h
  exact (hφ (atPoint x)).trans (h.symm.trans (hφ (atPoint _)).symm)

set_option linter.style.haveILetI false in
/-- Lemma 3.20 in the Section 2 saturated two-sorted model. Both the cut
and the automorphism are produced over the original fixed field base. -/
theorem definable_closed_disc_has_base_point
    {E : Type w} [Field E] {T : L.Theory} [T.IsUniversal]
    {Tconvex : (convexLanguage L).Theory} {terms : OrderedFieldTerms L}
    {graph : E → L.Formula (Fin 2)} {K : Type u}
    (d : CanonicalQEModel T Tconvex terms graph K)
    (hInput : d.hasAdjunctionInputs d)
    (hOM : IsOMinimalFieldTheory.{u, v, u} T) (hQE : EliminatesQuantifiers T)
    (hQEv : EliminatesQuantifiers Tconvex)
    (F : FieldTerms (convexLanguage L))
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμK : μ < #K)
    (hL : #(Σ i, L.Functions i) ≤ μ) :
    letI := d.field
    letI := d.order
    letI := d.orderedRing
    letI := d.languageStructure
    letI := convexStructure d.ring L
    InterpretsFieldTerms (K := K) F →
    (∀ Names : Type u, #Names < #K →
      RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K Names) →
    (∀ (D : L.Substructure K) (a : K),
      (∃ y ∈ adjoinFieldRepresentative D a, rv d.ring y ∉ rv d.ring '' (D : Set K)) →
      ∃ c : D, rv d.ring (a - c.val) ∉ rv d.ring '' (D : Set K)) →
    ∀ [DenselyOrdered d.ring.ValueGroup] (S : SortedSubstructure d.structureOn),
      #(S.carrier .vf) ≤ μ → ∀ (b : K) (r : d.ring.ValueGroup),
      SortedDefinableOver d.structureOn S.carrier
        {v : ∀ s, UnaryVFVariables s → CanonicalSort d.ring s | v .vf 0 ∈ closedDisc d.ring b r} →
      (S.carrier .vf ∩ closedDisc d.ring b r).Nonempty := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := convexStructure d.ring L
  intro hF hSat hDetect hdense S hSize b r hdef
  let B := vfReductOfSortedSubstructure d.ring d.convex d.rvPowers.pow S
  letI := fieldOnFieldSubstructure terms d.orderedTerms B
  have hnames : #(S.carrier .vf ⊕ Bool) ≤ μ := by
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_uzero]
    exact Cardinal.add_le_of_le hμ hSize (by apply le_trans _ hμ; simp)
  apply closedDisc_meets_base d.ring _ b r
  · intro hfar
    exact exists_radius_below_old_distances d.ring F ⟨(0 : B).val,(0 : B).property⟩ hfar
      hF (hSat _ (hnames.trans_lt hμK))
  · intro a hsame
    obtain ⟨e,he,hfix,hRV⟩ := immediate_automorphism_of_matching_translates
      d hInput hOM hQE hQEv F hμ hμK hL hF hSat hDetect S hSize a b
      (fun c => hsame c.val c.property)
    have h := unary_mem_iff_of_automorphism hdef e (fun s => by
      cases s with
      | vf => exact hfix
      | rv => exact fun t _ => hRV t) a
    exact h.mpr (he ▸ mem_closedDisc_center d.ring r b)

end GeneralizedEuler.Section3
