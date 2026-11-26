module

public import Section5.UnaryFunctions
public import Section5.DefinableProjection
public import Section3.AffineSlopes

/-! Prepare the branch tag and leading term of the derivative in
Lemma 5.15. The mean-value witness stays in the original prepared fiber. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Two RV values record the branch and the derivative respectively. -/
@[expose] def affineData (code : K → RV0 O) (d : K → K) (x : K) : Bool → RV0 O :=
  fun b => if b then rv O (d x) else code x

/-- The derivative is constant only in leading term. An equal branch tag
allows the mean-value equality, and order-convexity keeps its witness on
the same disc where the leading term has been prepared. -/
theorem unary_affine_after_preparation
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜
      (CenterTestVariables S.carrier (Empty ⊕ Bool))
      (CenterTestAssignments S.carrier (Empty ⊕ Bool)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set K) (f d : K → K) (code : K → RV0 O) (inj : Set.InjOn f A)
    (dataDef : SortedDefinableOver 𝓜 S.carrier
      {w : SortedAssignment (CanonicalSort O) (MixedVariables 1 (Empty ⊕ Bool)) |
        w .vf 0 ∈ A ∧ w .rv ∘ Sum.inr = affineData O code d (w .vf 0)})
    (mvt : ∀ a ∈ A, ∀ b ∈ A, code a = code b → a ≠ b →
      ∃ c ∈ Set.uIcc a b, f a - f b = d c * (a - b)) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      SortedDefinableOver 𝓜 S.carrier
        {v : SortedAssignment (CanonicalSort O) (MixedVariables 2 (HistoryIndex cs.length)) |
          P.map (v .vf 0) = (v .vf 1, decodeHistory O cs.length (v .rv))} ∧
      (P.map '' A = {p | rv O p.1 = P.lead p.2 ∧ ∃ x ∈ A, P.label x = p.2}) ∧
      ∀ x ∈ A, let C := P.label ⁻¹' {P.label x}
        C ⊆ A ∧ (∀ y ∈ C, affineData O code d y = affineData O code d x) ∧
        (C.Nontrivial → ∃ t : RV O, (t : RV0 O) = rv O (d x) ∧ RVAffineOn O C f t) := by
  let G : Set ((K × (Empty → RV0 O)) × (Bool → RV0 O)) :=
    {p | p.1.1 ∈ A ∧ p.2 = affineData O code d p.1.1}
  obtain ⟨cs,same,mapDef⟩ := unary_graph_preparation O hO power S minusOne hm F hF sat immediate G dataDef
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  have const {x y : K} (hx : x ∈ A) (he : P.label x = P.label y) :
      y ∈ A ∧ affineData O code d y = affineData O code d x := by
    have h := same x y Empty.elim he
    have hh : affineData O code d x ∈ {t | ((x,Empty.elim),t) ∈ G} := ⟨hx,rfl⟩
    have hh' := h ▸ hh
    exact ⟨hh'.1,hh'.2.symm⟩
  refine ⟨cs,mapDef,?_,?_⟩
  · ext p
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨P.leading x,x,hx,rfl⟩
    · rintro ⟨hl,x,hx,he⟩
      change P.label x = p.2 at he
      change rv O p.1 = P.lead p.2 at hl
      let y := p.1 + P.offset p.2
      have hy : P.label y = P.label x :=
        P.constant_label (by simpa only [y,he,add_sub_cancel_right] using hl)
      have hm : y ∈ A := (const hx hy.symm).1
      have hy' : P.label y = p.2 := hy.trans he
      refine ⟨y,hm,Prod.ext ?_ hy'⟩
      change y - P.offset (P.label y) = p.1
      rw [hy']
      exact add_sub_cancel_right _ _
  · intro x hx
    let C := P.label ⁻¹' {P.label x}
    have inside : C ⊆ A := fun _ hy => (const hx (show P.label _ = P.label x from hy).symm).1
    have tags (y : K) (hy : y ∈ C) : affineData O code d y = affineData O code d x :=
      (const hx (show P.label y = P.label x from hy).symm).2
    refine ⟨inside,tags,?_⟩
    intro hC
    change C.Nontrivial at hC
    have nonzero : P.lead (P.label x) ≠ 0 := by
      intro h
      have he : C = {x} := P.label_fiber_eq_singleton x h
      obtain ⟨a,ha,b,hb,hn⟩ := hC
      rw [he] at ha hb
      exact hn ((Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm)
    have hOrd : C.OrdConnected := by
      change (P.label ⁻¹' {P.label x}).OrdConnected
      rw [P.label_fiber_eq_openDisc x nonzero]
      exact valuativeDisc_ordConnected O hO x _ (fun _ _ h₁ h₂ => h₁.trans_lt h₂)
    have hDerivative (a : K) (ha : a ∈ C) : rv O (d a) = rv O (d x) :=
      congrFun (tags a ha) true
    have hMvt (a : K) (ha : a ∈ C) (b : K) (hb : b ∈ C) (hn : a ≠ b) :
        ∃ c ∈ C, f a - f b = d c * (a - b) := by
      have hcode : code a = code b := congrFun ((tags a ha).trans (tags b hb).symm) false
      obtain ⟨c,hc,he⟩ := mvt a (inside ha) b (inside hb) hcode hn
      exact ⟨c,hOrd.uIcc_subset ha hb hc,he⟩
    obtain ⟨a,ha,b,hb,hn⟩ := hC
    obtain ⟨c,hc,he⟩ := hMvt a ha b hb hn
    have dc : d c ≠ 0 := by
      intro h
      rw [h,zero_mul] at he
      exact hn (inj (inside ha) (inside hb) (sub_eq_zero.mp he))
    have dt : rv O (d x) ≠ 0 := (hDerivative c hc) ▸ (rv_eq_zero_iff O).not.mpr dc
    obtain ⟨t,ht⟩ := WithZero.ne_zero_iff_exists.mp dt
    exact ⟨t,ht,rvAffine_of_mean_value O (fun y hy => (hDerivative y hy).trans ht.symm) hMvt⟩

end GeneralizedEuler.Section5
