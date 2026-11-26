module

public import Section5.UnaryAffinePreparation
public import Section5.PositionedCellClassification
import all Section3.DiscMaps

/-! After preparing the derivative and branch data, each positioning
leaf is a point or an RV-affine disc chart. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

section DiscRestriction

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {A B C : Set K} {f g : K → K}

theorem restrict_discToDisc_source (dtd : DiscToDiscOn O A B f g) (sub : C ⊆ A) :
    DiscToDiscOn O C (f '' C) f g := by
  have img : f '' C ⊆ B := by
    rintro y ⟨x,hx,e⟩
    exact e ▸ dtd.1.mapsTo (sub hx)
  refine ⟨⟨Set.mapsTo_image _ _,dtd.1.injOn.mono sub,?_⟩,
    ⟨dtd.2.1.1.mono sub,dtd.2.1.2.mono img⟩,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,rfl⟩
  · exact fun a r hr h => dtd.2.2.1 a r hr (h.trans sub)
  · exact fun b r hr h => dtd.2.2.2 b r hr (h.trans img)

end DiscRestriction

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O

theorem affine_positioning_leaves
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (Empty ⊕ Bool))
      (CenterTestAssignments S.carrier (Empty ⊕ Bool)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A B : Set K) (f g d : K → K) (code : K → RV0 O)
    (dtd : DiscToDiscOn O A B f g)
    (dataDef : SortedDefinableOver 𝓜 S.carrier {w : SortedAssignment X (MixedVariables 1 (Empty ⊕ Bool)) |
      w .vf 0 ∈ A ∧ w .rv ∘ Sum.inr = affineData O code d (w .vf 0)})
    (mvt : ∀ a ∈ A, ∀ b ∈ A, code a = code b → a ≠ b →
      ∃ c ∈ Set.uIcc a b, f a - f b = d c * (a - b))
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      SortedDefinableOver 𝓜 S.carrier
        {v : SortedAssignment X (MixedVariables 2 (HistoryIndex cs.length)) |
          P.map (v .vf 0) = (v .vf 1,decodeHistory O cs.length (v .rv))} ∧
      ∀ x ∈ A, let C := P.label ⁻¹' {P.label x}
        (∀ y ∈ C, rv O y = rv O x) ∧
        (C = {x} ∨ ∃ (a b : K) (r s : O.ValueGroup) (u : RV O), r ≠ 0 ∧ s ≠ 0 ∧
          C = openDisc O a r ∧ f '' C = openDisc O b s ∧ RVAffineOn O C f u ∧ DiscToDiscOn O C (f '' C) f g) := by
  obtain ⟨cs,defP,_,leaf⟩ := unary_affine_after_preparation O hO power S minusOne hm F hF sat immediate
    A f d code dtd.1.injOn dataDef mvt
  refine ⟨cs,defP,?_⟩
  intro x hx C
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  refine ⟨?_,?_⟩
  · intro y hy
    exact ((UnaryPreparation.regularize (O := O)).prepare_decides Subtype.val cs hy).1
  by_cases hz : P.lead (P.label x) = 0
  · exact Or.inl (P.label_fiber_eq_singleton x hz)
  · let diff := x - P.offset (P.label x)
    let r := O.valuation diff
    have nd : diff ≠ 0 := fun eq => hz ((P.leading x).symm.trans ((rv_eq_zero_iff O).2 eq))
    have hr : r ≠ 0 := (map_ne_zero O.valuation).2 nd
    have eqC : C = openDisc O x r := P.label_fiber_eq_openDisc x hz
    have nontrivial : C.Nontrivial := by
      let y := x + diff * eps
      have e : y - x = diff * eps := add_sub_cancel_left _ _
      have inside : y ∈ C := by
        rw [eqC]
        change O.valuation (y-x) < r
        rw [e,map_mul]
        exact mul_lt_of_lt_one_right ((pos_iff_ne_zero).2 hr) small
      have ne : x ≠ y := by
        intro same
        exact mul_ne_zero nd he (e.symm.trans (sub_eq_zero.2 same.symm))
      exact ⟨x,show P.label x = P.label x from rfl,y,inside,ne⟩
    obtain ⟨sub,_,chart⟩ := leaf x hx
    obtain ⟨u,_,hf⟩ := chart nontrivial
    obtain ⟨b,s,hs,img⟩ := dtd.2.2.1 x r hr (eqC ▸ sub)
    exact Or.inr ⟨x,b,r,s,u,hr,hs,eqC,eqC.symm ▸ img,hf,restrict_discToDisc_source O dtd sub⟩

end GeneralizedEuler.Section5
