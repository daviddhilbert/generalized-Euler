module

public import Section5.AffineCellLeaves
public import Section5.PositioningLeafSchemes

/-! One unary preparation separates all named positioning branches
and their slopes. Every surviving label is a point, a constant
disc, or an affine disc with an open-disc image. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem positioning_leaves_from_branch_data
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (Empty ⊕ Bool))
      (CenterTestAssignments S.carrier (Empty ⊕ Bool)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set K) (f d : K → K) (code : K → RV0 O)
    (dataDef : SortedDefinableOver 𝓜 S.carrier {w : SortedAssignment Z (MixedVariables 1 (Empty ⊕ Bool)) |
      w .vf 0 ∈ A ∧ w .rv ∘ Sum.inr = affineData O code d (w .vf 0)})
    (mvt : ∀ a ∈ A, ∀ b ∈ A, code a = code b → a ≠ b →
      ∃ c ∈ Set.uIcc a b, f a - f b = d c * (a - b))
    (branches : ∀ t, let B := {x ∈ A | code x = t}
      (∀ x ∈ B, ∀ y ∈ B, f x = f y) ∨ (Set.InjOn f B ∧ ConcentricOn O B f))
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      SortedDefinableOver 𝓜 S.carrier
        {v : SortedAssignment Z (MixedVariables 2 (HistoryIndex cs.length)) |
          P.map (v .vf 0) = (v .vf 1,decodeHistory O cs.length (v .rv))} ∧
      ∀ x ∈ A, let C := P.label ⁻¹' {P.label x}
        C ⊆ A ∧ (∀ y ∈ C, rv O y = rv O x) ∧
        (C = {x} ∨ ∃ r : O.ValueGroup, r ≠ 0 ∧ C = openDisc O x r ∧
          ((∀ y ∈ C, ∀ w ∈ C, f y = f w) ∨ ∃ (b : K) (s : O.ValueGroup) (u : RV O),
            s ≠ 0 ∧ f '' C = openDisc O b s ∧ RVAffineOn O C f u)) := by
  obtain ⟨cs,hgraph,_,leaves⟩ := unary_affine_on_injective_prepared_fibers O hO power S minusOne hm F hF
    sat immediate A f d code dataDef mvt
  refine ⟨cs,hgraph,?_⟩
  intro x hx
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  let C := P.label ⁻¹' {P.label x}
  obtain ⟨sub,tag,affine⟩ := leaves x hx
  refine ⟨sub,fun y hy => ((UnaryPreparation.regularize (O := O)).prepare_decides Subtype.val cs hy).1,?_⟩
  by_cases hz : P.lead (P.label x) = 0
  · exact Or.inl (P.label_fiber_eq_singleton x hz)
  · let diff := x - P.offset (P.label x)
    let r := O.valuation diff
    have nd : diff ≠ 0 := fun e => hz ((P.leading x).symm.trans ((rv_eq_zero_iff O).2 e))
    have hr : r ≠ 0 := (map_ne_zero O.valuation).2 nd
    have eqC : C = openDisc O x r := P.label_fiber_eq_openDisc x hz
    refine Or.inr ⟨r,hr,eqC,?_⟩
    let B := {y ∈ A | code y = code x}
    have inBranch : C ⊆ B := fun y hy => ⟨sub hy,congrFun (tag y hy) false⟩
    rcases branches (code x) with constant | ⟨inj,concentric⟩
    · exact Or.inl (fun y hy w hw => constant y (inBranch hy) w (inBranch hw))
    · have nz : C.Nontrivial := by
        let y := x + diff * eps
        have e : y - x = diff * eps := add_sub_cancel_left _ _
        have inside : y ∈ C := by
          rw [eqC]
          change O.valuation (y-x) < r
          rw [e,map_mul]
          exact mul_lt_of_lt_one_right ((pos_iff_ne_zero).2 hr) small
        have ne : x ≠ y := fun h => mul_ne_zero nd he (e.symm.trans (sub_eq_zero.2 h.symm))
        exact ⟨x,rfl,y,inside,ne⟩
      obtain ⟨u,_,h⟩ := affine (inj.mono inBranch) nz
      obtain ⟨b,s,hs,img⟩ := concentric x r hr (eqC ▸ inBranch)
      exact Or.inr ⟨b,s,u,hs,(congrArg (f '' ·) eqC).trans img,h⟩

end GeneralizedEuler.Section5
