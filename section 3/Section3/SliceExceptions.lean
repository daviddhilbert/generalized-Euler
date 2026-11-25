module

public import Section3.DerivativeFormula
import all Section3.NormalizedSlice

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {X R I : Type*} [LinearOrder R]

/-- The residue labels strictly between labels of two points of a branch. -/
def twoSidedLabels (p : X → R) (B : Set X) : Set R :=
  {r | (∃ x ∈ B, p x < r) ∧ ∃ y ∈ B, r < p y}

theorem finite_endpoint_labels (p : X → R) (B : Set X) :
    (p '' B \ twoSidedLabels p B).Finite := by
  let lo := {r | IsLeast (p '' B) r}
  let hi := {r | IsGreatest (p '' B) r}
  have low : lo.Subsingleton := fun _ hx _ hy => IsLeast.unique hx hy
  have high : hi.Subsingleton := fun _ hx _ hy => IsGreatest.unique hx hy
  apply (low.finite.union high.finite).subset
  rintro r ⟨hm,hn⟩
  by_cases below : ∃ x ∈ B, p x < r
  · exact Or.inr ⟨hm,fun _ ⟨y,hy,he⟩ => le_of_not_gt (fun h => hn ⟨below,y,hy,he ▸ h⟩)⟩
  · exact Or.inl ⟨hm,fun _ ⟨y,hy,he⟩ => le_of_not_gt (fun h => below ⟨y,hy,he ▸ h⟩)⟩

theorem preimage_twoSidedLabels_subset [LinearOrder X] {p : X → R} (hp : Monotone p)
    {B : Set X} (hB : B.OrdConnected) : p ⁻¹' twoSidedLabels p B ⊆ B := by
  rintro x ⟨⟨a,ha,hl⟩,b,hb,hr⟩
  exact hB.out ha hb ⟨(hp.reflect_lt hl).le,(hp.reflect_lt hr).le⟩

/-- Only finitely many labels of a finite unary partition fail to lie
strictly inside at least one of its projected intervals. -/
theorem finite_labels_outside_branches [Finite I] (p : X → R) (B : I → Set X) {A : Set X}
    (cover : A ⊆ ⋃ i, B i) : (p '' A \ ⋃ i, twoSidedLabels p (B i)).Finite := by
  apply (finite_iUnion (fun i => finite_endpoint_labels p (B i))).subset
  rintro r ⟨⟨x,hx,rfl⟩,hn⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (cover hx)
  exact mem_iUnion_of_mem i ⟨mem_image_of_mem p hi,fun h => hn (mem_iUnion_of_mem i h)⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- Data on an individual nonzero branch from the finite partition of
Remark 3.30. The residue functions extend the two contractions on the
interval. The mean value identity is imposed on field representatives. -/
structure ResidueBranch (B : Set O) (g d : O → K) (c : K) where
  fieldValue : O → O
  fieldDerivative : O → O
  value : ∀ x ∈ B, (fieldValue x : K) = g x / c
  derivative : ∀ x ∈ B, (fieldDerivative x : K) = d x / c
  residueValue : Residue O → Residue O
  residueDerivative : Residue O → Residue O
  contracts : ∀ x ∈ B, IsLocalRing.residue O (fieldValue x) = residueValue (IsLocalRing.residue O x)
  contractsDerivative : ∀ x ∈ B, IsLocalRing.residue O (fieldDerivative x) = residueDerivative (IsLocalRing.residue O x)
  continuousDerivative : letI := residueLinearOrder O hO
    let U := twoSidedLabels (IsLocalRing.residue O) B
    ∀ r ∈ U, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ U, |s-r| < δ → |residueDerivative s-residueDerivative r| < ε
  meanValue : ∀ x ∈ B, ∀ y ∈ B, IsLocalRing.residue O x ≠ IsLocalRing.residue O y →
    ∃ z ∈ uIcc x y, (fieldValue y : K) - fieldValue x = ((y : K)-x)*fieldDerivative z

/-- The scale-independent test in 3.31 succeeds on the open interval
strictly between labels of the branch. -/
theorem normalizedSlice_in_branch {B : Set O} (hB : B.OrdConnected)
    {g d : O → K} {c : K} (H : ResidueBranch O hO B g d c) :
    letI := residueLinearOrder O hO
    let U := twoSidedLabels (IsLocalRing.residue O) B
    ∀ r ∈ U, NormalizedSliceAt O hO ((IsLocalRing.residue O) ⁻¹' U) g d c r := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let p := IsLocalRing.residue O
  let U := twoSidedLabels p B
  have inside : p ⁻¹' U ⊆ B := preimage_twoSidedLabels_subset (residue_monotone O hO) hB
  change ∀ r ∈ U, NormalizedSliceAt O hO (p ⁻¹' U) g d c r
  intro r hr
  have der : HasOrderDerivativeAt H.residueValue r (H.residueDerivative r) := by
    apply derivative_on_residue_interval O hO U H.fieldValue H.fieldDerivative _ _ r hr
      (fun x hx => H.contracts x (inside hx)) (fun x hx => H.contractsDerivative x (inside hx))
    · obtain ⟨⟨a,ha,hlo⟩,b,hb,hhi⟩ := hr
      refine ⟨min (r-p a) (p b-r),lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi),?_⟩
      intro h hsmall
      obtain ⟨hl,hu⟩ := lt_min_iff.mp hsmall
      exact ⟨⟨a,ha,by linarith [(abs_lt.mp hl).1]⟩,b,hb,by linarith [(abs_lt.mp hu).2]⟩
    · exact H.continuousDerivative r hr
    · intro x y hx hy hne
      obtain ⟨z,hz,hd⟩ := H.meanValue x (inside hx) y (inside hy) hne
      have between := (residue_monotone O hO).mapsTo_uIcc hz
      refine ⟨z,hz,?_,hd⟩
      obtain ⟨⟨a,ha,hal⟩,b,hb,hbh⟩ := hx
      obtain ⟨⟨a',ha',hal'⟩,b',hb',hbh'⟩ := hy
      rcases le_total (p x) (p y) with h | h
      · rw [uIcc_of_le h] at between
        exact ⟨⟨a,ha,hal.trans_le between.1⟩,b',hb',between.2.trans_lt hbh'⟩
      · rw [uIcc_of_ge h] at between
        exact ⟨⟨a',ha',hal'.trans_le between.1⟩,b,hb,between.2.trans_lt hbh⟩
  refine ⟨H.residueValue,fun x hx => ⟨H.fieldValue x,H.value x (inside hx),H.contracts x (inside hx)⟩,?_⟩
  intro x hx he
  refine ⟨H.fieldDerivative x,H.derivative x (inside hx),?_⟩
  rwa [H.contractsDerivative x (inside hx),he]

/-- Finiteness of the unary exception in 3.31 from the finite convex
partition in 3.30. The test uses every representative of the chosen
nonzero scale. Zero branches satisfy the zero derivative alternative. -/
theorem finite_normalized_slice_exceptions [Finite I] (A : Set O) (B : I → Set O)
    (g d : O → K) (c : I → K) (cover : A ⊆ ⋃ i, B i) (convex : ∀ i, (B i).OrdConnected)
    (branch : ∀ i, (∀ x ∈ B i, g x = 0 ∧ d x = 0) ∨
      (c i ≠ 0 ∧ Nonempty (ResidueBranch O hO (B i) g d (c i)))) :
    letI := residueLinearOrder O hO
    let p := IsLocalRing.residue O
    let U i := twoSidedLabels p (B i)
    (p '' A \ {r | ∃ i, r ∈ U i ∧
      ((∀ x, p x = r → g x = 0 ∧ d x = 0) ∨
       ∀ b, O.valuation b = O.valuation (c i) → NormalizedSliceAt O hO (p ⁻¹' U i) g d b r)}).Finite := by
  let := residueLinearOrder O hO
  apply (finite_labels_outside_branches (IsLocalRing.residue O) B cover).subset
  rintro r ⟨hr,hn⟩
  refine ⟨hr,fun h => ?_⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp h
  apply hn
  refine ⟨i,hi,?_⟩
  rcases branch i with hz | ⟨hc,⟨H⟩⟩
  · exact Or.inl (fun x hx => hz x (preimage_twoSidedLabels_subset (residue_monotone O hO) (convex i) (show IsLocalRing.residue O x ∈ _ from hx.symm ▸ hi)))
  · exact Or.inr (fun b hb => (normalizedSliceAt_iff_of_same_value O hO hc hb.symm).mp
      (normalizedSlice_in_branch O hO (convex i) H r hi))

end GeneralizedEuler.Section3
