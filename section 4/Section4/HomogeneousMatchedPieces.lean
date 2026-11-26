module

public import Section4.ConcreteMatchingSlices
public import Section4.MatchedRectangleWeights
public import Section4.Subrectangles
public import Section4.RectangleLabelMatching
import all Section4.MatchedRectangleWeights
import all Section4.MatchedResidueGraphs
import all Section4.ConcreteMatchingSlices
import all Section4.Subrectangles
import all Section4.MatchingSlices
import all Section4.RectangleFiberFamilies
import all Section4.RectangleLabelMatching
import all Section4.NormalRectangles

/-! Matched pieces with their original homogeneous degree. Their source
and target label sets are products; on those products the given RV
bijection carries whole fibers across the actual matching graph. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S k)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)

def localLabel (i : I) (u : (c i).units) (a : (c i).values) : (fiberFamily c).Label := ⟨⟨i,u⟩,a⟩

variable (i : I) (j : H)
  (q : MatchingSlice (Fin (c i).r → Additive O.ValueGroupˣ) (Fin (d j).r → Additive O.ValueGroupˣ)
    (Fin (c i).m → Residue O) (Fin (d j).m → Residue O))

def withinSlice (u : (c i).units) (a : (c i).values) (w : (d j).units) (b : (d j).values) : Prop :=
  (a.val,b.val) ∈ q.values ∧ (kernelResidue v ∘ u.val,kernelResidue v ∘ w.val) ∈ q.residues

include hv hs in
theorem homogeneous_slice_projections
    (height : (c i).r = (d j).r) (dv : (G : Set (Additive O.ValueGroupˣ)).Definable JG (pairedSet q.values))
    (dr : isRVSet _ S (residueGraphCode q.residues))
    (slice : ∀ a b, (a,b) ∈ q.values → ∀ u w, (u,w) ∈ q.residues ↔
      ((a,b),u,w) ∈ labelMatching c pull (linearValueSection v hv s hs) d f i j) :
    ∃ (left : Subrectangle (c i)) (right : Subrectangle (d j)),
      left.rect.tensor hv res val (C := C) = right.rect.tensor hv res val ∧
      (∀ u a, (u.val,a.val) ∈ left.labels ↔ ∃ w b, withinSlice c d i j q u a w b) ∧
      (∀ w b, (w.val,b.val) ∈ right.labels ↔ ∃ u a, withinSlice c d i j q u a w b) := by
  have sameM : (c i).m = (d j).m := by have := (c i).degree; have := (d j).degree; omega
  obtain ⟨⟨a₀,b₀⟩,h₀⟩ := q.values_nonempty
  obtain ⟨⟨u₀,w₀⟩,r₀⟩ := q.residues_nonempty
  have actual (u w) (h : (u,w) ∈ q.residues) :=
    matched_residues_in_units c pull hv s hs d f i j a₀ b₀ u w ((slice _ _ h₀ _ _).mp h)
  have inside (a b) (h : (a,b) ∈ q.values) := matched_values_in_domains c pull hv s hs d f i j a b u₀ w₀ ((slice _ _ h _ _).mp r₀)
  obtain ⟨hu,hw,weight⟩ := equal_height_slice_tensors (C := C) hv s hs res val sameM height q dv dr (c i).units (d j).units actual
  let left : Subrectangle (c i) := ⟨_,_,hu,matchedDomain_definable dv,Set.inter_subset_left,
    fun _ ⟨⟨a,b⟩,h,e⟩ => e ▸ (inside a b h).1⟩
  let right : Subrectangle (d j) := ⟨_,_,hw,matchedRange_definable dv,Set.inter_subset_left,
    fun _ ⟨⟨a,b⟩,h,e⟩ => e ▸ (inside a b h).2⟩
  refine ⟨left,right,weight,?_,?_⟩
  · intro u a
    constructor
    · rintro ⟨⟨_,w,hw⟩,⟨⟨a',b⟩,h,e⟩⟩
      have ab : (a.val,b) ∈ q.values := (show a'=a.val from e) ▸ h
      obtain ⟨r,hr,eq⟩ := (actual _ w hw).2
      exact ⟨⟨r,hr⟩,⟨b,(inside _ _ ab).2⟩,ab,eq.symm ▸ hw⟩
    · rintro ⟨w,b,h,r⟩
      exact ⟨⟨u.property,_,r⟩,⟨_,h,rfl⟩⟩
  · intro w b
    constructor
    · rintro ⟨⟨_,u,hu⟩,⟨⟨a,b'⟩,h,e⟩⟩
      have ab : (a,b.val) ∈ q.values := (show b'=b.val from e) ▸ h
      obtain ⟨r,hr,eq⟩ := (actual u _ hu).1
      exact ⟨⟨r,hr⟩,⟨a,(inside _ _ ab).1⟩,ab,eq.symm ▸ hu⟩
    · rintro ⟨u,a,h,r⟩
      exact ⟨⟨w.property,_,r⟩,⟨_,h,rfl⟩⟩

end GeneralizedEuler.Section4.NormalRectangle
