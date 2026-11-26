module

public import Section4.GlobalRectangleMatches
public import Section4.ResidualRectangleFamilies
import all Section4.GlobalRectangleMatches
import all Section4.RectangleFiberFamilies
import all Section4.Subrectangles
import all Section4.RefinedFamilyBijection
import all Section4.RVTaggedEquivalence
import all Section4.TaggedFiberMatching
import all Section4.ResidualRectangleFamilies

/-! Removing both projected families of matched labels restricts the
given RV bijection to the normalized residual families. -/
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

variable {height : ℕ}
variable (cuts : ∀ i j, PairCut (C := C) c pull hv s hs d f res val i j height)

private theorem remaining_iff {X Y : Type*} {P : Set X} {Q : Set Y} {I H : Type}
    (A : I → Set (X × Y)) (B : H → Set (X × Y)) (rem : (P ×ˢ Q) \ (⋃ i, A i) = ⋃ t, B t)
    {u : X} {a : Y} (hu : u ∈ P) (ha : a ∈ Q) :
    (∃ t, (u,a) ∈ B t) ↔ ¬∃ i, (u,a) ∈ A i := by
  rw [← Set.mem_iUnion,← rem]
  exact ⟨fun h ex => h.2 (Set.mem_iUnion.mpr ex),fun h => ⟨⟨hu,ha⟩,fun m => h (Set.mem_iUnion.mp m)⟩⟩

theorem normalized_remainder_iso
    (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j))
    {nl : I → ℕ} {nr : H → ℕ}
    (L : ∀ i, Fin (nl i) → Subrectangle (c i)) (R' : ∀ j, Fin (nr j) → Subrectangle (d j))
    (lDisj : ∀ i, Pairwise (fun t t' => Disjoint (L i t).labels (L i t').labels))
    (rDisj : ∀ j, Pairwise (fun t t' => Disjoint (R' j t).labels (R' j t').labels))
    (left : ∀ i, ((c i).units ×ˢ (c i).values) \ (⋃ t, (leftCut c pull hv s hs d f res val cuts i t).labels) =
      ⋃ t, (L i t).labels)
    (right : ∀ j, ((d j).units ×ˢ (d j).values) \ (⋃ t, (leftCut d pull hv s hs c f.symm res val
      (flippedCuts c pull hv s hs d f res val cuts) j t).labels) = ⋃ t, (R' j t).labels)
    (p : ((i : I) × Fin (nl i)) → NormalRectangle (JG := JG) (G := G) O v hO P S k)
    (q : ((j : H) × Fin (nr j)) → NormalRectangle (JG := JG) (G := G) O v hO P S k)
    (el : ∀ i t, RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (L i t).points (p ⟨i,t⟩).points)
    (er : ∀ j t, RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (R' j t).points (q ⟨j,t⟩).points) :
    (rvFamily p pull).Iso (rvFamily q pull) := by
  let e := onFibers c pull d f
  have keep (x : (rvFamily c pull).Points) : x ∈ Set.range (subfamily c pull L).includePoint ↔
      f x ∈ Set.range (subfamily d pull R').includePoint := by
    obtain ⟨t,rfl⟩ := (fiberEquiv c pull).surjective x
    let y := e t
    have fy : f (fiberEquiv c pull t) = fiberEquiv d pull y := ((fiberEquiv d pull).apply_symm_apply _).symm
    rw [fy,subfamily_range,subfamily_range]
    exact (remaining_iff _ _ (left t.1.1) t.1.2.property t.2.property).trans
      ((not_congr (matched_membership_preserved c pull hv s hs d f res val cuts t)).trans
        (remaining_iff _ _ (right y.1.1) y.1.2.property y.2.property).symm)
  have restrict := RVFamily.Subfamily.restrict_bijection (subfamily c pull L) (subfamily d pull R') f graph
    (subfamily_injective c pull L lDisj) (subfamily_injective d pull R' rDisj) keep
  have lf := subfamily_iso_normal c pull L p el
  have rf := subfamily_iso_normal d pull R' q er
  exact RVFamily.iso_trans _ _ _ (RVFamily.iso_symm _ _ lf) (RVFamily.iso_trans _ _ _ restrict rf)

end GeneralizedEuler.Section4.NormalRectangle
