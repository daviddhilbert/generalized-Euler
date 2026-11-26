module

public import Section4.HomogeneousMatchedPieces
import all Section4.HomogeneousMatchedPieces
import all Section4.ConcreteMatchingSlices
import all Section4.RectangleLabelMatching
import all Section4.RectangleFiberFamilies
import all Section4.Subrectangles
import all Section4.NormalRectangles
import all Section4.WholeMatchRectangles

/-! The common finite list of matched subrectangles for a pair of
maximal-height summands. Every listed term has the same tensor on the
two sides, and the two projected label sets are exact. -/
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

variable (i : I) (j : H)

structure PairCut (height : ℕ) where
  count : ℕ
  left : Fin count → Subrectangle (c i)
  right : Fin count → Subrectangle (d j)
  matched : Fin count → (c i).units → (c i).values → (d j).units → (d j).values → Prop
  weights : ∀ t, (left t).rect.tensor hv res val = (right t).rect.tensor hv res val (C := C)
  dom : ∀ t u a, (u.val,a.val) ∈ (left t).labels ↔ ∃ w b, matched t u a w b
  ran : ∀ t w b, (w.val,b.val) ∈ (right t).labels ↔ ∃ u a, matched t u a w b
  unique : ∀ t t' u a w b, matched t u a w b → matched t' u a w b → t=t'
  full : ∀ u a w b, (∃ t, matched t u a w b) ↔
    (c i).r = height ∧ (d j).r = height ∧
      keyMatch c pull hv s hs d f (localLabel c i u a) (localLabel d j w b)

variable (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j))
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

variable {JH : Language} [JH.Structure (Residue O)] (B : Set (Residue O))
local instance pairCutValueStructure : JG.Structure O.ValueGroupˣ := inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
    (fun e γ => (e • Additive.ofMul γ).toMul) P)
  (baseRes : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).2 ∈ B)

variable (rep : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)

include graph agrees units clamp powers base qe prim baseRes rep witness in
theorem pair_cut_exists (height : ℕ) : Nonempty (PairCut (C := C) c pull hv s hs d f res val i j height) := by
  classical
  by_cases top : (c i).r = height ∧ (d j).r = height
  · obtain ⟨n,q,defs,dj,cover,slice⟩ := concrete_matching_slices c pull hv s hs d f graph g agrees units clamp powers
      base qe B prim baseRes rep witness i j
    have each (t : Fin n) := homogeneous_slice_projections (C := C) c pull hv s hs d f res val i j (q t)
      (top.1.trans top.2.symm) (defs t).1 (defs t).2.2 (slice t)
    choose left right eq dom ran using each
    refine ⟨⟨n,left,right,fun t => withinSlice c d i j (q t),eq,dom,ran,?_,?_⟩⟩
    · intro t t' u a w b h h'
      exact Classical.byContradiction fun ne => Set.disjoint_left.mp (dj ne) h.1 h'.1
    · intro u a w b
      constructor
      · rintro ⟨t,v,r⟩
        exact ⟨top.1,top.2,(slice t _ _ v _ _).mp r⟩
      · rintro ⟨_,_,h⟩
        have hx : ((a.val,b.val),kernelResidue v ∘ u.val,kernelResidue v ∘ w.val) ∈ ⋃ t, (q t).values ×ˢ (q t).residues :=
          (congrArg (_ ∈ ·) cover).mp h
        exact Set.mem_iUnion.mp hx
  · refine ⟨⟨0,Fin.elim0,Fin.elim0,Fin.elim0,(fun t => t.elim0),(fun t => t.elim0),(fun t => t.elim0),(fun t => t.elim0),?_⟩⟩
    exact fun _ _ _ _ => ⟨fun ⟨t,_⟩ => t.elim0,fun h => (top ⟨h.1,h.2.1⟩).elim⟩

end GeneralizedEuler.Section4.NormalRectangle
