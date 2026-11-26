module

public import Section4.MatchingSlices
public import Section4.MatchedResidueClasses
import all Section4.MixedMatchFactors
import all Section4.WholeMatchRectangles
import all Section4.MatchedResidueGraphs
import all Section4.RectangleMatchGraph
import all Section4.RectangleFiberFamilies
import all Section4.IndependentRectangleMatches
import all Section4.NormalRectangles

/-! The actual finite matching carries definable graphs in both concrete
factor categories. Base representatives from Remark 4.1 define the
residue graph in RV for each nonempty value cell. -/
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
  {G : Submodule F (Additive O.ValueGroupˣ)} {k l : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S l)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

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
local instance matchedSliceValueStructure : JG.Structure O.ValueGroupˣ := inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
    (fun e γ => (e • Additive.ofMul γ).toMul) P)
  (baseRes : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).2 ∈ B)

variable (rep : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)

include graph agrees units clamp powers base qe prim baseRes rep witness in
theorem concrete_matching_slices (i : I) (j : H) :
    ∃ (n : ℕ) (q : Fin n → MatchingSlice (Fin (c i).r → O.ValueGroupˣ) (Fin (d j).r → O.ValueGroupˣ)
        (Fin (c i).m → Residue O) (Fin (d j).m → Residue O)),
      (∀ t, (G : Set (Additive O.ValueGroupˣ)).Definable JG (pairedSet (q t).values) ∧
        B.Definable JH (pairedSet (q t).residues) ∧ isRVSet _ S (residueGraphCode (q t).residues)) ∧
      Pairwise (fun t t' => Disjoint (q t).values (q t').values) ∧
      labelMatching c pull (linearValueSection v hv s hs) d f i j = ⋃ t, (q t).values ×ˢ (q t).residues ∧
      ∀ t a b, (a,b) ∈ (q t).values → ∀ u w, (u,w) ∈ (q t).residues ↔
        ((a,b),u,w) ∈ labelMatching c pull (linearValueSection v hv s hs) d f i j := by
  let sec := linearValueSection v hv s hs
  have secPower (e) (γ : O.ValueGroupˣ) : P e (sec.representative γ) = sec.representative (e • Additive.ofMul γ).toMul :=
    (powers e _).symm.trans (congrArg (fun t : Additive (PositiveRV O) => positiveRVToRV0 O t.toMul) (s.map_smul e _).symm)
  have sep := mixed_graph_separated sec prim g agrees clamp units secPower S (fun t => ⟨base t,baseRes t⟩)
    qe _ (whole_graph_definable c pull d f graph i j)
  obtain ⟨n,q,hd,dj,cover,full⟩ := matching_slices (P := fun D => (G : Set (Additive O.ValueGroupˣ)).Definable JG (pairedSet D))
    (Q := fun R => B.Definable JH (pairedSet R)) Set.definable_univ (fun h k => h.inter k) (fun h => h.compl)
    Set.definable_empty (fun h k => h.union k) sep (labelMatching_functional c pull sec d f i j)
    (fun h h' => labelMatching_functional d pull sec c f.symm j i
      ((labelMatching_inverse c pull sec d f i j _ _ _ _).mpr h)
      ((labelMatching_inverse c pull sec d f i j _ _ _ _).mpr h'))
  refine ⟨n,q,fun t => ⟨(hd t).1,(hd t).2,?_⟩,dj,cover,fun t a b h u w => full t (a,b) h (u,w)⟩
  exact residue_match_definable c pull hv s hs d f graph base rep witness i j (hd t).1 (q t).values_nonempty
    (q t).residues (fun a b h u w => full t (a,b) h (u,w))

end GeneralizedEuler.Section4.NormalRectangle
