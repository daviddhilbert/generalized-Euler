module

public import Section4.IndependentRectangleMatches
public import Section4.UnmatchedValueProjection
import all Section4.WholeMatchRectangles
import all Section4.UnmatchedValueProjection
import all Section4.MixedMatchFactors
import all Section4.RectangleFiberFamilies
import all Section4.RectangleMatchGraph
import all Section4.TaggedFiberMatching
import all Section4.NormalRectangles
import all Section4.IndependentRectangleMatches
import all Section4.DefinableValueFrames

/-! In a maximal-height rectangle, the projection of all unmatched
fibers is definable over the base value parameters. Its full disjoint
affine stratification has strictly smaller rank. -/
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
local instance remainderValueStructure : JG.Structure O.ValueGroupˣ := inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
    (fun e γ => (e • Additive.ofMul γ).toMul) P)
  (baseRes : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).2 ∈ B)

def matchedOver (i : I) (j : H) : Set ((Fin (c i).r → Additive O.ValueGroupˣ) × (Fin (c i).m → v.ker)) :=
  {z | ∃ b w, ((Additive.toMul ∘ z.1,b),kernelResidue v ∘ z.2,w) ∈
    labelMatching c pull (linearValueSection v hv s hs) d f i j}

def unmatchedValues (i : I) : Set (Fin (c i).r → Additive O.ValueGroupˣ) :=
  {a | a ∈ (c i).values ∧ ∃ u ∈ (c i).units, ∀ j : {j : H // (d j).r = (c i).r},
    (a,u) ∉ matchedOver c pull hv s hs d f i j.val}

include graph agrees units clamp powers base qe prim baseRes in
theorem unmatchedValues_definable (i : I) :
    (G : Set (Additive O.ValueGroupˣ)).Definable JG (unmatchedValues c pull hv s hs d f i) := by
  let sec := linearValueSection v hv s hs
  have secPower (e) (γ : O.ValueGroupˣ) : P e (sec.representative γ) = sec.representative (e • Additive.ofMul γ).toMul :=
    (powers e _).symm.trans (congrArg (fun t : Additive (PositiveRV O) => positiveRVToRV0 O t.toMul) (s.map_smul e _).symm)
  apply unmatched_value_projection (c i).valuesDef (c i).units
    (fun j : {j : H // (d j).r = (c i).r} => matchedOver c pull hv s hs d f i j.val)
  intro j
  have sep := mixed_graph_separated sec prim g agrees clamp units secPower S (fun t => ⟨base t,baseRes t⟩)
    qe _ (whole_graph_definable c pull d f graph i j.val)
  have proj := SeparatedSets.image Prod.fst Prod.fst (left' := (G : Set (Additive O.ValueGroupˣ)).Definable JG)
    (right' := fun _ => True) (fun hd => matchedDomain_definable hd) (fun _ => trivial) sep
  have pre := SeparatedSets.preimage (fun a : Fin (c i).r → Additive O.ValueGroupˣ => Additive.toMul ∘ a)
    (fun u : Fin (c i).m → v.ker => kernelResidue v ∘ u)
    (left' := (G : Set (Additive O.ValueGroupˣ)).Definable JG) (right' := fun _ => True)
    (fun h => h) (fun _ => trivial) proj
  convert pre using 1
  ext z
  constructor
  · rintro ⟨b,w,m⟩
    exact ⟨((Additive.toMul ∘ z.1,b),kernelResidue v ∘ z.2,w),m,rfl⟩
  · rintro ⟨⟨⟨a,b⟩,u,w⟩,m,e⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    exact ⟨b,w,m⟩

include graph agrees units clamp powers base qe prim baseRes in
theorem maximal_remainder_strata (i : I) (maximal : ∀ j, (d j).r ≤ (c i).r)
    (lang : ValueLanguage (J := JG) G)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D)) :
    ∃ (n : ℕ) (q : Fin n → IndependentPiece (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D) G (c i).r),
      (∀ t, (q t).rank < (c i).r) ∧ unmatchedValues c pull hv s hs d f i = ⋃ t, (q t).support ∧
      Pairwise (fun t t' => Disjoint (q t).support (q t').support) := by
  apply unmatched_stratification (fun p D t h => lang.cut p D t h) sat
    (unmatchedValues_definable c pull hv s hs d f graph g agrees units clamp powers base qe B prim baseRes i)
  rintro a ⟨ha,u,hu,missing⟩ ind
  let z : (fiberFamily c).Label := ⟨⟨i,u,hu⟩,a,ha⟩
  obtain ⟨b,height,m⟩ := independent_label_match c pull hv s hs d f graph g agrees units clamp powers base qe z ind maximal
  exact missing ⟨b.1.1,height⟩ ⟨_,_,m⟩

end GeneralizedEuler.Section4.NormalRectangle
