module

public import Section4.RectangleMatchGraph
public import Section4.MixedMatchFactors
import all Section4.MixedMatchFactors
import all Section4.RectangleMatchGraph
import all Section4.RepresentedFiberMatches
import all Section4.RectangleFiberFamilies
import all Section4.SignedRectangleFactors
import all Section4.RVTaggedEquivalence
import all Section2.RVSplitCoordinates

/-! The actual whole-match graph of two normalized rectangles splits
over the fixed base. Each nonempty factor is the graph of a bijection
between its coordinate projections. -/
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

variable (s : RVValueSection O)

omit [Finite I] in
theorem mixedLabel_injective (i : I) {a b : Fin (c i).r → O.ValueGroupˣ} {u w : Fin (c i).m → Residue O}
    (same : rawLabel c i (mixedPair s u a) = rawLabel c i (mixedPair s w b)) : a = b ∧ u = w := by
  have both := (Sigma.mk.inj_iff.mp same).2.eq
  have vals := congrArg Prod.snd both
  have res := congrArg Prod.fst both
  have rep (γ) : (signedLabel O hO (s.representative γ)).2 = γ := by
    change (signedLabel O hO (positiveRVToRV0 O (s.lift γ))).2 = γ
    rw [signedLabel_code]
    exact s.value_lift _
  constructor
  · funext t
    exact (rep _).symm.trans ((congrArg Prod.snd (congrFun vals t)).trans (rep _))
  · exact funext fun j => residueRV_injective O (congrFun res j)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S l)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

def labelMatching (i : I) (j : H) := mixedGraph s (RVFamily.representedMatches (rvFamily c pull) (rvFamily d pull)
  (a := pointLabel c pull) (b := pointLabel d pull) f i j)

theorem labelMatching_functional (i : I) (j : H) {a b b' u w w'}
    (one : ((a,b),u,w) ∈ labelMatching c pull s d f i j)
    (two : ((a,b'),u,w') ∈ labelMatching c pull s d f i j) : b = b' ∧ w = w' := by
  obtain ⟨hx,hy,h⟩ := (RVFamily.mem_representedMatches _ _ _ _ _ _ _).mp one
  obtain ⟨_,hy',h'⟩ := (RVFamily.mem_representedMatches _ _ _ _ _ _ _).mp two
  let x : (rvFamily c pull).Points := ⟨i,mixedPair s u a,hx⟩
  have left := ((wholeMatch_iff _ _ _ _ _).mp h x).mp rfl
  have right := ((wholeMatch_iff _ _ _ _ _).mp h' x).mp rfl
  exact mixedLabel_injective d s j (left.symm.trans right)

theorem labelMatching_inverse (i : I) (j : H) (a b u w) :
    ((b,a),w,u) ∈ labelMatching d pull s c f.symm j i ↔ ((a,b),u,w) ∈ labelMatching c pull s d f i j :=
  RVFamily.representedMatches_inverse _ _ f i j _ _

variable {JH : Language} [JH.Structure (Residue O)] {B : Set (Residue O)}
  {p : F → O.ValueGroupˣ → O.ValueGroupˣ}
local instance valueStructure : JG.Structure O.ValueGroupˣ := inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B p P)
  (g : F → PositiveField K →* PositiveField K) (power : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (sectionPower : ∀ e γ, P e (s.representative γ) = s.representative (p e γ))
  (base : ∀ t : S.carrier .rv, (s.encode t.val).1 ∈ G ∧ (s.encode t.val).2 ∈ B)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

include prim g power clamp units sectionPower base qe in
theorem whole_match_rectangles (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j)) (i : I) (j : H) :
    ∃ (n : ℕ) (D : Fin n → Set ((Fin (c i).r → O.ValueGroupˣ) × (Fin (d j).r → O.ValueGroupˣ)))
      (R : Fin n → Set ((Fin (c i).m → Residue O) × (Fin (d j).m → Residue O))),
      (∀ t, (G : Set (Additive O.ValueGroupˣ)).Definable JG (pairedSet (D t)) ∧ B.Definable JH (pairedSet (R t))) ∧
      labelMatching c pull s d f i j = ⋃ t, D t ×ˢ R t ∧
      Pairwise (fun t t' => Disjoint (D t ×ˢ R t) (D t' ×ˢ R t')) ∧
      ∀ t, ∃ (η : {a // ∃ b, (a,b) ∈ D t} ≃ {b // ∃ a, (a,b) ∈ D t})
        (q : {u // ∃ w, (u,w) ∈ R t} ≃ {w // ∃ u, (u,w) ∈ R t}),
        ∀ a u b w, (a.val,b.val) ∈ D t ∧ (u.val,w.val) ∈ R t ↔ η a = b ∧ q u = w := by
  apply mixed_graph_factors s prim g power clamp units sectionPower S base qe _
    (whole_graph_definable c pull d f graph i j) (labelMatching_functional c pull s d f i j)
  intro a a' b u u' w h h'
  exact labelMatching_functional d pull s c f.symm j i
    ((labelMatching_inverse c pull s d f i j _ _ _ _).mpr h)
    ((labelMatching_inverse c pull s d f i j _ _ _ _).mpr h')

end GeneralizedEuler.Section4.NormalRectangle
