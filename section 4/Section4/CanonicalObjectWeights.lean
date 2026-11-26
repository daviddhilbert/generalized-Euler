module

public import Section4.RectangleMultiplicativity
import all Section4.CanonicalRectangles
import all Section4.NormalRectangleCover

/-! The normalized rectangles required for multiplicativity exist over the
original base by the fixed-base rectangle theorem. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J JG JH JS : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure O.ValueGroupˣ]
  [JH.Structure (Residue O)] [JS.Structure (SignedValueGroup O)]
  (B : Set (Residue O)) (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
local instance objectCoverAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)


variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))

set_option maxHeartbeats 800000 in
include g agrees units clamp powers hv hs pull in
theorem canonical_object_rectangle_cover
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
      (fun e γ => (e • Additive.ofMul γ).toMul) P)
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ (G : Set (Additive O.ValueGroupˣ)) ∧
      ((linearValueSection v hv s hs).encode t.val).2 ∈ B)
    (reps : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
    (qe : ∀ {n} (φ : SortedFormula J F (FullRVVariables S (Fin n))), ∃ q : SortedFormula J F (FullRVVariables S (Fin n)), q.IsQF ∧
      ∀ x, q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)
    (sat : ∀ m (Δ : Set (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m))),
      (∀ t : Finset (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m)), (↑t : Set _) ⊆ Δ →
        ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ Δ, φ.Realize x)
    {n : ℕ} (U : Set (Fin n → RV0 O)) (hu : isRVSet _ S U) (pos : ∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) :
    HasRectangleCover (JG := JG) (G := G) O v hO P S n U := by
  classical
  let lang : ValueLanguage (J := JG) G :=
    ⟨definableFun_of_graph primitives.value_mul,fun t => definableFun_of_graph (primitives.value_power t)⟩
  obtain ⟨_,p,_,_,supports,charts⟩ := canonical_rectangles v hv s hs G B hO P g agrees units clamp powers
    primitives S base qe sat U hu
  exact positive_rectangle_cover O v hO P powers S lang s hs reps @pull U hu pos p supports charts

end GeneralizedEuler.Section4
