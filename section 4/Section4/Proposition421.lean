module

public import Section4.CanonicalSurjectivity
public import Section4.CanonicalObjectWeights
public import Section4.ResidueFactorAssignment
public import Section4.FactorRecovery
import all Section4.SignedTensorFactors
import all Section4.SignedValueGeneration
import all Section4.ValuePullback
import all Section4.SignedRectangleFactors
import all Section4.CanonicalChartCover
import all Section4.CanonicalChartMaps
import all Section4.NormalRectangleCover
import all Section4.PositiveObjectCover
import all Section4.RectangleMap
import all Section4.Factors
import all Section4.ResidueScissors
import all Section4.Objects

/-! Proposition 4.21, graph proof. The map on the actual fixed-base
semirings is bijective. The inverse is computed by positive chart
decomposition, including the recovery of arbitrary tagged signed pieces. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
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
open scoped TensorProduct
local instance prop421AdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

local instance prop421SignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) :=
  inferInstanceAs (JS.Structure (SignedValueGroup O))

variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp _ (signedLabel O hO) D))
  (liftIso : ∀ {k} (D C : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS C →
    ∀ e : D ≃ C, A.Definable JS {w : Fin k ⊕ Fin k → SignedValueGroup O |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp _ (signedLabel O hO) D) (sharp _ (signedLabel O hO) C))
  (interpret : SignedInterpretation (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A)
  (he : A.Definable JS ({1} : Set (Fin 1 → SignedValueGroup O)))
include g agrees units clamp powers hv hs interpret in
set_option maxHeartbeats 1800000 in
theorem proposition_4_21
    (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
      (fun e γ => (e • Additive.ofMul γ).toMul) P)
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ (G : Set (Additive O.ValueGroupˣ)) ∧
      ((linearValueSection v hv s hs).encode t.val).2 ∈ B)
    (reps : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
    (minus : rv O (-1) ∈ S.carrier .rv)
    (qe : ∀ {n} (φ : SortedFormula J F (FullRVVariables S (Fin n))), ∃ q : SortedFormula J F (FullRVVariables S (Fin n)), q.IsQF ∧
      ∀ x, q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)
    (sat : ∀ m (Δ : Set (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m))),
      (∀ t : Finset (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m)), (↑t : Set _) ⊆ Δ →
        ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ Δ, φ.Realize x)
    (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    Function.Bijective (balancedRectangleMap _ S (signedLabel O hO) A defSharp liftIso 1 he) := by
  classical
  let M := canonicalStructure (L := J) O hO P
  let R := ResidueSemiring M S (signedLabel O hO)
  let W := SemiringOfSets (J := JS) A
  let C := Polynomial ℕ
  let line := residueClass (sharpObject M S (signedLabel O hO) {1} (defSharp he))
    (sharp_residue M S (signedLabel O hO) A defSharp {1} (Set.finite_singleton _) he)
  let point := pieceClass {1} he
  let := (Polynomial.eval₂RingHom (Nat.castRingHom R) line).toAlgebra
  let := (Polynomial.eval₂RingHom (Nat.castRingHom W) point).toAlgebra
  let rmap := RingHom.id R
  have signedDef {n} {D : Set (Fin n → Additive O.ValueGroupˣ)} (hd : (G : Set _).Definable JG D) :
      A.Definable JS ((fun γ => positiveValueLabel O ∘ γ) '' D) :=
    signed_stratum_definable (V := Additive O.ValueGroupˣ) (Z := SignTypeˣ) (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A @interpret (fun _ => 1) D hd
  let vmap := signedPieceMap O G A @signedDef
  let x : C := Polynomial.X
  have rb : algebraMap C R x = rmap (entireUnitWeight O v hv hO P S 1) :=
    (Polynomial.eval₂_X (Nat.castRingHom R) line).trans (residue_sharp_generator O v hv hO P S A defSharp he)
  have vb : algebraMap C W x = vmap (eValue (J := JG) G) :=
    (Polynomial.eval₂_X (Nat.castRingHom W) point).trans (signedPieceMap_generator O G A @signedDef).symm
  let lang : ValueLanguage (J := JG) G :=
    ⟨definableFun_of_graph primitives.value_mul,fun t => definableFun_of_graph (primitives.value_power t)⟩
  have pull {n} {D : Set (Fin n → Additive O.ValueGroupˣ)} (hD : (G : Set _).Definable JG D) : isRVSet M S (positiveSharp O v D) := by
    rw [← signed_sharp_positive (J := J) O hO v hv P D]; exact defSharp (signedDef hD)
  have atlas {n} (U : Set (Fin n → RV0 O)) (d : isRVSet M S U) (p : ∀ y ∈ U, ∀ i, IsPositiveRV O (y i)) :=
    canonical_admits_charts O v hv s hs G B hO P g agrees units clamp powers S @pull primitives base reps qe sat U d p
  have cov {n} (U : Set (Fin n → RV0 O)) (h : GoodRVSet M S (IsPositiveRV O) U) :=
    canonical_object_rectangle_cover O v hv s hs G B hO P g agrees units clamp powers S @pull primitives base reps qe sat U h.1 h.2
  have old (t : S.carrier .rv) : Additive.ofMul (RVValueSection.valueCoordinate t.val) ∈ G := (base t).1
  have inv {m n} (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker) (D : Set (Fin m ⊕ Fin n → RV0 O))
      (hd : isRVSet M S D) (y : Fin m ⊕ Fin n → RV0 O) (hy : y ∈ D) : signedShear v hv s hs G L ∘ y ∈ D := by
    let f := signedShear v hv s hs G L
    let h := signedShear_reduct (J := J) v hv s hs G L hO g P agrees units clamp powers
    let a : Fin m ⊕ Fin n ≃ Fin (m+n) := finSumFinEquiv
    have eq (z : Fin m ⊕ Fin n → RV0 O) : z ∘ a.symm ∘ a = z := funext (fun j => congrArg z (a.symm_apply_apply j))
    have packed := isRVSet_precomp a hd
    have action := h.setInvariant S (fun t => signedShear_base v hv s hs G L _ (old t)) qe packed (y ∘ a.symm)
    exact (congrArg (· ∈ D) (eq (f ∘ y))).mp (action.mpr ((congrArg (· ∈ D) (eq y)).mpr hy))
  let back := rvTensorAssignment O v hv hO P powers S lang x rmap vmap rb vb s hs (lang.avoidance sat)
    @atlas @pull @cov minus @rvSat
  let forward : R ⊗[C] W →+* RVSemiring M S := balancedRectangleMap M S (signedLabel O hO) A defSharp liftIso 1 he
  let res := includeResidue M S (signedLabel O hO)
  let val := valueFactorHom M S (signedLabel O hO) A defSharp liftIso
  have left : back.comp res = (Algebra.TensorProduct.includeLeft : R →ₐ[C] R ⊗[C] W).toRingHom := by
    apply presented_hom_ext (residueRelation M S (signedLabel O hO))
    rintro ⟨⟨n,U⟩,hu⟩
    change back (includeResidue M S _ (residueClass U hu)) = residueClass U hu ⊗ₜ[C] (1 : W)
    rw [includeResidue_class]
    apply rvTensorAssignment_assigned O v hv hO P powers S lang x rmap vmap rb vb s hs (lang.avoidance sat) @atlas @pull @cov minus @rvSat
    exact residue_factor_assignment O v hv hO P powers S lang x rmap vmap rb vb s hs (lang.avoidance sat)
      @atlas @pull @witness old @inv minus @rvSat U hu
  have right : back.comp val = (Algebra.TensorProduct.includeRight : W →ₐ[C] R ⊗[C] W).toRingHom := by
    apply recover_signed_pieces (V := Additive O.ValueGroupˣ) (Z := SignTypeˣ) (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A (1 : SignTypeˣ) @interpret
    intro n D hd
    let sd := (fun γ => positiveValueLabel O ∘ γ) '' D
    change back (valueFactorHom M S _ A defSharp liftIso (pieceClass sd (signedDef hd))) = (1 : R) ⊗ₜ[C] pieceClass sd (signedDef hd)
    rw [valueFactorHom_piece,← signedPieceMap_class O G A @signedDef D hd]
    apply rvTensorAssignment_assigned O v hv hO P powers S lang x rmap vmap rb vb s hs (lang.avoidance sat) @atlas @pull @cov minus @rvSat
    change (tensorLocalMeasure (k := n) O v hv hO P powers S lang x rmap vmap rb vb s hs (lang.avoidance sat)
      @atlas).assigned (sharp M (signedLabel O hO) sd) _
    rw [signed_sharp_positive (J := J) O hO v hv P]
    exact positive_sharp_assignment O v hv hO P powers S lang x rmap vmap rb vb s hs (lang.avoidance sat) @atlas @pull D hd
  have inverse := tensor_left_inverse_of_factors forward back res val (fun _ _ => rfl) left right
  exact ⟨inverse.injective,canonical_rectangle_surjective O v hv s hs G B hO P g agrees units clamp powers S A
    defSharp liftIso @signedDef 1 he primitives base reps minus qe sat @rvSat⟩

end GeneralizedEuler.Section4
