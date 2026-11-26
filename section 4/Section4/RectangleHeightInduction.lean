module

public import Section4.RectangleHeightStep
import all Section4.RectangleHeightStep
import all Section4.RectanglePairCuts
import all Section4.NormalRectangles

/-! The finite height induction comparing two tagged rectangle presentations. -/
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
variable {I H : Type} [Fintype I] [Fintype H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S k)

open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)

variable (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

variable (lang : ValueLanguage (J := JG) G) (e : C)
  (resBalance : algebraMap C R e = res (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = val (eValue (J := JG) G))
  (rep : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))

variable {JH : Language} [JH.Structure (Residue O)] (B : Set (Residue O))
local instance heightInductionValueStructure : JG.Structure O.ValueGroupˣ := inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
    (fun e γ => (e • Additive.ofMul γ).toMul) P)
  (baseRes : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).2 ∈ B)

variable (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)


include agrees units clamp powers base qe lang resBalance valBalance rep sat prim baseRes witness in
theorem normal_rectangle_families_equal (iso : (rvFamily c pull).Iso (rvFamily d pull)) :
    (∑ i, (c i).tensor hv res val (C := C)) = ∑ j, (d j).tensor hv res val := by
  classical
  have compare (n : ℕ) : ∀ {A B : Type} [Fintype A] [Fintype B]
      (p : A → NormalRectangle (JG := JG) (G := G) O v hO P S k)
      (q : B → NormalRectangle (JG := JG) (G := G) O v hO P S k),
      (∀ i, (p i).r < n) → (∀ j, (q j).r < n) → (rvFamily p pull).Iso (rvFamily q pull) →
      (∑ i, (p i).tensor hv res val (C := C)) = ∑ j, (q j).tensor hv res val := by
    induction n with
    | zero =>
      intro A B _ _ p q hp hq _
      let _ : IsEmpty A := ⟨fun i => Nat.not_lt_zero _ (hp i)⟩
      let _ : IsEmpty B := ⟨fun j => Nat.not_lt_zero _ (hq j)⟩
      simp
    | succ h lower =>
      intro A T _ _ p q hp hq ⟨f,graph⟩
      let cuts i j := Classical.choice (pair_cut_exists (JH := JH) (C := C) p pull hv s hs q f res val i j
        graph g agrees units clamp powers base qe B prim baseRes rep witness h)
      exact height_step p pull hv s hs q f res val cuts graph g agrees units clamp powers base qe
        lang e resBalance valBalance rep sat (fun i => Nat.le_of_lt_succ (hp i))
        (fun j => Nat.le_of_lt_succ (hq j)) (@lower)
  exact compare (k+1) c d (fun i => by have := (c i).degree; omega)
    (fun j => by have := (d j).degree; omega) iso

end GeneralizedEuler.Section4.NormalRectangle
