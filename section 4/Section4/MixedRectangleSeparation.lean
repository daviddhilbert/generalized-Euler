module

public import Section4.CanonicalRectangles
import all Section2.RVCoordinatePrimitives
import all Section2.RVSplitCoordinates

/-! Slice a definable RV relation at residue one in its value variables
and at value one in its residue variables. The resulting relation is a
finite union of products over the two original parameter sets. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} {J JG JH : Language} [J.Structure K] [J.Structure (Residue O)]
  [JG.Structure O.ValueGroupˣ] [JH.Structure (Residue O)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {A : Set O.ValueGroupˣ} {B : Set (Residue O)} {p : F → O.ValueGroupˣ → O.ValueGroupˣ}
  (s : RVValueSection O)
  (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO A B p P)
  (g : F → PositiveField K →* PositiveField K) (power : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (sectionPower : ∀ e γ, P e (s.representative γ) = s.representative (p e γ))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (base : ∀ t : S.carrier .rv, (s.encode t.val).1 ∈ A ∧ (s.encode t.val).2 ∈ B)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

include prim g power clamp units sectionPower base qe in
theorem mixed_rectangle_separation {I H : Type} [Finite I] [Finite H]
    (U : Set (I ⊕ H → RV0 O)) (hu : isRVSet _ S U) :
    SeparatedSets (A.Definable JG) (B.Definable JH)
      {z : (H → O.ValueGroupˣ) × (I → Residue O) |
        Sum.elim (residueRV O ∘ z.2) (s.representative ∘ z.1) ∈ U} := by
  let Q := s.canonicalCoordinatePresentation prim g power clamp units sectionPower
  have h := Q.separated_rv_pullback S hu qe base (s.separated_decoded_coordinate_graph prim)
  let vals (x : H → O.ValueGroupˣ) : I ⊕ H → O.ValueGroupˣ := Sum.elim (fun _ => 1) x
  let res (u : I → Residue O) : I ⊕ H → Residue O := Sum.elim u (fun _ => 1)
  have hv : A.DefinableMap JG vals := by
    intro i
    exact Sum.rec (fun _ => JG.definableFun_const H prim.value_one)
      (fun _ => Set.DefinableFun.proj JG) i
  have hr : B.DefinableMap JH res := by
    intro i
    exact Sum.rec (fun _ => Set.DefinableFun.proj JH)
      (fun _ => JH.definableFun_const I prim.residue_one) i
  have sep := SeparatedSets.preimage vals res (left' := A.Definable JG) (right' := B.Definable JH)
    (fun d => d.preimage_map hv) (fun d => d.preimage_map hr) h
  convert sep using 1
  ext z
  apply (congrArg (· ∈ U) _).to_iff
  funext i
  cases i with
  | inl i => exact (s.join_one _).symm
  | inr j =>
    change s.representative _ = s.join _ 1
    exact (congrArg (s.representative (z.1 j) * ·) (residueRV_one O)).trans (mul_one (M := RV0 O) _ ) |>.symm

end GeneralizedEuler.Section4
