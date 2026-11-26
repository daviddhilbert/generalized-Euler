module

public import Section4.SignedShears
public import Section4.RectangleDecomposition
public import Section4.DefinableValueFrames
public import Section2.RVCoordinatePrimitives
import all Section4.SignedShears
import all Section2.RVSplitCoordinates
import all Section2.RVCoordinatePrimitives

/-! Apply the finite rectangle construction to the actual canonical two-sorted
structure, using the fixed-base RV formula of Section 2. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))

def kernelResidue (t : v.ker) : Residue O := rvResidue O (positiveRVToRV0 O t.val.toMul)

theorem kernelResidue_join (γ : Additive O.ValueGroupˣ) (t : v.ker) :
    (linearValueSection v hv s hs).join γ.toMul (kernelResidue v t) =
      positiveRVToRV0 O (s γ + t.val).toMul := by
  have unit : unsignedValue O (positiveRVToRV0 O t.val.toMul) = 1 := by
    rw [← positiveValueMap_coe]
    have h : v t.val = 0 := t.property
    rw [hv] at h
    exact congrArg (fun a : Additive O.ValueGroupˣ => (a.toMul : O.ValueGroup)) h
  have inRange : positiveRVToRV0 O t.val.toMul ∈ Set.range (residueRV O) := by
    rw [range_residueRV]; exact Or.inr unit
  change positiveRVToRV0 O (s γ).toMul * residueRV O (rvResidue O _) = _
  rw [residueRV_rvResidue_of_mem_range O inRange]
  exact (positiveRVToRV0_mul O _ _).symm

variable {J JG JH : Language} [J.Structure K] [J.Structure (Residue O)]
  [JG.Structure O.ValueGroupˣ] [JH.Structure (Residue O)] (B : Set (Residue O))
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K)
  (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul =
    P e (positiveRVToRV0 O x.toMul))

def residuePullback {n} (U : Set (Fin n → v.ker)) : Prop :=
  ∃ R : Set (Fin n → Residue O), B.Definable JH R ∧ U = (fun t => kernelResidue v ∘ t) ⁻¹' R

local instance additiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

include g agrees units clamp powers in
theorem canonical_rectangles {n}
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
      (fun e γ => (e • Additive.ofMul γ).toMul) P)
    (C : SortedSubstructure (canonicalStructure (L := J) O hO P))
    (base : ∀ t : C.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ (G : Set (Additive O.ValueGroupˣ)) ∧
      ((linearValueSection v hv s hs).encode t.val).2 ∈ B)
    (qe : ∀ φ : SortedFormula J F (FullRVVariables C (Fin n)), ∃ q : SortedFormula J F (FullRVVariables C (Fin n)), q.IsQF ∧
      ∀ x, q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)
    (sat : ∀ m (Δ : Set (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m))),
      (∀ t : Finset (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m)), (↑t : Set _) ⊆ Δ → ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ Δ, φ.Realize x)
    (U : Set (Fin n → RV0 O)) (hU : isRVSet _ C U) :
    let D := {x : Fin n → Additive (PositiveRV O) | (fun i => positiveRVToRV0 O (x i).toMul) ∈ U}
    ∃ (l : ℕ) (p : Fin l → PositivePiece v G (fun _ A => (G : Set (Additive O.ValueGroupˣ)).Definable JG A)
        (residuePullback (JH := JH) v B)),
      (∀ x, x ∈ D ↔ ∃ i, x ∈ (p i).carrier D) ∧
      Pairwise (fun i j => Disjoint ((p i).carrier D) ((p j).carrier D)) ∧
      (∀ γ, ∃! i, γ ∈ (p i).value.support) ∧
      ∀ i, ∃ e : (p i).rectangle ≃ (p i).carrier D, ∀ z,
        (e z).val = (p i).value.frame.assemble v s z.1.val z.2.val := by
  classical
  let D := {x : Fin n → Additive (PositiveRV O) | (fun i => positiveRVToRV0 O (x i).toMul) ∈ U}
  let old := linearValueSection v hv s hs
  let p (e : F) (γ : O.ValueGroupˣ) := (e • Additive.ofMul γ).toMul
  have hpow (e γ) : P e (old.representative γ) = old.representative (p e γ) :=
    (powers e _).symm.trans (congrArg (fun t : Additive (PositiveRV O) => positiveRVToRV0 O t.toMul)
      (s.map_smul e _).symm)
  let pos := old.canonicalCoordinatePresentation primitives g agrees clamp units hpow
  have sep := pos.separated_rv_pullback C hU qe base (old.separated_decoded_coordinate_graph primitives)
  let Q := residuePullback (n := n) (JH := JH) v B
  have separated := SeparatedSets.preimage (id : (Fin n → Additive O.ValueGroupˣ) → _)
    (fun t : Fin n → v.ker => kernelResidue v ∘ t) (left' := fun D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D) (fun h => h)
    (right' := Q) (fun h => ⟨_,h,rfl⟩) sep
  have valLang : ValueLanguage (J := JG) G :=
    ⟨definableFun_of_graph primitives.value_mul,fun e => definableFun_of_graph (primitives.value_power e)⟩
  apply decompose_positive_set v s hs G _ Q D _ _ Set.definable_univ (fun a b => a.inter b)
    (fun a => a.compl) _ _ (fun p D i h => valLang.cut p D i h) (valLang.avoidance sat)
  · intro l x hx
    let f := signedShear v hv s hs G l
    have fixed (t : C.carrier .rv) : f t.val = t.val := signedShear_base v hv s hs G l _ (base t).1
    have h := ((signedShear_reduct (J := J) v hv s hs G l hO g P agrees units clamp powers).setInvariant
      C fixed qe hU (fun i => positiveRVToRV0 O (x i).toMul)).mpr hx
    convert h using 1
    exact (congrArg (· ∈ U) (funext fun i => (signedShear_positive v hv s hs G l (x i)).symm)).to_iff
  · convert separated using 1
    ext x
    change (fun i => positiveRVToRV0 O (s (x.1 i) + (x.2 i).val).toMul) ∈ U ↔
      (fun i => old.join (x.1 i).toMul (kernelResidue v (x.2 i))) ∈ U
    exact (congrArg (· ∈ U) (funext fun i => (kernelResidue_join v hv s hs (x.1 i) (x.2 i)).symm)).to_iff
  · exact ⟨∅,Set.definable_empty,rfl⟩
  · rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩; exact ⟨_,ha.union hb,rfl⟩

end GeneralizedEuler.Section4
