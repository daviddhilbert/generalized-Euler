module

public import Section4.MeasurableCharts
public import Section4.CanonicalRectangles
import all Section4.SliceComparison
import all Section4.MeasurableCharts
import all Section4.CanonicalRectangles

/-! The canonical fixed-base cover by nonempty measurable charts, in the form
used to assign weights to positive definable objects and their graphs. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
private theorem select_cover {X : Type*} {l : ℕ} (D : Set X) (p : Fin l → Set X) (P : Fin l → Prop)
    (cover : ∀ x, x ∈ D ↔ ∃ i, x ∈ p i) (disj : Pairwise (fun i j => Disjoint (p i) (p j)))
    (active : ∀ i, (p i).Nonempty → P i) :
    ∃ (m : ℕ) (idx : Fin m → Fin l), (∀ j, P (idx j)) ∧
      Pairwise (fun i j => Disjoint (p (idx i)) (p (idx j))) ∧ (⋃ j, p (idx j)) = D := by
  classical
  let e := (Fintype.equivFin {i // P i}).symm
  refine ⟨_,fun j => (e j).val,fun j => (e j).property,fun i j ne => disj (fun h => ne (e.injective (Subtype.ext h))),?_⟩
  ext x
  rw [Set.mem_iUnion,cover]
  constructor
  · rintro ⟨j,h⟩; exact ⟨_,h⟩
  · rintro ⟨i,hi⟩
    let j : {i // P i} := ⟨i,active i ⟨x,hi⟩⟩
    refine ⟨e.symm j,?_⟩
    change x ∈ p (e (e.symm j)).val
    rw [e.apply_symm_apply]; exact hi

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
local instance chartCoverAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)


variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))

def AdmitsCharts {n : ℕ} (D : Set (Fin n → Additive (PositiveRV O))) :=
  ∃ (l : ℕ) (p : Fin l → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n),
    (∀ i, (p i).measurable O v hO P S) ∧ (∀ i, (p i).residue.Nonempty) ∧
    Pairwise (fun i j => Disjoint ((p i).carrier s) ((p j).carrier s)) ∧ (⋃ i, (p i).carrier s) = D

set_option maxHeartbeats 800000 in
include g agrees units clamp powers hv hs pull in
theorem canonical_admits_charts
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
    AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U) := by
  classical
  let lang : ValueLanguage (J := JG) G :=
    ⟨definableFun_of_graph primitives.value_mul,fun t => definableFun_of_graph (primitives.value_power t)⟩
  obtain ⟨l,p,cv,dj,supports,charts⟩ := canonical_rectangles v hv s hs G B hO P g agrees units clamp powers
    primitives S base qe sat U hu
  have meas := measurable_positive_charts O v s hs hO P powers S reps lang @pull U hu pos p supports charts
  let raw i := (p i).carrier (codeTuple O ⁻¹' U)
  have hit (i : Fin l) : (p i).asChart.carrier s = raw i := (p i).asChart_carrier s _ (charts i)
  have active (i : Fin l) (hi : (raw i).Nonempty) : (p i).residues.Nonempty := by
    obtain ⟨e,_⟩ := charts i
    let w := (e.symm ⟨hi.choose,hi.choose_spec⟩).2
    exact ⟨w.val,w.property⟩
  obtain ⟨m,idx,ne,disjoint,union⟩ := select_cover _ raw _ cv dj active
  have separate : Pairwise (fun i j => Disjoint ((p (idx i)).asChart.carrier s) ((p (idx j)).asChart.carrier s)) :=
    fun i j h => (congrArg₂ Disjoint (hit (idx i)) (hit (idx j))).mpr (disjoint h)
  have unions := (congrArg (fun sets : Fin m → Set (Fin n → Additive (PositiveRV O)) => ⋃ i, sets i) (funext fun j => hit (idx j))).trans union
  exact ⟨m,fun j => (p (idx j)).asChart,fun j => meas (idx j),ne,separate,unions⟩

end GeneralizedEuler.Section4
