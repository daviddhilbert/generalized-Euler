module

public import Section3.SmoothSlices
import all Section3.SmoothSlices
import all Section3.NormalizedSlice
import all Section2.Residue
import all Section2.ResidueTopology
import all Section2.TorsorDerivative

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set Filter
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
    (hO : IsOrderConvex O)

noncomputable def scaledResidue (R : RV0 O) (c : K) := rvResidue O (R / rv O c)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem scaledResidue_of_rv (a c : K) : scaledResidue O (rv O a) c = totalResidue O (a/c) := by
  rw [scaledResidue,←map_div₀ (G₀ := K) (G₀' := RV0 O) (rv O),rvResidue_rv]

/-- Statement of the adjacent comparison at a representative on an
open residue slice. Both contractions in the conclusion are the actual
RV and residue functions given on that slice. -/
def AdjacentComparison (g d : O → K) (G : Residue O → RV0 O) (x : O) : Prop :=
  letI := residueLinearOrder O hO
  let r := IsLocalRing.residue O x
  O.valuation (d x) ≤ O.valuation (g x) ∧
    (∀ c : K, c ≠ 0 → O.valuation c = O.valuation (g x) →
      (¬ (d x = 0 ∨ O.valuation (d x) < O.valuation (g x)) ↔
        ∃ s : Residue O, s ≠ 0 ∧ HasOrderDerivativeAt (fun t => scaledResidue O (G t) c) r s ∧
          rv O (d x) = rv O c * residueRV O s)) ∧
    (g x ∈ O → d x ∈ O ∧ HasOrderDerivativeAt (fun t => rvResidue O (G t)) r (totalResidue O (d x)))

/-- All field inputs on the indicated interval have one unsigned value.
This is the unary restriction of the open value locus. -/
def SingleSliceValue (U : Set (Residue O)) (g : O → K) :=
  ∀ x y : O, IsLocalRing.residue O x ∈ U → IsLocalRing.residue O y ∈ U → O.valuation (g x) = O.valuation (g y)

def PiecewiseSliceMVT (U : Set (Residue O)) (g d : O → K) :=
  ∃ (m : ℕ) (B : Fin m → Set O), (IsLocalRing.residue O) ⁻¹' U = ⋃ i, B i ∧ (∀ i, (B i).OrdConnected) ∧
    ∀ i x, x ∈ B i → ∀ y ∈ B i, IsLocalRing.residue O x ≠ IsLocalRing.residue O y →
      ∃ z ∈ uIcc x y, g y-g x = ((y : K)-x)*d z

/-- C¹ of a given RV contraction on a fixed nonzero output-value chart,
spelled out in residue coordinates for any choice of scale. -/
def SmoothSliceChart (U : Set (Residue O)) (g : O → K) (G : Residue O → RV0 O) : Prop :=
  letI := residueLinearOrder O hO
  letI := residueOrderTopology O hO
  ∀ c : K, c ≠ 0 → (∀ x : O, IsLocalRing.residue O x ∈ U → O.valuation (g x) = O.valuation c) →
    ContinuousOn (fun t => scaledResidue O (G t) c) U ∧ ∃ D : Residue O → Residue O, ContinuousOn D U ∧
      ∀ r ∈ U, HasOrderDerivativeAt (fun t => scaledResidue O (G t) c) r (D r)

private theorem zero_on_slice {U : Set (Residue O)} {g d : O → K}
    (constD : SingleSliceValue O U d) (pieces : PiecewiseSliceMVT O U g d)
    (zero : ∀ x : O, IsLocalRing.residue O x ∈ U → g x = 0) :
    letI := residueOrderTopology O hO
    IsOpen U → ∀ x : O, IsLocalRing.residue O x ∈ U → d x = 0 := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := residueOrderTopology O hO
  let : OrderTopology (Residue O) := ⟨rfl⟩
  intro hU x hx
  obtain ⟨m,B,cover,convex,mvt⟩ := pieces
  let p := IsLocalRing.residue O
  have inside i : B i ⊆ p ⁻¹' U := fun y hy => cover.symm.subset (mem_iUnion_of_mem i hy)
  have pair : ∃ i, (p '' B i).Nontrivial := by
    by_contra! h
    have finite := finite_iUnion (fun i => (h i).finite)
    have eqn : U = ⋃ i, p '' B i := by rw [←image_iUnion,←cover,(IsLocalRing.residue_surjective).image_preimage]
    obtain ⟨a,b,⟨ha,hb⟩,sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
    exact Ioo_infinite (ha.trans hb) ((eqn.symm ▸ finite : U.Finite).subset sub)
  obtain ⟨i,_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hne⟩ := pair
  obtain ⟨z,hz,sec⟩ := mvt i a ha b hb hne
  rw [zero a (inside i ha),zero b (inside i hb),sub_zero] at sec
  have dz := (mul_eq_zero.mp sec.symm).resolve_left (sub_ne_zero.mpr (fun h => hne.symm (congrArg p (Subtype.ext h))))
  apply (map_eq_zero O.valuation).mp
  rw [constD x z hx (inside i ((convex i).uIcc_subset ha hb hz)),dz,map_zero]

/-- Local theorem for 3.31, including the identically zero chart. The
pure field MVT on the branches and C¹ of the two given RV contractions
give both alternatives and the unconditional residue derivative. -/
theorem adjacent_comparison_on_slice {U : Set (Residue O)} (g d : O → K) (G H : Residue O → RV0 O)
    (cg : ∀ x : O, IsLocalRing.residue O x ∈ U → rv O (g x) = G (IsLocalRing.residue O x))
    (cd : ∀ x : O, IsLocalRing.residue O x ∈ U → rv O (d x) = H (IsLocalRing.residue O x))
    (vg : SingleSliceValue O U g) (vd : SingleSliceValue O U d) (mvt : PiecewiseSliceMVT O U g d)
    (smoothG : SmoothSliceChart O hO U g G) (smoothH : SmoothSliceChart O hO U d H) :
    letI := residueOrderTopology O hO
    IsOpen U → ∀ x : O, IsLocalRing.residue O x ∈ U → AdjacentComparison O hO g d G x := by
  classical
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := residueOrderTopology O hO
  let : OrderTopology (Residue O) := ⟨rfl⟩
  intro hU x hx
  let p := IsLocalRing.residue O
  let A := p ⁻¹' U
  have around := interval_around hU hx
  have fill (r : Residue O) (hr : r ∈ U) : ∃ y ∈ A, p y = r := by
    obtain ⟨y,hy⟩ := IsLocalRing.residue_surjective r
    exact ⟨y,show p y ∈ U from hy.symm ▸ hr,hy⟩
  by_cases gz : g x = 0
  · have allZero (y : O) (hy : y ∈ A) : g y = 0 := (map_eq_zero O.valuation).mp
        ((vg y x hy hx).trans (by rw [gz,map_zero]))
    have dx := zero_on_slice O hO vd mvt allZero hU x hx
    refine ⟨by simp [gz,dx],fun c cn eqn => False.elim (cn ((map_eq_zero O.valuation).mp (by simpa [gz] using eqn))),?_⟩
    intro _
    refine ⟨dx ▸ O.zero_mem,?_⟩
    have raw : HasOrderDerivativeAt (fun _ : Residue O => 0) (p x) 0 := by
      intro eps hp; exact ⟨1,one_pos,fun h _ _ => by simpa using hp⟩
    obtain ⟨δ,pos,near⟩ := around
    have ht : totalResidue O (d x) = 0 := by rw [dx,totalResidue_of_mem O O.zero_mem]; exact map_zero _
    rw [ht]
    apply derivative_of_agreement_near raw pos
    intro t lt
    obtain ⟨y,hy,he⟩ := fill _ (near t lt)
    rw [←he,←cg y hy,allZero y hy,rvResidue_rv,totalResidue_of_mem O O.zero_mem]
    exact (map_zero _).symm
  have normalized (c : K) (cn : c ≠ 0) (hv : O.valuation c = O.valuation (g x)) :
      NormalizedSliceAt O hO A g d c (p x) := by
    have gval (y : O) (hy : y ∈ A) := (vg y x hy hx).trans hv.symm
    obtain ⟨_,D,cont,der⟩ := smoothG c cn gval
    obtain ⟨m,B,cover,bconv,mv⟩ := mvt
    apply smooth_slice_of_piecewise_mean_value O hO g d c U B (fun t => scaledResidue O (G t) c) D _ _ cover bconv mv hU cont der _ _ hx
    · intro y hy
      have inO : g y/c ∈ O := by rw [←O.valuation_le_one_iff,map_div₀,gval y hy,div_self ((map_ne_zero O.valuation).mpr cn)]
      refine ⟨⟨_,inO⟩,rfl,?_⟩
      rw [←cg y hy,scaledResidue_of_rv,totalResidue_of_mem O inO]
    · intro y z hy hz; rw [map_div₀,map_div₀,vd y z hy hz]
    · intro integ
      have valLe : O.valuation (d x) ≤ O.valuation c :=
        (div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr cn))).mp (by
          rw [←map_div₀]; exact (O.valuation_le_one_iff _).mpr (integ x hx))
      rcases valLe.eq_or_lt with eqn | lt
      · refine ⟨fun t => scaledResidue O (H t) c,(smoothH c cn (fun y hy => (vd y x hy hx).trans eqn)).1,?_⟩
        intro y z hy hz
        change scaledResidue O (H (IsLocalRing.residue O y)) c = _
        rw [←cd y hy,scaledResidue_of_rv,←hz,totalResidue_of_mem O z.property]
      · refine ⟨fun _ => 0,continuousOn_const,?_⟩
        intro y z hy hz
        symm
        apply not_ne_iff.mp
        intro hn
        have one := (residue_ne_zero_iff_value_one O z).mp hn
        rw [hz,map_div₀,div_eq_one_iff_eq ((map_ne_zero O.valuation).mpr cn),vd y x hy hx] at one
        exact lt.ne one
  have extract (c : K) (cn : c ≠ 0) (hv : O.valuation c = O.valuation (g x)) :=
    normalized_jet_alternatives O hO g d cn (fun y (hy : y ∈ A) => (vg y x hy hx).trans hv.symm)
      (p x) (normalized c cn hv)
  obtain ⟨_,_,out⟩ := extract (g x) gz rfl
  refine ⟨(out x hx rfl).1,?_,?_⟩
  · intro c cn hv
    obtain ⟨J,ag,alt⟩ := extract c cn hv
    obtain ⟨δ,positive,near⟩ := around
    have agree (t : Residue O) (ht : |t| < δ) : J (p x+t) = scaledResidue O (G (p x+t)) c := by
      obtain ⟨y,hy,he⟩ := fill _ (near t ht)
      obtain ⟨z,hz,hj⟩ := ag y hy
      rw [←he,←cg y hy,scaledResidue_of_rv,←hz,totalResidue_of_mem O z.property,←hj]
    apply (alt x hx rfl).2.2.trans
    apply exists_congr; intro s
    exact and_congr_right (fun _ => and_congr ⟨fun H => derivative_of_agreement_near H positive agree,
      fun H => derivative_of_agreement_near H positive (fun t ht => (agree t ht).symm)⟩ Iff.rfl)
  · intro gxO
    let g' (y : O) : O := if hy : y ∈ A then ⟨g y,(O.valuation_le_one_iff _).mp
      ((vg y x hy hx).trans_le ((O.valuation_le_one_iff _).mpr gxO))⟩ else 0
    have ge (y : O) (hy : y ∈ A) : (g' y : K) = g y := by simp only [g',dite_eq_left hy]
    let c : O := ⟨g x,gxO⟩
    obtain ⟨J,hJ,test⟩ := normalized (g x) gz rfl
    have good : NormalizedSliceAt O hO A (fun y => (g' y : K)) d c (p x) :=
      ⟨J,fun y hy => by dsimp only; rw [ge y hy]; exact hJ y hy,test⟩
    have contr (y : O) (hy : y ∈ A) : p (g' y) = rvResidue O (G (p y)) := by
      rw [←cg y hy,←ge y hy,rvResidue_rv,totalResidue_of_mem O (g' y).property]
    obtain ⟨δ,pos,near⟩ := around
    obtain ⟨w,hw,der⟩ := reduce_adjacent_jet O hO g' d c gz (fun t => rvResidue O (G t)) (p x)
      contr good ⟨δ,pos,fun t ht => fill _ (near t ht)⟩ x hx rfl
    exact ⟨hw ▸ w.property,by rw [←hw,totalResidue_of_mem O w.property]; exact der⟩

end GeneralizedEuler.Section3
