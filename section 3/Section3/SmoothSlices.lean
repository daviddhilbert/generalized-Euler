module

public import Section3.ReducedJets
public import Section2.ResidueTopology
import all Section2.ResidueTopology
import all Section3.NormalizedSlice
import all Section3.SliceExceptions
import all Section2.TorsorDerivative

public section

namespace GeneralizedEuler.Section3

open Set Filter GeneralizedEuler.Section2
open scoped Topology

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [TopologicalSpace k] [OrderTopology k]

private theorem interval_around {U : Set k} (hU : IsOpen U) {r : k} (hr : r ∈ U) :
    ∃ δ > 0, ∀ h : k, |h| < δ → r+h ∈ U := by
  obtain ⟨a,b,⟨ha,hb⟩,sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hr)
  refine ⟨min (r-a) (b-r),lt_min (sub_pos.mpr ha) (sub_pos.mpr hb),fun h hh => sub ?_⟩
  obtain ⟨l,u⟩ := lt_min_iff.mp hh
  exact ⟨by linarith [(abs_lt.mp l).1],by linarith [(abs_lt.mp u).2]⟩

/-- On an open residue interval a finite exceptional set cannot separate
two continuous derivatives, including over a non-Archimedean field. -/
theorem equal_on_open_of_finite_disagreement {U : Set k} (hU : IsOpen U) {f g : k → k}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (bad : {x ∈ U | f x ≠ g x}.Finite) :
    EqOn f g U := by
  intro r hr
  by_contra hn
  have diff : ∀ᶠ t in 𝓝 r, f t ≠ g t :=
    (((hf r hr).continuousAt (hU.mem_nhds hr)).ne_iff_eventually_ne ((hg r hr).continuousAt (hU.mem_nhds hr))).mp hn
  have nh := Filter.inter_mem (hU.mem_nhds hr) diff
  obtain ⟨a,b,⟨ha,hb⟩,sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp nh
  exact Ioo_infinite (ha.trans hb) (bad.subset sub)

variable {X : Type*}

omit [Field k] [IsStrictOrderedRing k] in
theorem isOpen_twoSidedLabels (p : X → k) (B : Set X) : IsOpen (twoSidedLabels p B) := by
  have eqn : twoSidedLabels p B = (⋃ a ∈ B, Ioi (p a)) ∩ (⋃ b ∈ B, Iio (p b)) := by
    ext r
    simp [twoSidedLabels]
  rw [eqn]
  exact (isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_Ioi))).inter
    (isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_Iio)))

variable {K I : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
    (hO : IsOrderConvex O)

/-- On a nonzero constant-value chart of 3.31, the finitely many
endpoints from 3.30 cause no failure when the two given contractions
are smooth. Compare their derivatives away from those endpoints and
then use continuity on the entire open slice. This argument works for
each field-parameter slice independently. -/
theorem smooth_normalized_slice [Finite I] (g d : O → K) (c : K) (U : Set (Residue O))
    (B : I → Set O) (G D : Residue O → Residue O)
    (Dcontract : ∀ x, IsLocalRing.residue O x ∈ U → ∃ z : O, (z : K) = g x/c ∧
      IsLocalRing.residue O z = G (IsLocalRing.residue O x))
    (fieldValue : ∀ x y : O, IsLocalRing.residue O x ∈ U → IsLocalRing.residue O y ∈ U →
      O.valuation (d x / c) = O.valuation (d y / c))
    (cover : (IsLocalRing.residue O) ⁻¹' U ⊆ ⋃ i, B i) (convex : ∀ i, (B i).OrdConnected)
    (branch : ∀ i, Nonempty (ResidueBranch O hO (B i) g d c)) :
    letI := residueLinearOrder O hO
    letI := residueOrderTopology O hO
    IsOpen U → ContinuousOn D U → (∀ r ∈ U, HasOrderDerivativeAt G r (D r)) →
    ((∀ x : O, IsLocalRing.residue O x ∈ U → d x/c ∈ O) →
      ∃ H : Residue O → Residue O, ContinuousOn H U ∧ ∀ (x z : O), IsLocalRing.residue O x ∈ U →
        (z : K) = d x/c → H (IsLocalRing.residue O x) = IsLocalRing.residue O z) →
    ∀ r ∈ U, NormalizedSliceAt O hO ((IsLocalRing.residue O) ⁻¹' U) g d c r := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := residueOrderTopology O hO
  let : OrderTopology (Residue O) := ⟨rfl⟩
  intro hU cont deriv chart
  let p := IsLocalRing.residue O
  let V i := twoSidedLabels p (B i)
  have fin : (U \ ⋃ i, V i).Finite := by
    have heq : p '' (p ⁻¹' U) = U := (IsLocalRing.residue_surjective).image_preimage U
    rw [←heq]
    exact finite_labels_outside_branches p B cover
  intro r hr
  obtain ⟨a,b,⟨ha,hb⟩,sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hr)
  have good : ∃ t ∈ U, ∃ i, t ∈ V i := by
    by_contra! none
    exact Ioo_infinite (ha.trans hb) (fin.subset (fun w hw => ⟨sub hw,fun h => by
      obtain ⟨i,hi⟩ := mem_iUnion.mp h; exact none w (sub hw) i hi⟩))
  obtain ⟨t,ht,i,hi⟩ := good
  obtain ⟨x,hx⟩ := IsLocalRing.residue_surjective t
  have nt := normalizedSlice_in_branch O hO (convex i) (branch i).some t hi
  obtain ⟨_,_,atX⟩ := nt
  obtain ⟨z,hz,_⟩ := atX x (show p x ∈ V i from hx.symm ▸ hi) hx
  have integral (y : O) (hy : p y ∈ U) : d y/c ∈ O := by
    rw [←O.valuation_le_one_iff,fieldValue y x hy (hx.symm ▸ ht),←hz]
    exact O.valuation_le_one z
  obtain ⟨H,hH,mapH⟩ := chart integral
  have equal : EqOn D H U := by
    apply equal_on_open_of_finite_disagreement hU cont hH
    apply fin.subset
    rintro u ⟨hu,ne⟩
    refine ⟨hu,fun inside => ?_⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp inside
    obtain ⟨J,hJ,slope⟩ := normalizedSlice_in_branch O hO (convex j) (branch j).some u hj
    obtain ⟨y,hy⟩ := IsLocalRing.residue_surjective u
    obtain ⟨q,hq,delta⟩ := slope y (show p y ∈ V j from hy.symm ▸ hj) hy
    have hOpen := hU.inter (isOpen_twoSidedLabels p (B j))
    obtain ⟨δ,hδ,near⟩ := interval_around hOpen (show u ∈ U ∩ V j from ⟨hu,hj⟩)
    have corrected := derivative_of_agreement_near (H := G) delta hδ (by
      intro t ht
      obtain ⟨a,ha⟩ := IsLocalRing.residue_surjective (u+t)
      have inU := ha.symm ▸ (near t ht).1
      have inV := ha.symm ▸ (near t ht).2
      obtain ⟨l,hl,eqL⟩ := hJ a inV
      obtain ⟨m,hm,eqM⟩ := Dcontract a inU
      have eql : l = m := Subtype.ext (hl.trans hm.symm)
      rw [←ha,←eqL,←eqM,eql])
    exact ne (((deriv u hu).unique corrected).trans (hy ▸ (mapH y q (hy.symm ▸ hu) hq).symm))
  refine ⟨G,fun x hx => Dcontract _ hx,fun x hx he => ?_⟩
  let q : O := ⟨d x/c,integral x hx⟩
  exact ⟨q,rfl,by rw [←mapH x q hx rfl,he,←equal hr]; exact deriv r hr⟩


/-- Apply the preceding result directly to the field MVT on the finitely
many convex branches of the unary restriction. Integrality of the
normalized derivative and both residue branch functions are constructed
in the proof. In particular no definable selection of slice exceptions or
of representatives of the output value is needed. -/
theorem smooth_slice_of_piecewise_mean_value [Finite I] (g d : O → K) (c : K)
    (U : Set (Residue O)) (B : I → Set O) (G D : Residue O → Residue O)
    (contr : ∀ x, IsLocalRing.residue O x ∈ U → ∃ z : O, (z : K) = g x/c ∧
      IsLocalRing.residue O z = G (IsLocalRing.residue O x))
    (fieldValue : ∀ x y : O, IsLocalRing.residue O x ∈ U → IsLocalRing.residue O y ∈ U →
      O.valuation (d x/c) = O.valuation (d y/c))
    (cover : (IsLocalRing.residue O) ⁻¹' U = ⋃ i, B i) (convex : ∀ i, (B i).OrdConnected)
    (mvt : ∀ i x, x ∈ B i → ∀ y ∈ B i, IsLocalRing.residue O x ≠ IsLocalRing.residue O y →
      ∃ z ∈ uIcc x y, g y-g x = ((y : K)-x)*d z) :
    letI := residueLinearOrder O hO
    letI := residueOrderTopology O hO
    IsOpen U → ContinuousOn D U → (∀ r ∈ U, HasOrderDerivativeAt G r (D r)) →
    ((∀ x : O, IsLocalRing.residue O x ∈ U → d x/c ∈ O) →
      ∃ H : Residue O → Residue O, ContinuousOn H U ∧ ∀ (x z : O), IsLocalRing.residue O x ∈ U →
        (z : K) = d x/c → H (IsLocalRing.residue O x) = IsLocalRing.residue O z) →
    ∀ r ∈ U, NormalizedSliceAt O hO ((IsLocalRing.residue O) ⁻¹' U) g d c r := by
  classical
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := residueOrderTopology O hO
  let : OrderTopology (Residue O) := ⟨rfl⟩
  intro hU hD der chart r hr
  let p := IsLocalRing.residue O
  let A := p ⁻¹' U
  have sub (i : I) : B i ⊆ A := fun x hx => cover.symm.subset (mem_iUnion_of_mem i hx)
  let f (x : O) : O := if h : x ∈ A then (contr x h).choose else 0
  have fx (x : O) (hx : x ∈ A) : (f x : K) = g x/c ∧ p (f x) = G (p x) := by
    simpa only [f,dite_eq_left hx] using (contr x hx).choose_spec
  have secant (i : I) {x y : O} (hx : x ∈ B i) (hy : y ∈ B i) (ne : p x ≠ p y) :
      ∃ z ∈ uIcc x y, (f y : K)-f x = ((y : K)-x)*(d z/c) := by
    obtain ⟨z,hz,he⟩ := mvt i x hx y hy ne
    refine ⟨z,hz,?_⟩
    rw [(fx _ (sub i hy)).1,(fx _ (sub i hx)).1,←sub_div,he,mul_div_assoc]
  have pair : ∃ i, (p '' B i).Nontrivial := by
    by_contra! h
    have fin := finite_iUnion (fun i => (h i).finite)
    have whole : U = ⋃ i, p '' B i := by
      rw [←image_iUnion,←cover,(IsLocalRing.residue_surjective).image_preimage]
    obtain ⟨a,b,⟨ha,hb⟩,inside⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hr)
    exact Ioo_infinite (ha.trans hb) ((whole.symm ▸ fin : U.Finite).subset inside)
  obtain ⟨i,_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hne⟩ := pair
  obtain ⟨z,hz,he⟩ := secant i hx hy hne
  have hzA := sub i ((convex i).uIcc_subset hx hy hz)
  have integ (x : O) (hx : x ∈ A) : d x/c ∈ O := by
    rw [←O.valuation_le_one_iff,fieldValue x z hx hzA,O.valuation_le_one_iff]
    exact integral_of_mean_value O hne he
  let d' (x : O) : O := if h : x ∈ A then ⟨d x/c,integ x h⟩ else 0
  have dx (x : O) (hx : x ∈ A) : (d' x : K) = d x/c := by simp only [d',dite_eq_left hx]
  obtain ⟨H,continu,red⟩ := chart integ
  apply smooth_normalized_slice O hO g d c U B G D contr fieldValue cover.subset convex _ hU hD der chart r hr
  intro i
  refine ⟨⟨f,d',fun x hx => (fx _ (sub i hx)).1,fun x hx => dx _ (sub i hx),G,H,
    fun x hx => (fx _ (sub i hx)).2,fun x hx => (red _ _ (sub i hx) (dx _ (sub i hx))).symm,?_,?_⟩⟩
  · dsimp only
    intro t ht eps hp
    obtain ⟨a,ha⟩ := IsLocalRing.residue_surjective t
    have tU : t ∈ U := ha ▸ (sub i (preimage_twoSidedLabels_subset (residue_monotone O hO) (convex i)
      (show p a ∈ twoSidedLabels p (B i) from ha.symm ▸ ht)) : p a ∈ U)
    have near := (continu t tU).continuousAt (hU.mem_nhds tU) |>.preimage_mem_nhds
      (Ioo_mem_nhds (sub_lt_self _ hp) (lt_add_of_pos_right _ hp))
    obtain ⟨l,u,⟨lo,hi⟩,ins⟩ := mem_nhds_iff_exists_Ioo_subset.mp near
    refine ⟨min (t-l) (u-t),lt_min (sub_pos.mpr lo) (sub_pos.mpr hi),fun w _ hw => ?_⟩
    obtain ⟨ll,uu⟩ := lt_min_iff.mp hw
    have hm : H w ∈ Ioo (H t-eps) (H t+eps) := ins
      ⟨by linarith [(abs_lt.mp ll).1],by linarith [(abs_lt.mp uu).2]⟩
    exact abs_lt.mpr ⟨by linarith [hm.1],by linarith [hm.2]⟩
  · intro a ha b hb hn
    obtain ⟨z,hz,he⟩ := secant i ha hb hn
    exact ⟨z,hz,by rw [dx _ (sub i ((convex i).uIcc_subset ha hb hz))]; exact he⟩

end GeneralizedEuler.Section3
