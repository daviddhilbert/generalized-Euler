module

public import Section3.DiscRayQuotient
public import Section3.AtomicProfiles
public import Section2.ResidueMap
import all Section2.ValuativeDisc

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set
variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- The radius representative is allowed to move. If an automorphism
fixes the closed disc as a set, its scale nonetheless has the old value. -/
theorem scale_value_of_invariant_disc (e : K ≃+* K) (ring : RespectsValuationRing O O e.toRingHom)
    (a d : K) (dn : d ≠ 0)
    (fixed : e '' closedDisc O a (O.valuation d) = closedDisc O a (O.valuation d)) :
    O.valuation (e d) = O.valuation d := by
  have test (b v x : K) (vn : v ≠ 0) : x ∈ closedDisc O b (O.valuation v) ↔ (x-b)/v ∈ O := by
    rw [←O.valuation_le_one_iff,map_div₀,div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr vn))]
    rfl
  have mem (x : K) : e x ∈ closedDisc O (e a) (O.valuation (e d)) ↔ x ∈ closedDisc O a (O.valuation d) := by
    rw [test _ _ _ ((map_ne_zero _).mpr dn),test _ _ _ dn,←map_sub,←map_div₀]
    exact ring _
  have eqn : closedDisc O (e a) (O.valuation (e d)) = closedDisc O a (O.valuation d) := by
    rw [←fixed]
    ext x
    obtain ⟨x,rfl⟩ := e.surjective x
    exact (mem x).trans e.injective.mem_set_image.symm
  have hcen : e a ∈ closedDisc O a (O.valuation d) := eqn ▸ mem_closedDisc_center O _ _
  rw [←closedDisc_change_center O hcen] at eqn
  exact le_antisymm ((closedDisc_subset_iff_radius O).mp eqn.subset)
    ((closedDisc_subset_iff_radius O).mp eqn.symm.subset)

/-- Formula for an automorphism on the affine line of maximal children.
The translation is the label of the transformed origin. Its linear part
is the residue of the ratio of the transformed and original scales. -/
theorem semilinear_child_label (e : K ≃+* K) (ring : RespectsValuationRing O O e.toRingHom)
    (a d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (fixed : e '' closedDisc O a r = closedDisc O a r) :
    ∃ α β : Residue O, β ≠ 0 ∧ (e a ∈ openDisc O a r → α = 0) ∧
      ∀ x : closedDisc O a r, let hx := fixed.subset (mem_image_of_mem e x.property)
        childLabel O a d hr hd ⟨e x.val,hx⟩ = α+β*mapResidue O O e.toRingHom ring (childLabel O a d hr hd x) := by
  have dn : d ≠ 0 := (map_ne_zero _).mp (hd.trans_ne hr)
  have ed := (scale_value_of_invariant_disc O e ring a d dn (hd.symm ▸ fixed)).trans hd
  have center := mem_closedDisc_center O r a
  let ea : closedDisc O a r := ⟨e a,fixed.subset (mem_image_of_mem e center)⟩
  let u := discChartScale O (e d) d hr ed hd
  refine ⟨childLabel O a d hr hd ea,IsLocalRing.residue O u,discChartScale_residue_ne_zero O _ _ hr ed hd,
    (discChildrenChart_eq_zero_iff O a d hr hd ea).mpr,?_⟩
  intro x hx
  change IsLocalRing.residue O (normalizedPoint O a d hr hd ⟨e x.val,hx⟩) =
    IsLocalRing.residue O (normalizedPoint O a d hr hd ea) +
    IsLocalRing.residue O u * mapResidue O O e.toRingHom ring (IsLocalRing.residue O (normalizedPoint O a d hr hd x))
  rw [mapResidue_residue,←map_mul,←map_add]
  congr 1
  apply Subtype.ext
  change (e x.val-a)/d = (e a-a)/d + (e d/d)*e ((x.val-a)/d)
  rw [map_div₀,map_sub]
  field_simp [dn,(map_ne_zero e).mpr dn]
  ring

/-- The induced map on residue fields is an ordered-field automorphism. -/
@[expose] noncomputable def residueFieldEquiv (e : K ≃+* K) (ring : RespectsValuationRing O O e.toRingHom) :
    Residue O ≃+* Residue O :=
  RingEquiv.ofBijective (mapResidue O O e.toRingHom ring) ⟨(mapResidue O O e.toRingHom ring).injective,by
    intro y
    obtain ⟨z,rfl⟩ := IsLocalRing.residue_surjective y
    let w : O := ⟨e.symm z,(ring _).mp (by simp)⟩
    refine ⟨IsLocalRing.residue O w,?_⟩
    rw [mapResidue_residue]
    congr 1
    exact Subtype.ext (e.apply_symm_apply z)⟩

theorem residueFieldEquiv_apply (e : K ≃+* K) (ring : RespectsValuationRing O O e.toRingHom)
    (r : Residue O) : residueFieldEquiv O e ring r = mapResidue O O e.toRingHom ring r := rfl

end GeneralizedEuler.Section3
