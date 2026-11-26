module

public import Section5.PositioningDistance

/-! A positioning branch on a disc is a product when its image radius
is small enough. Otherwise the opposite paradigm gives the balanced
product form, including the graph case at zero. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem constant_positioned_cell_product (A : Set K) (f : K → K) (b : K) (t : RV0 O)
    (constant : ∀ x ∈ A, f x = b) :
    positionedCell O A f t = A ×ˢ {y | rv O (y-b) = t} := by
  ext p
  change (p.1 ∈ A ∧ rv O (p.2 - f p.1) = t) ↔ (p.1 ∈ A ∧ rv O (p.2-b) = t)
  exact and_congr_right (fun h => by rw [constant p.1 h])

/-- For the affine disc chart, the radius test yields exactly the
two nonconstant forms of a positioned cell. -/
theorem classify_affine_positioned_disc
    (a b : K) (r s : O.ValueGroup) (hr : r ≠ 0) (hs : s ≠ 0)
    {f g : K → K} (t : RV0 O) (u : RV O)
    (affine : RVAffineOn O (openDisc O a r) f u)
    (dtd : DiscToDiscOn O (openDisc O a r) (openDisc O b s) f g) :
    let A := openDisc O a r
    let B := openDisc O b s
    let C := positionedCell O A f t
    (s ≤ unsignedValue O t ∧ t ≠ 0 ∧ ∃ c, C = A ×ˢ openDisc O c (unsignedValue O t)) ∨
      (unsignedValue O (oppositeParadigm O t u) < r ∧
        (∀ p ∈ C, p.2 ∈ B) ∧
        (∀ y ∈ B, g y ∈ A ∧ f (g y) = y) ∧
        (fun p : K × K => (p.1 - g p.2,p.2)) '' C = (rv O ⁻¹' {oppositeParadigm O t u}) ×ˢ B) := by
  intro A B C
  have image : f '' A = B := dtd.1.image_eq
  by_cases large : s ≤ unsignedValue O t
  · have ht : t ≠ 0 := by
      intro hz
      have hs' : s ≤ 0 := by simpa only [hz,map_zero] using large
      exact hs (le_antisymm hs' zero_le)
    have inside : a ∈ A := mem_openDisc_center O hr a
    have product := positionedCell_product_of_radius O hs inside dtd.1.mapsTo large
    obtain ⟨x,hx⟩ := rv_surjective O t
    have hxn : x ≠ 0 := fun h => ht (by simp [← hx,h])
    have eq : {y | rv O (y-f a) = t} = openDisc O (f a + x) (unsignedValue O t) := by
      ext y
      rw [← hx,unsignedValue_rv]
      change rv O (y - f a) = rv O x ↔ O.valuation (y - (f a+x)) < O.valuation x
      rw [rv_eq_rv_iff_valuation O hxn,sub_sub]
    exact Or.inl ⟨large,ht,f a + x,product.trans (congrArg (A ×ˢ ·) eq)⟩
  · have small := not_le.1 large
    have opp := oppositeParadigm_small_of_target_radius O hr affine image small
    have cont (p : K × K) (hp : p ∈ C) : p.2 ∈ B := by
      have h := dtd.1.mapsTo hp.1
      change p.2 ∈ openDisc O b s
      rw [← openDisc_change_center O h]
      change O.valuation (p.2 - f p.1) < s
      rw [← unsignedValue_rv,show rv O (p.2 - f p.1) = t from hp.2]
      exact small
    have inv (y : K) (hy : y ∈ B) : g y ∈ A ∧ f (g y) = y := by
      obtain ⟨x,hx,he⟩ := dtd.1.surjOn hy
      have hx' := (congrArg g he).symm.trans (dtd.2.1.1 hx)
      exact ⟨hx'.symm ▸ hx,dtd.2.1.2 hy⟩
    exact Or.inr ⟨opp,cont,inv,positionedCell_translate_first O B affine opp cont inv⟩

end GeneralizedEuler.Section5
