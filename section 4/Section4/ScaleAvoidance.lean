module

public import Section4.IntervalScales
import all Section4.IntervalScales
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.ModelTheory.Definability
public import Mathlib.Algebra.Module.Torsion.Free

/-! Finite satisfiability and saturation for the successive choices of
coordinates attaining the ranks of a box. -/
public section
namespace GeneralizedEuler.Section4
open FirstOrder
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

/-- Distinct scalar fractions of a width outside a subspace belong to
distinct cosets. This works over an arbitrary ordered exponent field. -/
theorem interval_avoid_finite_cosets (H : Submodule F V) {b : V} (hb : 0 < b) (outside : b ∉ H)
    (centers : Finset V) : ∃ x ∈ Set.Ioo 0 b, ∀ g ∈ centers, x - g ∉ H := by
  classical
  have nz : H.mkQ b ≠ 0 := fun h => outside ((Submodule.Quotient.mk_eq_zero H).mp h)
  let q (r : F) := r • H.mkQ b
  have inj : Function.Injective q := smul_left_injective F nz
  have finite := (centers.finite_toSet.image H.mkQ).preimage inj.injOn
  obtain ⟨r,hr,miss⟩ := (Set.Ioo_infinite (zero_lt_one : (0:F) < 1)).exists_notMem_finite finite
  refine ⟨r • b,⟨smul_pos hr.1 hb,?_⟩,?_⟩
  · simpa using smul_lt_smul_of_pos_right hr.2 hb
  · intro g mem h
    apply miss
    refine ⟨g,mem,?_⟩
    have eq := (Submodule.Quotient.mk_eq_zero H).mpr h
    change H.mkQ (r • b - g) = 0 at eq
    rw [map_sub,map_smul,sub_eq_zero] at eq
    exact eq.symm

/-- Finite satisfiability of any family of definable unary conditions
over a single small parameter set, in the ordinary first-order saturation
form used by the rest of Section 4. -/
theorem realize_definable_conditions {J : Language} {W : Type*} [J.Structure W] (A : Set W)
    (sat : ∀ Δ : Set (J[[A]].Formula Unit),
      (∀ fs : Finset (J[[A]].Formula Unit), (↑fs : Set _) ⊆ Δ →
        ∃ x : Unit → W, ∀ φ ∈ fs, φ.Realize x) →
      ∃ x : Unit → W, ∀ φ ∈ Δ, φ.Realize x)
    {I : Type*} (test : I → Set (Unit → W)) (defTest : ∀ i, A.Definable J (test i))
    (finite : ∀ s : Finset I, ∃ x, ∀ i ∈ s, x ∈ test i) : ∃ x, ∀ i, x ∈ test i := by
  classical
  choose φ hφ using defTest
  obtain ⟨x,hx⟩ := sat (Set.range φ) (by
    intro s hs
    choose witness hw using fun p : s => hs p.property
    obtain ⟨x,hx⟩ := finite (Finset.univ.image witness)
    refine ⟨x,fun ψ mem => ?_⟩
    let p : s := ⟨ψ,mem⟩
    have h := hx (witness p) (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)
    rwa [hφ (witness p),hw p] at h)
  exact ⟨x,fun i => (hφ i).symm ▸ hx (φ i) ⟨i,rfl⟩⟩

variable (F) in
def scaleTube (a center : V) (c : F) : Set (Unit → V) := {x | |x () - center| ≤ |c| • |a|}

theorem mem_scaleSpace_iff_tube (a x : V) :
    x ∈ scaleSpace F a ↔ ∃ c : F, |x| ≤ |c| • |a| := by
  constructor
  · rintro ⟨c,hc,h⟩; exact ⟨c,by simpa [abs_of_nonneg hc] using h⟩
  · rintro ⟨c,h⟩; exact ⟨|c|,abs_nonneg _,h⟩


omit [IsStrictOrderedRing F] [IsStrictOrderedModule F V] in
/-- Each tube excluded from a ray has a finite upper endpoint. -/
theorem ray_avoid_finite_tubes {a step : V} (pos : 0 < step) (cuts : Finset (V × F)) :
    ∃ x : V, 0 < x ∧ ∀ p ∈ cuts, |p.2| • |a| < |x - p.1| := by
  classical
  let endpt (p : V × F) := p.1 + |p.2| • |a|
  obtain ⟨u,hu⟩ := (cuts.image endpt).bddAbove
  let x := max u 0 + step
  have high : max u 0 < x := lt_add_of_pos_right _ pos
  refine ⟨x,(le_max_right u 0).trans_lt high,?_⟩
  intro p hp
  have lt : p.1 + |p.2| • |a| < x := (hu (Finset.mem_image.mpr ⟨p,hp,rfl⟩)).trans_lt ((le_max_left _ _).trans_lt high)
  exact ((lt_sub_iff_add_lt).mpr ((add_comm (|p.2| • |a|) p.1).trans_lt lt)).trans_le (le_abs_self _)

/-- Saturation chooses a point of the domain outside the sum of the
parameter subspace and the scale subspace. The finite test is expressed
using individual intervals, which are definable even when the entire
convex subspace is external. -/
theorem realize_outside_scale {J : Language} [J.Structure V] (G : Submodule F V)
    (a : V) (D : Set V)
    (dom : (G : Set V).Definable J {x : Unit → V | x () ∈ D})
    (tube : ∀ g : G, ∀ c : F, (G : Set V).Definable J (scaleTube F a g.val c))
    (sat : ∀ Δ : Set (J[[(G : Set V)]].Formula Unit),
      (∀ fs : Finset (J[[(G : Set V)]].Formula Unit), (↑fs : Set _) ⊆ Δ →
        ∃ x : Unit → V, ∀ φ ∈ fs, φ.Realize x) →
      ∃ x : Unit → V, ∀ φ ∈ Δ, φ.Realize x)
    (finite : ∀ cuts : Finset (G × F), ∃ y ∈ D, ∀ p ∈ cuts, |p.2| • |a| < |y - p.1.val|) :
    ∃ y ∈ D, y ∉ G ⊔ scaleSpace F a := by
  classical
  let test : Option (G × F) → Set (Unit → V)
    | none => {x | x () ∈ D}
    | some p => (scaleTube F a p.1.val p.2)ᶜ
  have hd : ∀ i, (G : Set V).Definable J (test i) := by
    rintro (_|p)
    · exact dom
    · exact (tube p.1 p.2).compl
  obtain ⟨x,hx⟩ := realize_definable_conditions (G : Set V) sat test hd (by
    intro s
    obtain ⟨y,hy,h⟩ := finite s.eraseNone
    refine ⟨fun _ => y,?_⟩
    rintro (_|p) hp
    · exact hy
    · exact not_le.mpr (h p (Finset.mem_eraseNone.mpr hp)))
  refine ⟨x (),hx none,?_⟩
  rintro h
  obtain ⟨g,hg,z,hz,eq⟩ := Submodule.mem_sup.mp h
  obtain ⟨c,hc⟩ := (mem_scaleSpace_iff_tube a z).mp hz
  have avoids := hx (some (⟨g,hg⟩,c))
  apply avoids
  change |x () - g| ≤ |c| • |a|
  simpa [← eq] using hc

theorem bounded_finite_scale_avoidance (G : Submodule F V) {a b : V} (hb : 0 < b)
    (outside : b ∉ scaleSpace F a) (cuts : Finset (G × F)) :
    ∃ y ∈ Set.Ioo 0 b, ∀ p ∈ cuts, |p.2| • |a| < |y - p.1.val| := by
  classical
  obtain ⟨y,hy,h⟩ := interval_avoid_finite_cosets (scaleSpace F a) hb outside (cuts.image (fun p => p.1.val))
  refine ⟨y,hy,fun p hp => lt_of_not_ge ?_⟩
  exact fun le => h _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩) ((mem_scaleSpace_iff_tube a _).mpr ⟨p.2,le⟩)

end GeneralizedEuler.Section4
