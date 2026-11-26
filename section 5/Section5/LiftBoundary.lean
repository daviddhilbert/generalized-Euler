module

public import Section3.Contraction

/-! The paired boundary exclusions in the full-arity step of Lemma 5.12. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section3

variable {X Y U V : Type*} (p : X → U) (q : Y → V) (e : U ≃ V) (h : X → Y)
  (hlabel : ∀ x, q (h x) = e (p x))

include hlabel in
/-- A candidate lift meeting every target fiber is onto off the RV
boundary of its image. -/
theorem surj_lift_off_boundary (hp : Function.Surjective p) {y : Y}
    (hy : q y ∉ rvBoundary q (Set.range h)) : ∃ x, h x = y := by
  by_contra! hn
  have hy' : y ∉ Set.range h := fun ⟨x, hxy⟩ => hn x hxy
  obtain ⟨x, hx⟩ := hp (e.symm (q y))
  apply hy
  refine ⟨⟨h x, Set.mem_range_self x, ?_⟩, y, rfl, hy'⟩
  rw [hlabel x, hx, e.apply_symm_apply]

include hlabel in
/-- Off both exceptional sets, the candidate map and its right inverse
are inverse bijections on the paired fibers. The right inverse is chosen
over each target field tuple. -/
theorem bijOn_lift_off_boundaries
    (g : {y : Y // q y ∉ rvBoundary q (Set.range h)} → X)
    (hg : ∀ y, h (g y) = y.val) :
    let B := rvBoundary q (Set.range h)
    let D := rvBoundary p (Set.range g)
    let good : Set U := {u | e u ∉ B ∧ u ∉ D}
    Set.BijOn h (p ⁻¹' good) (q ⁻¹' (e '' good)) := by
  intro B D good
  have right_label (y : {y : Y // q y ∉ B}) : e (p (g y)) = q y.val := by
    rw [← hlabel, hg]
  have inverse (x : X) (hx : p x ∈ good) :
      g ⟨h x, by rw [hlabel]; exact hx.1⟩ = x := by
    let z : {y : Y // q y ∉ B} := ⟨h x, by rw [hlabel]; exact hx.1⟩
    have hpz : p (g z) = p x := e.injective ((right_label z).trans (hlabel x))
    have hxg : x ∈ Set.range g := by
      by_contra hnot
      exact hx.2 ⟨⟨g z, Set.mem_range_self z, hpz⟩, x, rfl, hnot⟩
    obtain ⟨y, hy⟩ := hxg
    have eq : y = z := Subtype.ext ((hg y).symm.trans (congrArg h hy))
    change g z = x
    exact eq ▸ hy
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨p x, hx, (hlabel x).symm⟩
  · intro x hx x' hx' hxx'
    have eq : (⟨h x, by rw [hlabel]; exact hx.1⟩ : {y : Y // q y ∉ B}) =
        ⟨h x', by rw [hlabel]; exact hx'.1⟩ := Subtype.ext hxx'
    exact (inverse x hx).symm.trans ((congrArg g eq).trans (inverse x' hx'))
  · rintro y ⟨u, hu, eq⟩
    let z : {y : Y // q y ∉ B} := ⟨y, eq ▸ hu.1⟩
    have hgz : p (g z) = u := e.injective ((right_label z).trans eq.symm)
    exact ⟨g z, by change p (g z) ∈ good; rwa [hgz], hg z⟩

end GeneralizedEuler.Section5
