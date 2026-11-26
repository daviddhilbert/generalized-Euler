module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Tactic

/-! The extreme-ray argument in the parameter subdivision for Question
4.16, over the ordered field of exponents. The parameter cone is written
in its independent ray coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F E I B : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup E] [Module F E]

def polyCone (a : I → E →ₗ[F] F) : Set E := {u | ∀ i, 0 ≤ a i u}
def activeFace (a : I → E →ₗ[F] F) (u : E) : Set E :=
  {w | w ∈ polyCone a ∧ ∀ i, a i u = 0 → a i w = 0}
def positiveRay (u : E) := (fun t : F => t • u) '' Ici 0

private theorem small_scalar [Finite I] (x y : I → F) (pos : ∀ i, 0 ≤ x i)
    (active : ∀ i, x i = 0 → y i = 0) : ∃ ε : F, 0 < ε ∧ ∀ i, ε * |y i| ≤ x i := by
  classical
  let _ := Fintype.ofFinite I
  let bound i := if x i = 0 then 1 else x i / (|y i|+1)
  have hb i : 0 < bound i := by
    dsimp [bound]; split_ifs with h
    · exact one_pos
    · exact div_pos (lt_of_le_of_ne (pos i) (Ne.symm h)) (by positivity)
  let values := insert (1 : F) (Finset.univ.image bound)
  have ne : values.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let ε := values.min' ne
  have eps : 0 < ε := by
    have mem := values.min'_mem ne
    obtain h | h := Finset.mem_insert.mp mem
    · change 0 < values.min' ne; rw [h]; exact one_pos
    · obtain ⟨i,_,eq⟩ := Finset.mem_image.mp h
      change 0 < values.min' ne; rw [← eq]; exact hb i
  refine ⟨ε,eps,fun i => ?_⟩
  by_cases hi : x i = 0
  · simp [hi,active i hi]
  · have le := values.min'_le (bound i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have le' : ε ≤ x i / (|y i|+1) := by simpa [bound,hi] using le
    have := (le_div_iff₀ (by positivity : 0 < |y i|+1)).mp le'
    linarith

theorem perturb [Finite I] (a : I → E →ₗ[F] F) {u w : E} (hu : u ∈ polyCone a)
    (hw : ∀ i, a i u = 0 → a i w = 0) :
    ∃ ε : F, 0 < ε ∧ u+ε • w ∈ polyCone a ∧ u-ε • w ∈ polyCone a := by
  obtain ⟨ε,pos,le⟩ := small_scalar (fun i => a i u) (fun i => a i w) hu hw
  have bound i : |ε * a i w| ≤ a i u := by simpa [abs_mul,abs_of_pos pos] using le i
  refine ⟨ε,pos,fun i => ?_,fun i => ?_⟩
  · simp only [map_add,map_smul,smul_eq_mul]
    linarith [(abs_le.mp (bound i)).1]
  · simp only [map_sub,map_smul,smul_eq_mul]
    linarith [(abs_le.mp (bound i)).2]

theorem extreme_projection_of_directions [Finite I] [Finite B] [DecidableEq B]
    (a : I → E →ₗ[F] F) (π : E →ₗ[F] (B → F)) (u : E)
    (inside : u ∈ polyCone a) (positive : ∀ j, 0 ≤ π u j)
    (directions : ∀ i, 0 < π u i → ∃ w : E, (∀ t, a t u=0 → a t w=0) ∧ π w=Pi.single i 1)
    (extreme : IsExtreme F (polyCone a ∩ {x | ∀ j, 0 ≤ π x j}) (positiveRay (F := F) u))
    {i j : B} (hi : 0 < π u i) (hj : 0 < π u j) : i=j := by
  by_contra ne
  let e : B → F := Pi.single i 1
  obtain ⟨w,hw,image⟩ := directions i hi
  let rows : I ⊕ B → E →ₗ[F] F := Sum.elim a (fun t => (LinearMap.proj t).comp π)
  have whole : polyCone rows = polyCone a ∩ {x | ∀ t, 0 ≤ π x t} := by
    ext x; exact ⟨fun h => ⟨fun t => h (.inl t),fun t => h (.inr t)⟩,
      fun h t => by cases t with | inl t => exact h.1 t | inr t => exact h.2 t⟩
  have tight (t) : rows t u = 0 → rows t w = 0 := by
    cases t with
    | inl t => exact hw t
    | inr t =>
      intro h
      have neq : t≠i := fun eq => hi.ne' (eq ▸ h)
      exact (congrFun image t).trans (Pi.single_eq_of_ne neq _)
  obtain ⟨ε,hε,left,right⟩ := perturb rows (whole.symm ▸ And.intro inside positive) tight
  have onRay : u ∈ positiveRay (F := F) u := ⟨1,zero_le_one,one_smul _ _⟩
  obtain ⟨t,_,same⟩ := extreme.left_mem_of_mem_openSegment (whole ▸ left) (whole ▸ right) onRay
    (mem_openSegment_add_sub (𝕜 := F) u (ε • w))
  have eq (l) := congrFun (congrArg π same) l
  have unit : t = 1 := by
    have h : t * π u j = π u j := by simpa [image,e,Ne.symm ne] using eq j
    exact mul_right_cancel₀ hj.ne' (h.trans (one_mul _).symm)
  have h : π u i = π u i + ε := by simpa [unit,image,e] using eq i
  linarith

/-- If the image of the active face contains the parameter face of the
point, an extreme ray has at most one positive parameter coordinate. -/
theorem extreme_projection [Finite I] [Finite B] [DecidableEq B]
    (a : I → E →ₗ[F] F) (π : E →ₗ[F] (B → F)) (u : E)
    (inside : u ∈ polyCone a) (positive : ∀ j, 0 ≤ π u j)
    (adapted : {p : B → F | (∀ j, 0 ≤ p j) ∧ ∀ j, π u j = 0 → p j = 0} ⊆ π '' activeFace a u)
    (extreme : IsExtreme F (polyCone a ∩ {x | ∀ j, 0 ≤ π x j}) (positiveRay (F := F) u))
    {i j : B} (hi : 0 < π u i) (hj : 0 < π u j) : i=j := by
  apply extreme_projection_of_directions a π u inside positive _ extreme hi hj
  intro i hi
  have nonneg (j) : 0 ≤ (Pi.single i 1 : B → F) j := by by_cases h : j=i <;> simp [h]
  have zeros (j) (hz : π u j=0) : (Pi.single i 1 : B → F) j=0 :=
    by
      have ne : j≠i := fun eq => hi.ne' ((congrArg (π u) eq).symm.trans hz)
      exact Pi.single_eq_of_ne ne _
  obtain ⟨w,mem,im⟩ := adapted ⟨nonneg,zeros⟩
  exact ⟨w,mem.2,im⟩

end GeneralizedEuler.Section4.Polyhedral
