module

public import Section4.HeightDrop
public import Section4.DefinableValueFrames
import all Section4.TupleFibers
import all Section4.ValueStratification

/-! Degree one of Question 4.16. Generic unary labels are matched on
whole fibers. Saturation makes each definable unmatched tag finite. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup T] [Module F T]
  (v : T →ₗ[F] V) (G : Submodule F V)

theorem unary_whole_match (R : (Fin 1 → T) → (Fin 1 → T) → Prop)
    (invariant : ∀ L x y, R x y → R (shear v G L ∘ x) (shear v G L ∘ y))
    (inj : ∀ {x x' y}, R x y → R x' y → x=x') (single : ∀ {x y y'}, R x y → R x y' → y=y')
    (d : v.ker) (hd : d ≠ 0) {x y} (h : R x y) (generic : v (x 0) ∉ G) :
    {b | ∃ a ∈ fullFiber v (v ∘ x), R a b} = fullFiber v (v ∘ y) := by
  apply whole_fiber_match v G R invariant inj single d hd h
  exact linearIndependent_unique_iff.mpr (fun eq => generic ((Submodule.Quotient.mk_eq_zero G).mp eq))

theorem finite_unmatched_unary {P : ∀ k, Set (Fin k → V) → Prop} (sat : RealizesAffineAvoidance G P)
    (D : Set (Fin 1 → V)) (hd : P 1 D) (old : ∀ x ∈ D, x 0 ∈ G) : D.Finite := by
  classical
  have dep : ¬ ∃ x ∈ D, LinearIndependent F (G.mkQ ∘ x) := by
    rintro ⟨x,hx,ind⟩
    exact linearIndependent_unique_iff.mp ind ((Submodule.Quotient.mk_eq_zero G).mpr (old x hx))
  obtain ⟨p,cover⟩ := finite_pivot_cover sat hd dep
  refine (p.finite_toSet.biUnion (fun a _ => Set.finite_range a.frame.eval)).subset ?_
  intro x hx
  obtain ⟨a,ha,mem⟩ := cover x hx
  exact Set.mem_iUnion₂.mpr ⟨a,ha,mem⟩

section Matching
variable {X Y I J : Type*} (a : X → I) (b : Y → J) (f : X ≃ Y)

def WholeMatch (i : I) (j : J) : Prop := f '' (a ⁻¹' {i}) = b ⁻¹' {j}

theorem wholeMatch_functional (hb : Function.Surjective b) {i j k}
    (h : WholeMatch a b f i j) (h' : WholeMatch a b f i k) : j=k := by
  obtain ⟨y,hy⟩ := hb j
  exact hy.symm.trans (show b y = k from (congrArg (y ∈ ·) (h.symm.trans h')).mp hy)

theorem wholeMatch_injective (ha : Function.Surjective a) {i j k}
    (h : WholeMatch a b f i k) (h' : WholeMatch a b f j k) : i=j := by
  obtain ⟨x,hx⟩ := ha i
  have mem : f x ∈ f '' (a ⁻¹' {j}) := (h.trans h'.symm) ▸ (Set.mem_image_of_mem f (show x ∈ a ⁻¹' {i} from hx))
  obtain ⟨y,hy,eq⟩ := mem
  exact hx.symm.trans (f.injective eq ▸ hy)

theorem wholeMatch_preserves_matched (x : X) : (∃ j, WholeMatch a b f (a x) j) ↔ ∃ i, WholeMatch a b f i (b (f x)) := by
  constructor
  · rintro ⟨j,h⟩
    have eq : b (f x) = j := (congrArg (f x ∈ ·) h).mp (Set.mem_image_of_mem f (show x ∈ a ⁻¹' {a x} from rfl))
    exact ⟨a x,eq.symm ▸ h⟩
  · rintro ⟨i,h⟩
    have mem : f x ∈ f '' (a ⁻¹' {i}) := h.symm ▸ (show f x ∈ b ⁻¹' {b (f x)} from rfl)
    obtain ⟨u,hu,eq⟩ := mem
    exact ⟨_,(f.injective eq ▸ hu : a x = i).symm ▸ h⟩

def unmatchedFibers :
    {x : X // ¬ ∃ j, WholeMatch a b f (a x) j} ≃ {y : Y // ¬ ∃ i, WholeMatch a b f i (b y)} := by
  exact f.subtypeEquiv (fun x => not_congr (wholeMatch_preserves_matched a b f x))

end Matching
end GeneralizedEuler.Section4
