module

public import Section5.PositioningLeafConditions
public import Section3.AffineSlopes
import all Section3.AffineSlopes

/-! Read the first-order tests on an actual unary graph. This gives
a direct way to verify a named leaf from its geometric description. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K) {P : TCsort → Type}

local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty

theorem positioningLeafValid_of_geometry
    {D : Set (SortedAssignment Z (SumVariables P U))}
    {G : Set (SortedAssignment Z (SumVariables (SumVariables P U) U))}
    (p : SortedAssignment Z P) (A : Set K) (f : K → K)
    (dom : ∀ x : fieldAssignment 1 Z, appendAssignments p x ∈ D ↔ x .vf 0 ∈ A)
    (graph : ∀ x y : fieldAssignment 1 Z, x .vf 0 ∈ A →
      (appendAssignments (appendAssignments p x) y ∈ G ↔ f (x .vf 0) = y .vf 0))
    (shape : A = ∅ ∨ (∃ a : K, A = {a}) ∨ ∃ (a : K) (r : O.ValueGroup),
      r ≠ 0 ∧ A = openDisc O a r ∧
      ((∀ x ∈ A, ∀ y ∈ A, f x = f y) ∨ ∃ (b : K) (s : O.ValueGroup) (u : RV O),
        s ≠ 0 ∧ f '' A = openDisc O b s ∧ RVAffineOn O A f u)) :
    positioningLeafValid O D G p := by
  rcases shape with empty | point | ⟨a,r,hr,ha,shape⟩
  · exact Or.inl (fun x h => (Set.notMem_empty _) (empty ▸ (dom x).1 h))
  · obtain ⟨a,ha⟩ := point
    exact Or.inr (Or.inl ⟨a,fun x => (dom x).trans (ha ▸ Iff.rfl)⟩)
  · refine Or.inr (Or.inr ⟨⟨a,r,hr,fun x => (dom x).trans (ha ▸ Iff.rfl)⟩,?_⟩)
    rcases shape with constant | ⟨b,s,u,hs,himage,affine⟩
    · apply Or.inl
      intro x y v w hx hv hxy hvw
      have hx' := (dom x).1 hx
      have hv' := (dom v).1 hv
      have y' := (graph x y hx').1 hxy
      have w' := (graph v w hv').1 hvw
      exact fieldAssignment_ext (fun i => by
        rw [Subsingleton.elim i (0 : Fin 1)]
        exact y'.symm.trans ((constant (x .vf 0) hx' (v .vf 0) hv').trans w'))
    · refine Or.inr ⟨⟨b,s,hs,?_⟩,(u : RV0 O),WithZero.coe_ne_zero,?_⟩
      · intro y
        have img : y .vf 0 ∈ f '' A ↔ y .vf 0 ∈ openDisc O b s := by rw [himage]
        refine (Iff.trans ?_ img)
        change (∃ x : fieldAssignment 1 Z,
          appendAssignments (appendAssignments p x) y ∈ G ∧ appendAssignments p x ∈ D) ↔ _
        constructor
        · rintro ⟨x,hg,hd⟩
          exact ⟨x .vf 0,(dom x).1 hd,(graph x y ((dom x).1 hd)).1 hg⟩
        · rintro ⟨x,hx,hy⟩
          let a : fieldAssignment 1 Z := fieldTupleAssignment (fun _ => x)
          exact ⟨a,(graph a y hx).2 hy,(dom a).2 hx⟩
      · intro x y v w hxy hvw
        have hx : x .vf 0 ∈ A := (dom x).1 hxy.2
        have hv : v .vf 0 ∈ A := (dom v).1 hvw.2
        rw [← (graph x y hx).1 hxy.1,← (graph v w hv).1 hvw.1]
        exact affine (x .vf 0) hx (v .vf 0) hv

end GeneralizedEuler.Section5
