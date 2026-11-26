module

public import Section4.ValueFrames
public import Section2.AffineValueSelection

/-! Finite disjoint affine stratification by elimination of dependent
coordinates. The model-theoretic input is realization of finitely
satisfiable affine avoidance conditions over the fixed base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (G : Submodule F V)

theorem exists_pivot_of_dependent {n : ℕ} (x : Fin (n+1) → V)
    (h : ¬LinearIndependent F (G.mkQ ∘ x)) : ∃ p : ValuePivot G n, x ∈ Set.range p.frame.eval := by
  classical
  let u := G.mkQ ∘ x
  rw [linearIndependent_iff_notMem_span] at h
  push Not at h
  obtain ⟨k,hk⟩ := h
  have eq : u '' (Set.univ \ {k}) = Set.range (u ∘ k.succAbove) := by
    ext a
    constructor
    · rintro ⟨j,hj,rfl⟩
      have hn : j ≠ k := hj.2
      obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq hn
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨Set.mem_univ _,k.succAbove_ne i⟩,rfl⟩
  change u k ∈ Submodule.span F (u '' _) at hk
  rw [eq] at hk
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hk
  let t := ∑ j, c j • x (k.succAbove j)
  have hzero : G.mkQ (x k - t) = 0 := by
    rw [map_sub]; apply sub_eq_zero.mpr
    simpa only [u,Function.comp_apply,t,map_sum,map_smul] using hc.symm
  refine ⟨⟨k,c,⟨_,(Submodule.Quotient.mk_eq_zero G).mp hzero⟩⟩,?_⟩
  apply ValuePivot.mem_range _ _ |>.mpr
  change x k = t + (x k - t)
  abel

/-- The only saturation instance used by the stratification. All tests have
coefficients in the exponent field and translations in the base. -/
def RealizesAffineAvoidance (P : ∀ n, Set (Fin n → V) → Prop) : Prop :=
  ∀ n (D : Set (Fin (n+1) → V)), P (n+1) D →
    (∀ s : Finset (ValuePivot G n), ∃ x ∈ D, ∀ p ∈ s, x ∉ Set.range p.frame.eval) →
      ∃ x ∈ D, ∀ p : ValuePivot G n, x ∉ Set.range p.frame.eval

variable {G}
theorem finite_pivot_cover {P : ∀ n, Set (Fin n → V) → Prop} (sat : RealizesAffineAvoidance G P)
    {n} {D : Set (Fin (n+1) → V)} (hd : P _ D)
    (h : ¬∃ x ∈ D, LinearIndependent F (G.mkQ ∘ x)) :
    ∃ s : Finset (ValuePivot G n), ∀ x ∈ D, ∃ p ∈ s, x ∈ Set.range p.frame.eval := by
  classical
  by_contra! bad
  obtain ⟨x,hx,avoids⟩ := sat n D hd bad
  have dep : ¬LinearIndependent F (G.mkQ ∘ x) := fun hi => h ⟨x,hx,hi⟩
  obtain ⟨p,hp⟩ := exists_pivot_of_dependent G x dep
  exact avoids p hp

structure IndependentPiece (P : ∀ n, Set (Fin n → V) → Prop) (G : Submodule F V) (n : ℕ) where
  rank : ℕ
  frame : ValueFrame G rank n
  domain : Set (Fin rank → V)
  definable : P rank domain
  independent : ∃ x ∈ domain, LinearIndependent F (G.mkQ ∘ x)

namespace IndependentPiece
variable {P : ∀ n, Set (Fin n → V) → Prop} {n m : ℕ}
def support (a : IndependentPiece P G n) := a.frame.eval '' a.domain

def map (f : ValueFrame G n m) (a : IndependentPiece P G n) : IndependentPiece P G m :=
  { a with frame := f.comp a.frame }

theorem support_map (f : ValueFrame G n m) (a : IndependentPiece P G n) :
    (a.map f).support = f.eval '' a.support := by
  simp only [support,map,Set.image_image]
  exact congrArg (fun g => g '' a.domain) (funext (f.comp_eval a.frame))
end IndependentPiece

/-- The first applicable pivot defines a disjoint cut, even when the input
tuple satisfies several independent affine equations. -/
def firstPivot {n l} (p : Fin l → ValuePivot G n) (D : Set (Fin (n+1) → V)) (i : Fin l) :
    Set (Fin n → V) := {z | (p i).frame.eval z ∈ D ∧
      ∀ j < i, (p i).frame.eval z ∉ Set.range (p j).frame.eval}

theorem stratify_values (P : ∀ n, Set (Fin n → V) → Prop)
    (cut : ∀ {n l} (p : Fin l → ValuePivot G n) (D) (i), P _ D → P _ (firstPivot p D i))
    (sat : RealizesAffineAvoidance G P) {n} (D : Set (Fin n → V)) (hd : P n D) :
    ∃ (l : ℕ) (a : Fin l → IndependentPiece P G n), ∀ x,
      (x ∈ D ↔ ∃ i, x ∈ (a i).support) ∧ ∀ i j, x ∈ (a i).support → x ∈ (a j).support → i = j := by
  classical
  induction n with
  | zero =>
    by_cases h : D.Nonempty
    · refine ⟨1,fun _ => ⟨0,ValueFrame.identity 0,D,hd,?_⟩,?_⟩
      · obtain ⟨x,hx⟩ := h; exact ⟨x,hx,linearIndependent_empty_type⟩
      · intro x
        simp [IndependentPiece.support,ValueFrame.identity_eval]
    · refine ⟨0,Fin.elim0,fun x => ⟨?_,fun i => i.elim0⟩⟩
      simp [Set.not_nonempty_iff_eq_empty.mp h]
  | succ n ih =>
    by_cases h : ∃ x ∈ D, LinearIndependent F (G.mkQ ∘ x)
    · refine ⟨1,fun _ => ⟨_,ValueFrame.identity _,D,hd,h⟩,?_⟩
      intro x; simp [IndependentPiece.support,ValueFrame.identity_eval]
    obtain ⟨s,hs⟩ := finite_pivot_cover sat hd h
    let e := s.equivFin.symm
    let p (i : Fin s.card) := (e i).val
    choose count a cover using fun i => ih (firstPivot p D i) (cut p D i hd)
    let I := Σ i, Fin (count i)
    let idx := (Fintype.equivFin I).symm
    let piece (k : I) := (a k.1 k.2).map (p k.1).frame
    refine ⟨_,piece ∘ idx,fun x => ⟨?_,?_⟩⟩
    · constructor
      · intro hx
        obtain ⟨q,hq,belongs⟩ := hs x hx
        let hits := Finset.univ.filter (fun i => x ∈ Set.range (p i).frame.eval)
        have hh : hits.Nonempty := ⟨e.symm ⟨q,hq⟩,by simpa [hits,p] using belongs⟩
        let i := hits.min' hh
        have hi := Finset.mem_filter.mp (hits.min'_mem hh)
        obtain ⟨z,hz⟩ := hi.2
        have hz' : z ∈ firstPivot p D i := by
          refine ⟨hz ▸ hx,fun j hj mem => ?_⟩
          exact (not_le.mpr hj) (hits.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz ▸ mem⟩))
        obtain ⟨j,hj⟩ := (cover i z).1.mp hz'
        refine ⟨idx.symm ⟨i,j⟩,?_⟩
        change x ∈ (piece (idx (idx.symm ⟨i,j⟩))).support
        rw [Equiv.apply_symm_apply]
        simp only [piece,IndependentPiece.support_map]
        exact ⟨z,hj,hz⟩
      · rintro ⟨j,hj⟩
        let k := idx j
        change x ∈ ((a k.1 k.2).map _).support at hj
        rw [IndependentPiece.support_map] at hj
        obtain ⟨z,hz,rfl⟩ := hj
        exact ((cover k.1 z).1.mpr ⟨k.2,hz⟩).1
    · intro i j hi hj
      apply idx.injective
      generalize hk : idx i = k at *
      generalize hl : idx j = l at *
      change x ∈ (piece (idx i)).support at hi
      change x ∈ (piece (idx j)).support at hj
      rw [hk] at hi; rw [hl] at hj
      rcases k with ⟨i,t⟩; rcases l with ⟨j,u⟩
      change x ∈ ((a i t).map _).support at hi
      change x ∈ ((a j u).map _).support at hj
      rw [IndependentPiece.support_map] at hi hj
      obtain ⟨z,hz,ez⟩ := hi
      obtain ⟨w,hw,ew⟩ := hj
      have zi := (cover i z).1.mpr ⟨t,hz⟩
      have wj := (cover j w).1.mpr ⟨u,hw⟩
      have ij : i = j := le_antisymm (le_of_not_gt fun lt => zi.2 j lt ⟨w,ew.trans ez.symm⟩)
        (le_of_not_gt fun lt => wj.2 i lt ⟨z,ez.trans ew.symm⟩)
      subst j
      have zw := (p i).frame.injective (ez.trans ew.symm)
      subst w
      exact congrArg (Sigma.mk i) ((cover i z).2 _ _ hz hw)

end GeneralizedEuler.Section4
