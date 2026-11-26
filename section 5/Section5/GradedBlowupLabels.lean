module

public import Section5.UnaryBlowup
public import Mathlib.Data.Set.Finite.Lattice

/-! The two degrees of an elementary blowup. Finiteness of the retained
label fibers bounds both strata before forming an RV object. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {F A : Type*} [DecidableEq F]

/-- Delete the coordinate in which the object is blown up. -/
@[expose] def deleteCoordinate {Y : Type*} (j : F) (x : F → Y) : {i : F // i ≠ j} → Y :=
  fun i => x i.val

/-- The updated label keeps the other coordinates and multiplies the
chosen coordinate by the extra RV parameter. -/
@[expose] def blowupLabel (j : F) (f : A → F → RV0 O) (p : A × RV0 O) : F → RV0 O :=
  Function.update (f p.1) j (p.2 * f p.1 j)

theorem delete_blowupLabel (j : F) (f : A → F → RV0 O) (p : A × RV0 O) :
    deleteCoordinate j (blowupLabel O j f p) = deleteCoordinate j (f p.1) := by
  funext i
  exact Function.update_of_ne i.property _ _

theorem blowupLabel_zero_iff (j : F) (f : A → F → RV0 O) (p : A × RV0 O)
    (hne : f p.1 j ≠ 0) : blowupLabel O j f p j = 0 ↔ p.2 = 0 := by
  rw [blowupLabel,Function.update_self,mul_eq_zero,or_iff_left hne]

theorem blowupLabel_nonzero (j : F) (f : A → F → RV0 O) (p : A × RV0 O)
    (h : ∀ i, f p.1 i ≠ 0) (hp : p.2 ≠ 0) (i : F) : blowupLabel O j f p i ≠ 0 := by
  by_cases e : i = j
  · subst i
    exact (blowupLabel_zero_iff O j f p (h j)).not.2 hp
  · rw [blowupLabel,Function.update_of_ne e]
    exact h i

omit [DecidableEq F] in
/-- The finite-to-one deletion hypothesis on the image combines with
the finite fibers of the original structure map. -/
theorem blowup_deleted_finite (j : F) (f : A → F → RV0 O)
    (finiteF : ∀ t, (f ⁻¹' {t}).Finite)
    (finiteDelete : ∀ t, {u ∈ Set.range f | deleteCoordinate j u = t}.Finite) :
    ∀ t, ((deleteCoordinate j ∘ f) ⁻¹' {t}).Finite := by
  intro t
  apply ((finiteDelete t).biUnion (fun u _ => finiteF u)).subset
  intro a ha
  exact Set.mem_iUnion₂.mpr ⟨f a,⟨⟨a,rfl⟩,ha⟩,rfl⟩

/-- For a fixed blown-up label and a fixed original point, the
multiplier is uniquely recovered by dividing by the old coordinate. -/
theorem blowup_finite_fibers (j : F) (f : A → F → RV0 O)
    (nonzero : ∀ a, f a j ≠ 0)
    (finiteDelete : ∀ t, ((deleteCoordinate j ∘ f) ⁻¹' {t}).Finite) :
    ∀ t, (blowupLabel O j f ⁻¹' {t}).Finite := by
  intro t
  have inj : Set.InjOn Prod.fst (blowupLabel O j f ⁻¹' {t}) := by
    rintro ⟨a,s⟩ ha ⟨a',s'⟩ ha' he
    change a = a' at he
    subst a'
    have hc := congrFun (ha.trans ha'.symm : blowupLabel O j f (a,s) = blowupLabel O j f (a,s')) j
    simp only [blowupLabel, Function.update_self] at hc
    rw [mul_comm (G := RV0 O) s, mul_comm (G := RV0 O) s'] at hc
    exact Prod.ext rfl (rv_mul_left_cancel O (nonzero a) hc)
  apply (Set.finite_image_iff inj).1
  apply (finiteDelete (deleteCoordinate j t)).subset
  rintro _ ⟨p,hp,rfl⟩
  have he : blowupLabel O j f p = t := hp
  exact (delete_blowupLabel O j f p).symm.trans (congrArg (deleteCoordinate j) he)

end GeneralizedEuler.Section5
