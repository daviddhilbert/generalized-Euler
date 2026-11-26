module

public import Section4.LexicographicConeSubdivision
import all Section4.LexicographicConeSubdivision
import all Section4.PolyhedralGenerators
import all Section4.ConeBoundary

/-! Disjoint relatively open simplicial cones on subsets of a prescribed
finite set of generators, including the zero-dimensional face. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F E : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup E] [Module F E]

structure SimpleCone (F E : Type*) [Field F] [AddCommGroup E] [Module F E] where
  rays : ℕ
  param : (Fin rays → F) →ₗ[F] E
  injective : Function.Injective param

def SimpleCone.openPart (c : SimpleCone F E) : Set E := c.param '' {x | ∀ i, 0<x i}
def SimpleCone.ray (c : SimpleCone F E) (j : Fin c.rays) := c.param (Pi.single j 1)
def SimpleCone.closedPart (c : SimpleCone F E) : Set E := c.param '' {x | ∀ i, 0≤x i}

variable {n : ℕ} (A : (Fin n → F) →ₗ[F] E)

def extendSupport (s : Finset (Fin n)) : (Fin (Fintype.card s) → F) →ₗ[F] (Fin n → F) where
  toFun x i := if h : i ∈ s then x (Fintype.equivFin s ⟨i,h⟩) else 0
  map_add' x y := funext fun i => by split <;> simp_all
  map_smul' t x := funext fun i => by split <;> simp_all

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem extend_at (s : Finset (Fin n)) (x : Fin (Fintype.card s) → F) (i : s) :
    extendSupport s x i.val = x (Fintype.equivFin s i) := by simp [extendSupport,i.property]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem extend_out (s : Finset (Fin n)) (x : Fin (Fintype.card s) → F) {i : Fin n} (h : i∉s) :
    extendSupport s x i = 0 := by simp [extendSupport,h]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem extend_injective (s : Finset (Fin n)) :
    Function.Injective (extendSupport (F := F) s) := by
  intro x y e; funext j
  obtain ⟨i,rfl⟩ := (Fintype.equivFin s).surjective j
  simpa only [extend_at] using congrFun e i.val

@[expose] def supportedCone (s : Finset (Fin n)) (h : AdmissibleSupport A s) : SimpleCone F E where
  rays := Fintype.card s
  param := A.comp (extendSupport s)
  injective := by
    intro x y eq
    apply extend_injective s
    exact sub_eq_zero.mp ((admissible_independent A h) _ (fun i hi => by simp [extend_out _ _ hi])
      (by rw [map_sub]; exact sub_eq_zero.mpr eq))

theorem supported_openPart (s : Finset (Fin n)) (h : AdmissibleSupport A s) (u : E) :
    u ∈ (supportedCone A s h).openPart ↔ ∃ x : Fin n → F, (∀ i, 0≤x i) ∧ live x=s ∧ A x=u := by
  classical
  constructor
  · rintro ⟨x,pos,rfl⟩
    refine ⟨extendSupport s x,fun i => ?_,?_,rfl⟩
    · by_cases hi : i∈s
      · exact (extend_at s x ⟨i,hi⟩).symm ▸ (pos _).le
      · rw [extend_out s x hi]
    · ext i
      change (i ∈ Finset.univ.filter (fun t => 0 < extendSupport s x t)) ↔ _
      rw [Finset.mem_filter]; simp only [Finset.mem_univ,true_and]
      by_cases hi : i∈s
      · exact iff_of_true ((extend_at s x ⟨i,hi⟩).symm ▸ pos _) hi
      · rw [extend_out s x hi]; simp [hi]
  · rintro ⟨x,pos,rfl,rfl⟩
    let e := (Fintype.equivFin (live x)).symm
    let t (j) := x (e j).val
    refine ⟨t,fun j => (Finset.mem_filter.mp (e j).property).2,?_⟩
    apply congrArg A
    funext i
    by_cases hi : i ∈ live x
    · simpa only [t,e,Equiv.symm_apply_apply] using extend_at (live x) t ⟨i,hi⟩
    · rw [extend_out _ _ hi]
      exact (pos i).antisymm (le_of_not_gt (fun lt => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩)))

theorem supported_ray (s : Finset (Fin n)) (h : AdmissibleSupport A s) (j : Fin (Fintype.card s)) :
    (supportedCone A s h).ray j = A (Pi.single ((Fintype.equivFin s).symm j).val 1) := by
  apply congrArg A
  let e := Fintype.equivFin s
  funext i
  change (extendSupport s (Pi.single j (1 : F))) i = (Pi.single (e.symm j).val (1 : F) : Fin n → F) i
  by_cases hi : i∈s
  · let q : s := ⟨i,hi⟩
    have atq := extend_at s (Pi.single j (1 : F)) q
    change (extendSupport s (Pi.single j (1 : F))) i = (Pi.single j (1 : F) : Fin _ → F) (e q) at atq
    rw [atq]
    by_cases eq : i=(e.symm j).val
    · have same : q=e.symm j := Subtype.ext eq
      rw [same,e.apply_symm_apply,Pi.single_eq_same,eq,Pi.single_eq_same]
    · have ne : e q ≠ j := fun h => eq (congrArg Subtype.val (e.eq_symm_apply.mpr h))
      simp only [Pi.single_eq_of_ne ne,Pi.single_eq_of_ne eq]
  · have ne : i≠(e.symm j).val := fun eq => hi (eq ▸ (e.symm j).property)
    rw [extend_out s (Pi.single j (1 : F)) hi,Pi.single_eq_of_ne ne]

theorem subdivide_generators :
    ∃ (m : ℕ) (c : Fin m → SimpleCone F E),
      (∀ i j, ∃ t, (c i).ray j = A (Pi.single t 1)) ∧
      Pairwise (fun i j => Disjoint (c i).openPart (c j).openPart) ∧
      (⋃ i, (c i).openPart) = A '' {x | ∀ i, 0≤x i} := by
  classical
  let T := {s : Finset (Fin n) // AdmissibleSupport A s}
  let e := (Fintype.equivFin T).symm
  let c i := supportedCone A (e i).val (e i).property
  refine ⟨_,c,fun i j => ⟨((Fintype.equivFin (e i).val).symm j).val,supported_ray A _ _ j⟩,?_,?_⟩
  · intro i j ne
    apply disjoint_left.mpr
    intro u hu hv
    obtain ⟨x,px,sx,im⟩ := (supported_openPart A _ _ u).mp hu
    obtain ⟨y,py,sy,im'⟩ := (supported_openPart A _ _ u).mp hv
    have eq := admissible_unique A px py (sx.symm ▸ (e i).property) (sy.symm ▸ (e j).property) (im.trans im'.symm)
    exact ne (e.injective (Subtype.ext (sx.symm.trans ((congrArg live eq).trans sy))))
  · ext u; rw [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨x,px,_,im⟩ := (supported_openPart A _ _ u).mp hi
      exact ⟨x,px,im⟩
    · rintro ⟨x,px,rfl⟩
      obtain ⟨y,py,im,ad⟩ := exists_admissible A x px
      let t : T := ⟨live y,ad⟩
      exact ⟨e.symm t,(supported_openPart A _ _ _).mpr ⟨y,py,(congrArg Subtype.val (e.apply_symm_apply t)).symm,im⟩⟩

end GeneralizedEuler.Section4.Polyhedral
