module

public import Section4.BoundedValueBoxes
import all Section4.BoundedValueBoxes

/-! A uniform piecewise linear bijection between a simplex and a box
over an ordered vector space. Its coordinates are sums of pairwise minima,
so only addition and order are needed to define the graph. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set
variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

def simplexCoordinates {n : ℕ} (x : Fin n → V) (i : Fin n) := ∑ j, min (x i) (x j)

omit [IsOrderedAddMonoid V] in
private theorem at_min {n} (x : Fin n → V) (i) (h : ∀ j, x i ≤ x j) :
    simplexCoordinates x i = n • x i := by simp [simplexCoordinates,fun j => min_eq_left (h j)]

private theorem coord_upper {n} (x : Fin n → V) (i) : simplexCoordinates x i ≤ n • x i := by
  simpa [simplexCoordinates] using Finset.sum_le_sum (s := Finset.univ) (fun j _ => min_le_left (x i) (x j))

private theorem strict_coord {n} (x : Fin n → V) {i j} (h : x i < x j) :
    simplexCoordinates x i < simplexCoordinates x j := by
  apply Finset.sum_lt_sum (fun k _ => min_le_min_right _ h.le)
  exact ⟨j,Finset.mem_univ _,by simpa [min_eq_left h.le] using h⟩

omit [IsOrderedAddMonoid V] in
private theorem drop_min {n} (x : Fin (n+1) → V) (i : Fin (n+1)) (h : ∀ j, x i ≤ x j) (j : Fin n) :
    simplexCoordinates x (i.succAbove j) = x i + simplexCoordinates (x ∘ i.succAbove) j := by
  unfold simplexCoordinates
  rw [Fin.sum_univ_succAbove _ i,min_eq_right (h _)]
  rfl

private theorem simplex_injective (n : ℕ) : Function.Injective (simplexCoordinates (V := V) (n := n)) := by
  induction n with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro x y eq
    obtain ⟨i,_,hx⟩ := Finset.univ.exists_min_image x Finset.univ_nonempty
    have mx (j) := hx j (Finset.mem_univ _)
    have my (j) : y i ≤ y j := by
      by_contra! lt
      have less := strict_coord y lt
      rw [← eq] at less
      exact less.not_ge (Finset.sum_le_sum (fun k _ => min_le_min_right _ (mx j)))
    have atI := congrFun eq i
    rw [at_min x i mx,at_min y i my] at atI
    have root : x i = y i := (smul_right_injective V (Nat.succ_ne_zero n)) atI
    have rest : x ∘ i.succAbove = y ∘ i.succAbove := by
      apply ih; funext j
      have same := congrFun eq (i.succAbove j)
      rw [drop_min x i mx j,drop_min y i my j,root] at same
      exact add_left_cancel same
    funext j
    exact i.succAboveCases root (fun k => congrFun rest k) j

variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Module F V]

include F in
private theorem simplex_surjective (n : ℕ) : Function.Surjective (simplexCoordinates (V := V) (n := n)) := by
  induction n with
  | zero => exact fun y => ⟨y,Subsingleton.elim _ _⟩
  | succ n ih =>
    intro y
    obtain ⟨i,_,hy⟩ := Finset.univ.exists_min_image y Finset.univ_nonempty
    let a := ((n+1 : ℕ) : F)⁻¹ • y i
    have mul : (n+1) • a = y i := by
      rw [← Nat.cast_smul_eq_nsmul F]
      exact smul_inv_smul₀ (by exact_mod_cast Nat.succ_ne_zero n) _
    obtain ⟨z,hz⟩ := ih (fun j => y (i.succAbove j) - a)
    have az (j : Fin n) : a ≤ z j := by
      by_contra! lt
      have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
      have above := (smul_lt_smul_iff_of_pos_left hn).mpr lt
      have h := (coord_upper z j).trans_lt above
      rw [congrFun hz j] at h
      have bad := (sub_lt_iff_lt_add.mp h).trans_eq (succ_nsmul a n).symm
      exact bad.not_ge (mul ▸ hy _ (Finset.mem_univ _))
    let x : Fin (n+1) → V := i.insertNth (α := fun _ => V) a z
    have mx : ∀ j, x i ≤ x j := i.succAboveCases (by rfl) (fun j => by simpa [x] using az j)
    refine ⟨x,funext (i.succAboveCases ?_ (fun j => ?_))⟩
    · simpa [at_min x i mx,x] using mul
    · rw [drop_min x i mx]
      have rest : x ∘ i.succAbove = z := funext (fun j => Fin.insertNth_apply_succAbove _ _ _ _)
      rw [rest,congrFun hz j]
      simp [x]

def openValueSimplex {n : ℕ} (b : V) : Set (Fin n → V) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < b}

include F in
theorem simplex_to_box {n : ℕ} (b : V) (hb : 0 < b) :
    simplexCoordinates '' openValueSimplex (n := n) b = boundedBox (fun _ : Fin n => b) := by
  ext y
  obtain ⟨x,rfl⟩ := simplex_surjective (V := V) F n y
  rw [(simplex_injective n).mem_set_image]
  by_cases h : n = 0
  · subst n; simp [openValueSimplex,boundedBox,hb]
  · have : NeZero n := ⟨h⟩
    obtain ⟨j,_,max⟩ := Finset.univ.exists_max_image x Finset.univ_nonempty
    have upper : simplexCoordinates x j = ∑ i, x i := by
      simp [simplexCoordinates,fun i => min_eq_right (max i (Finset.mem_univ _))]
    constructor
    · rintro ⟨pos,sum⟩ i
      exact ⟨Finset.sum_pos (fun t _ => lt_min (pos i) (pos t)) Finset.univ_nonempty,
        (Finset.sum_le_sum (fun k _ => min_le_right (x i) (x k))).trans_lt sum⟩
    · intro hit
      refine ⟨fun i => ?_,upper ▸ (hit j).2⟩
      by_contra! hi
      exact ((hit i).1.trans_le (coord_upper x i)).not_ge (nsmul_nonpos hi _)


variable {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)
  (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})

omit [IsOrderedAddMonoid V] [LinearOrder F] [IsStrictOrderedRing F] in
include lang order in
theorem simplex_coordinates_definable (n : ℕ) :
    (G : Set V).DefinableMap J (simplexCoordinates (n := n)) := by
  intro i
  have term (j : Fin n) : (G : Set V).DefinableFun J (fun x : Fin n → V => min (x i) (x j)) := by
    let indices : Fin 2 → Fin n := ![i,j]
    have cut : (G : Set V).Definable J {x : Fin n → V | x i ≤ x j} := order.preimage_comp indices
    simpa only [min_def] using Set.DefinableFun.ite cut (Set.DefinableFun.proj J) (Set.DefinableFun.proj J)
  have sum (s : Finset (Fin n)) : (G : Set V).DefinableFun J (fun x => ∑ j ∈ s, min (x i) (x j)) := by
    induction s using Finset.induction_on with
    | empty => simpa using J.definableFun_const (Fin n) G.zero_mem
    | insert j s hj ih => simpa only [Finset.sum_insert hj] using lang.addFun (term j) ih
  exact sum Finset.univ

include lang order in
theorem simplex_box_class {n : ℕ} (b : V) (hb : 0 < b)
    (ds : (G : Set V).Definable J (openValueSimplex (n := n) b))
    (db : (G : Set V).Definable J (boundedBox (fun _ : Fin n => b))) :
    ValueObject.pieceClass _ ds = ValueObject.pieceClass _ db := by
  have f := simplex_coordinates_definable F G lang order n
  have eq := ValueObject.pieceClass_images simplexCoordinates id f (fun _ => Set.DefinableFun.proj J) _ ds
    (simplex_injective n).injOn Function.injective_id.injOn
  simpa only [simplex_to_box F b hb,Set.image_id] using eq.symm

end GeneralizedEuler.Section4
