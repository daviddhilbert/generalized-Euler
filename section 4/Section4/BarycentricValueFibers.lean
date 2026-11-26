module

public import Section4.SimplexBox
import all Section4.SimplexBox
import all Section4.BoundedValueBoxes
import all Section4.DefinableValueFrames

/-! Positive coefficients with one prescribed sum, as they occur over a
ray of the parameter cone in the box decomposition. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

def sumFiber {n : ℕ} (b : V) : Set (Fin (n+1) → V) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i = b}

def sumFiberMap {n : ℕ} (x : Fin (n+1) → V) := simplexCoordinates (Fin.init x)

theorem sumFiber_init_image {n : ℕ} (b : V) :
    Fin.init '' sumFiber (n := n) b = openValueSimplex b := by
  ext x
  constructor
  · rintro ⟨u,⟨pos,total⟩,rfl⟩
    rw [Fin.sum_univ_castSucc] at total
    exact ⟨fun i => pos i.castSucc,by change (∑ i : Fin n, u i.castSucc) < b; rw [← total]; exact lt_add_of_pos_right _ (pos _)⟩
  · rintro ⟨pos,small⟩
    refine ⟨Fin.snoc x (b - ∑ i, x i),⟨?_,?_⟩,Fin.init_snoc ..⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using sub_pos.mpr small
      | cast i => simpa using pos i
    · simp [Fin.sum_univ_castSucc]

omit [IsStrictOrderedModule F V] in
include F in
theorem sumFiberMap_image {n : ℕ} (b : V) (hb : 0 < b) :
    sumFiberMap '' sumFiber (n := n) b = boundedBox (fun _ : Fin n => b) := by
  change (simplexCoordinates ∘ (Fin.init : (Fin (n+1) → V) → Fin n → V)) '' _ = _
  exact (Set.image_comp simplexCoordinates (Fin.init : (Fin (n+1) → V) → Fin n → V) _).trans (by rw [sumFiber_init_image,simplex_to_box F b hb])

theorem sumFiberMap_injOn {n : ℕ} (b : V) : InjOn sumFiberMap (sumFiber (n := n) b) := by
  intro x hx y hy eq
  have h := simplex_injective n eq
  have hs := hx.2.trans hy.2.symm
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc] at hs
  have same : (∑ i : Fin n, x i.castSucc) = ∑ i : Fin n, y i.castSucc := congrArg (fun u => ∑ i, u i) h
  rw [same] at hs
  exact funext (Fin.lastCases (add_left_cancel hs) (congrFun h))

variable {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)
  (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
include lang order in
theorem sumFiber_definable {n : ℕ} (b : V) (hb : b ∈ G) : (G : Set V).Definable J (sumFiber (n := n) b) := by
  classical
  have pos (i : Fin (n+1)) : (G : Set V).Definable J {x : Fin (n+1) → V | 0 < x i} := by
    let pair (x : Fin (n+1) → V) := ![x i,0]
    have hd : (G : Set V).DefinableMap J pair := by
      intro j; fin_cases j
      · exact Set.DefinableFun.proj J
      · exact J.definableFun_const _ G.zero_mem
    convert (order.preimage_map hd).compl using 1
    ext x; exact lt_iff_not_ge
  have ds (t : Finset (Fin (n+1))) : (G : Set V).DefinableFun J (fun x : Fin (n+1) → V => ∑ i ∈ t, x i) := by
    induction t using Finset.induction_on with
    | empty => simpa using J.definableFun_const (Fin (n+1)) G.zero_mem
    | insert i t hi ih => simpa only [Finset.sum_insert hi] using lang.addFun (Set.DefinableFun.proj J (i := i)) ih
  convert (Set.definable_iInter_of_finite pos).inter ((ds Finset.univ).ofPred_eq (J.definableFun_const _ hb)) using 1
  ext x; simp [sumFiber]

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
include lang order in
theorem sumFiberMap_definable (n : ℕ) : (G : Set V).DefinableMap J (sumFiberMap (V := V) (n := n)) :=
  fun i => ((simplex_coordinates_definable F G lang order n) i).comp (g := Fin.init) (fun _ => Set.DefinableFun.proj J)

end GeneralizedEuler.Section4
