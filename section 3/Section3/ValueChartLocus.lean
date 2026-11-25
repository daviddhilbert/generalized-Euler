module

public import Section3.GoodLabels
public import Section2.ContinuousDefinitions
import all Section2.ContinuousDefinitions

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set Filter
open scoped Topology

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [TopologicalSpace k] [OrderTopology k]
    {L : Language} [L.Structure k] {P : Set k} {n : ℕ}

private theorem mem_interior_iff_box (S : Set (Fin n → k)) (x : Fin n → k) :
    x ∈ interior S ↔ ∃ l u : Fin n → k, (∀ j, l j < x j ∧ x j < u j) ∧
      ∀ y, (∀ j, l j < y j ∧ y j < u j) → y ∈ S := by
  classical
  constructor
  · intro hx
    have h := mem_interior_iff_mem_nhds.mp hx
    rw [nhds_pi,Filter.mem_pi] at h
    obtain ⟨J,_,B,hB,sub⟩ := h
    choose l u hcenter inner using fun j => mem_nhds_iff_exists_Ioo_subset.mp (hB j)
    exact ⟨l,u,hcenter,fun y hy => sub (fun j _ => inner j (hy j))⟩
  · rintro ⟨l,u,hx,sub⟩
    let box := univ.pi (fun j => Ioo (l j) (u j))
    exact interior_maximal (show box ⊆ S from fun y hy => sub y (fun j => hy j (mem_univ _)))
      (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)) (fun j _ => hx j)

/-- The fiber interior at the diagonal is a fixed-base definable
condition. The formula quantifies the lower and upper corners of an
open box and tests all its points, also for the empty tuple. -/
theorem definable_fiber_interior (F : OrderedFieldTerms L) (hF : InterpretsOrderedFieldTerms (A := k) F)
    (R : (Fin n → k) → (Fin n → k) → Prop)
    (hR : P.Definable L {w : Fin n ⊕ Fin n → k | R (w ∘ Sum.inl) (w ∘ Sum.inr)}) :
    P.Definable L {x | x ∈ interior {y | R x y}} := by
  obtain ⟨φ,hφ⟩ := hR
  let N := Fin n
  let A := N ⊕ N
  let B := A ⊕ N
  let D := B ⊕ N
  let cmp {I : Type} (i j : I) := (((L.lhomWithConstants P).onRelation F.le).formula ![Term.var j,.var i]).not
  have lt {I : Type} (i j : I) (w : I → k) : (cmp i j).Realize w ↔ w i < w j := by
    rw [show cmp i j = _ from rfl,Formula.realize_not,Formula.realize_rel,LHom.map_onRelation,hF.le,←not_le]
    rfl
  let box {I : Type} (l x u : N → I) := Formula.iInf (fun j => cmp (l j) (x j) ⊓ cmp (x j) (u j))
  have inside {I : Type} (l x u : N → I) (w : I → k) : (box l x u).Realize w ↔
      ∀ j, w (l j) < w (x j) ∧ w (x j) < w (u j) := by
    simp only [box,Formula.realize_iInf,Formula.realize_inf,lt]
  let x : N → B := Sum.inl ∘ Sum.inl
  let l : N → B := Sum.inl ∘ Sum.inr
  let u : N → B := Sum.inr
  let y : N → D := Sum.inr
  let test := (box (Sum.inl ∘ l) y (Sum.inl ∘ u)).imp (φ.relabel (Sum.elim (Sum.inl ∘ x) y))
  refine ⟨Formula.iExs N (Formula.iExs N ((box l x u) ⊓ Formula.iAlls N test)),?_⟩
  ext w
  change w ∈ interior {z | R w z} ↔ _
  rw [mem_interior_iff_box]
  have rel (a b z : N → k) : (φ.relabel (Sum.elim (Sum.inl ∘ x) y)).Realize
      (Sum.elim (Sum.elim (Sum.elim w a) b) z) ↔ R w z := by
    rw [Formula.realize_relabel]
    have eqn : Sum.elim (Sum.elim (Sum.elim w a) b) z ∘ Sum.elim (Sum.inl ∘ x) y = Sum.elim w z := by
      funext j; cases j <;> rfl
    rw [eqn]
    exact (Set.ext_iff.mp hφ _).symm
  simp only [mem_ofPred_eq,Formula.realize_iExs,Formula.realize_iAlls,Formula.realize_inf,
    test,Formula.realize_imp,inside,l,x,u,y,Function.comp_apply,Sum.elim_inl,Sum.elim_inr]
  apply exists_congr; intro a; apply exists_congr; intro b
  apply and_congr_right; intro _
  apply forall_congr'; intro z; apply imp_congr_right; intro _
  exact (rel a b z).symm

/-- Remove the value-fiber boundaries for all the jets at once.
Definability over the original base uses equality of two output values,
so their individual values never have to be named in that base. -/
theorem definable_value_chart_locus {I V : Type*} [Finite I] (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := k) F) (A : Set (Fin n → k)) (dA : P.Definable L A)
    (v : I → (Fin n → k) → V) (fin : ∀ i, (v i '' A).Finite)
    (dEq : ∀ i, P.Definable L {w : Fin n ⊕ Fin n → k | v i (w ∘ Sum.inl) = v i (w ∘ Sum.inr)})
    (tame : ∀ S : Set (Fin n → k), (univ : Set k).Definable L S → IsNowhereDense (frontier S)) :
    ∃ W ⊆ A, P.Definable L W ∧ P.Definable L (A \ W) ∧ IsOpen W ∧
      projectionDimensionWithBot (A \ W) < (n : WithBot ℕ) ∧
      ∀ x ∈ W, ∀ i, ∀ᶠ y in 𝓝 x, v i y = v i x := by
  classical
  let cell (i : I) (b : V) := {x ∈ A | v i x = b}
  let good (i : I) := ⋃ b ∈ v i '' A, interior (cell i b)
  let W := interior A ∩ ⋂ i, good i
  have diag (i : I) : good i = {x | x ∈ interior {y | y ∈ A ∧ v i x = v i y}} := by
    ext x
    change (x ∈ ⋃ b ∈ v i '' A, interior (cell i b)) ↔ _
    rw [mem_iUnion₂]
    constructor
    · rintro ⟨b,_,hx⟩
      have he : v i x = b := (interior_subset hx).2
      exact interior_mono (t := {y | y ∈ A ∧ v i x = v i y}) (fun z hz => ⟨hz.1,he.trans hz.2.symm⟩) hx
    · intro hx
      have hA := (interior_subset hx).1
      exact ⟨v i x,mem_image_of_mem _ hA,interior_mono (s := {y | y ∈ A ∧ v i x = v i y}) (t := cell i (v i x)) (fun z hz => ⟨hz.1,hz.2.symm⟩) hx⟩
  have dInt : P.Definable L (interior A) := definable_fiber_interior F hF (fun _ y => y ∈ A) (dA.preimage_comp Sum.inr)
  have dGood (i : I) : P.Definable L (good i) := by
    rw [diag]
    exact definable_fiber_interior F hF _ ((dA.preimage_comp (Sum.inr : Fin n → Fin n ⊕ Fin n)).inter (dEq i))
  have dW : P.Definable L W := dInt.inter (definable_iInter_of_finite dGood)
  have dc (i : I) (b) (hb : b ∈ v i '' A) : (univ : Set k).Definable L (cell i b) := by
    obtain ⟨x,_,rfl⟩ := hb
    have assign : (univ : Set k).DefinableMap L (fun y : Fin n → k => Sum.elim y x) := by
      intro j; cases j with
      | inl j => exact DefinableFun.proj L
      | inr j => exact L.definableFun_const _ (mem_univ _)
    exact (dA.mono (subset_univ _)).inter (((dEq i).mono (subset_univ _)).preimage_map assign)
  let bad (i : I) := ⋃ b ∈ v i '' A, frontier (cell i b)
  have thin (i : I) : IsNowhereDense (bad i) := by
    let B := v i '' A
    have : Finite B := (fin i).to_subtype
    have eqn : bad i = ⋃ b : B, frontier (cell i b.val) := by simp [bad,B,iUnion_subtype]
    rw [eqn]
    exact IsNowhereDense.iUnion (fun b => tame _ (dc i _ b.property))
  have cover : A \ W ⊆ frontier A ∪ ⋃ i, bad i := by
    intro x hx
    by_contra! no
    have nA := fun h => no (Or.inl h)
    apply hx.2
    refine ⟨(mem_interior_iff_notMem_frontier hx.1).mpr nA,mem_iInter.mpr (fun i => ?_)⟩
    let hv := mem_image_of_mem (v i) hx.1
    have inC : x ∈ cell i (v i x) := ⟨hx.1,rfl⟩
    apply mem_iUnion₂.mpr
    exact ⟨v i x,hv,(mem_interior_iff_notMem_frontier inC).mpr
      (fun h => no (Or.inr (mem_iUnion_of_mem i (mem_iUnion₂.mpr ⟨v i x,hv,h⟩))))⟩
  have hthin := ((tame _ (dA.mono (subset_univ _))).union (IsNowhereDense.iUnion thin)).mono cover
  refine ⟨W,fun _ h => interior_subset h.1,dW,dA.sdiff dW,
    isOpen_interior.inter (isOpen_iInter_of_finite (fun _ => isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_interior)))),
    dimensionWithBot_lt_arity_iff.mpr (eq_empty_of_subset_empty ((interior_mono subset_closure).trans hthin.subset)),?_⟩
  intro x hx i
  have he := (diag i) ▸ mem_iInter.mp hx.2 i
  filter_upwards [mem_interior_iff_mem_nhds.mp he] with y hy using hy.2.symm

end GeneralizedEuler.Section3
