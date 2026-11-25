module

public import Section3.FixedHolly
public import Section3.Monotonicity
public import Mathlib.Topology.Order.Basic
import all Section2.ValuativeInterval

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [Field K] [LinearOrder K] (O : ValuationSubring K)
    {L J : Language} [L.Structure K] [J.Structure K] {P : Set K}

omit [Field K] [LinearOrder K] in
private theorem definable_unary_image {g : K → K}
    (dg : P.DefinableFun J (fun v : Fin 1 → K => g (v 0))) {A : Set K} (da : P.Definable₁ J A) :
    P.Definable₁ J (g '' A) := by
  let ρ : Option (Fin 1) → Fin 1 ⊕ Unit := fun t => t.elim (.inl 0) (fun _ => .inr ())
  have gr := (show P.Definable J _ from dg).preimage_comp ρ
  have dom := (show P.Definable J _ from da).preimage_comp (fun _ : Fin 1 => (Sum.inr () : Fin 1 ⊕ Unit))
  change P.Definable J {w : Fin 1 → K | w 0 ∈ g '' A}
  convert (dom.inter gr).exists_of_finite using 1
  ext w
  change (∃ x ∈ A, g x = w 0) ↔ ∃ z : Unit → K, z () ∈ A ∧ g (z ()) = w 0
  exact ⟨fun ⟨x,h,he⟩ => ⟨fun _ => x,h,he⟩,fun ⟨z,h,he⟩ => ⟨z (),h,he⟩⟩

theorem valuativeInterval_of_convex_hnf {A : Set K} (conv : A.OrdConnected) (hne : A.Nonempty)
    {D : Finset (Set K)} (hnf : IsHollyDecomposition O A D) : IsValuativeInterval O A := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨C,hc,hxC⟩ := mem_iUnion₂.mp (hnf.2.1 ▸ hx)
  have eqn := hnf.piece_eq_component O hc hxC
  have he : C = A := eqn.trans (ordConnectedComponent_subset.antisymm
    (subset_ordConnectedComponent hx Subset.rfl))
  exact he ▸ hnf.1 C hc

variable [TopologicalSpace K]

/-- Corollary 3.4 from 3.3, pure-field monotonicity and HNF. Intersect
the two original partitions, then take their intrinsic Holly components.
Each restriction retains a pure branch over the same base, and the
definable intermediate value property gives one interval as its image. -/
theorem holly_monotonicity (embed : L →ᴸ J) [embed.IsExpansionOn K]
    (leSym : J.Relations 2) (hLE : ∀ v : Fin 2 → K, Structure.RelMap leSym v ↔ v 0 ≤ v 1)
    (holly : ∀ U, P.Definable₁ J U → ∃ H, IsHollyDecomposition O U H)
    (A : Set K) (f : K → K) {m : ℕ} (B : Fin m → Set K) (g : Fin m → K → K)
    (pieces : ∀ i, P.Definable₁ J (B i) ∧ B i ⊆ A ∧ EqOn (g i) f (B i))
    (uniqueB : ∀ x ∈ A, ∃! i, x ∈ B i)
    (pure : ∀ i, P.DefinableFun L (fun v : Fin 1 → K => g i (v 0)))
    (omin : ∀ i, ∃ (k : ℕ) (D : Fin k → Set K), (∀ x, ∃! j, x ∈ D j) ∧
      ∀ j, P.Definable₁ L (D j) ∧ ContinuousOn (g i) (D j) ∧ MonotonePiece (g i) (D j) ∧
        ∀ x ∈ D j, ∀ y ∈ D j, ∀ w ∈ uIcc (g i x) (g i y), ∃ z ∈ uIcc x y, g i z = w) :
    ∃ (n : ℕ) (C : Fin n → Set K), (∀ x ∈ A, ∃! j, x ∈ C j) ∧ ∀ j,
      C j ⊆ A ∧ P.Definable₁ J (C j) ∧ IsValuativeInterval O (C j) ∧ ContinuousOn f (C j) ∧
      MonotonePiece f (C j) ∧ IsValuativeInterval O (f '' C j) ∧
        ∃ h : K → K, P.DefinableFun L (fun v : Fin 1 → K => h (v 0)) ∧ EqOn h f (C j) := by
  classical
  choose k D one data using omin
  let part (i : Fin m) (j : Fin (k i)) := B i ∩ D i j
  have defPart i j : P.Definable₁ J (part i j) := (pieces i).1.inter ((data i j).1.map_expansion embed)
  choose cells covers using fun i j => holly (part i j) (defPart i j)
  let Ind := (i : Fin m) × (j : Fin (k i)) × (cells i j)
  let e := Fintype.equivFin Ind
  let C (z : Ind) := z.2.2.val
  have sub (i j) (t : cells i j) : t.val ⊆ part i j :=
    fun x hx => (covers i j).2.1.symm.subset (mem_iUnion₂.mpr ⟨t.val,t.property,hx⟩)
  have oneCell (i j) (x : K) (hx : x ∈ part i j) : ∃! t : cells i j, x ∈ t.val := by
    obtain ⟨T,hT,hxT⟩ := mem_iUnion₂.mp ((covers i j).2.1 ▸ hx)
    exact ⟨⟨T,hT⟩,hxT,fun t ht => Subtype.ext
      (((covers i j).piece_eq_component O t.property ht).trans ((covers i j).piece_eq_component O hT hxT).symm)⟩
  refine ⟨_,fun j => C (e.symm j),?_,?_⟩
  · intro x hx
    obtain ⟨i,hi,ui⟩ := uniqueB x hx
    obtain ⟨j,hj,uj⟩ := one i x
    obtain ⟨t,ht,ut⟩ := oneCell i j x ⟨hi,hj⟩
    refine ⟨e ⟨i,j,t⟩,by simpa [C] using ht,?_⟩
    intro v hv
    obtain ⟨⟨i',j',t'⟩,rfl⟩ := e.surjective v
    change (C (e.symm (e ⟨i',j',t'⟩))) x at hv
    rw [e.symm_apply_apply] at hv
    obtain rfl := ui i' (sub i' j' t' hv).1
    obtain rfl := uj j' (sub _ j' t' hv).2
    rw [ut t' hv]
  · intro v
    obtain ⟨⟨i,j,t⟩,rfl⟩ := e.surjective v
    simp only [Equiv.symm_apply_apply,C]
    let T := t.val
    have st : T ⊆ B i := (sub i j t).trans inter_subset_left
    have sd : T ⊆ D i j := (sub i j t).trans inter_subset_right
    have eqn : EqOn (g i) f T := (pieces i).2.2.mono st
    have hT : IsValuativeInterval O T := (covers i j).1 t.val t.property
    obtain ⟨lo,hi,_,_,he⟩ := hT.2
    have cv : T.OrdConnected := he ▸ valuativeInterval_ordConnected lo hi
    have dt := fixed_base_holly_components O leSym hLE (defPart i j) (covers i j) t.val t.property
    have dim : P.Definable₁ J (g i '' T) := definable_unary_image ((pure i).map_expansion embed) dt
    obtain ⟨ims,him⟩ := holly _ dim
    have ci := image_ordConnected_of_intermediate_values cv (fun x hx y hy =>
      (data i j).2.2.2 x (sd hx) y (sd hy))
    have hval := valuativeInterval_of_convex_hnf O ci (hT.1.image _) him
    refine ⟨st.trans (pieces i).2.1,dt,hT,((data i j).2.1.mono sd).congr eqn.symm,?_,
      (image_congr eqn) ▸ hval,_,pure i,eqn⟩
    cases (data i j).2.2.1.restrict sd with
    | const same => exact .const (fun x hx y hy => (eqn hx).symm.trans ((same x hx y hy).trans (eqn hy)))
    | increasing up => exact .increasing (fun x hx y hy lt => eqn hx ▸ eqn hy ▸ up hx hy lt)
    | decreasing down => exact .decreasing (fun x hx y hy lt => eqn hx ▸ eqn hy ▸ down hx hy lt)

end GeneralizedEuler.Section3
