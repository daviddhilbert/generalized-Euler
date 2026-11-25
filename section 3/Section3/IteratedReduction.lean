module

public import Section3.ContractedJets
import all Section3.SmoothSlices
import all Section3.ReducedJets
import all Section2.TorsorDerivative

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set Filter
open scoped Topology

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [TopologicalSpace k] [OrderTopology k] {n : ℕ}

/-- Coordinate derivative, extended by zero where no derivative exists.
On the common open set its value is uniquely determined. -/
noncomputable def orderPartial (i : Fin n) (g : (Fin n → k) → k) (x : Fin n → k) : k := by
  classical
  exact if h : ∃ s, HasOrderDerivativeAt (fun u => g (Function.update x i u)) (x i) s then h.choose else 0

noncomputable def iteratedOrderPartial (g : (Fin n → k) → k) : List (Fin n) → (Fin n → k) → k
  | [] => g
  | i :: w => orderPartial i (iteratedOrderPartial g w)

def wordIndex (w : List (Fin n)) (i : Fin n) := w.count i

/-- The adjacent identities imply equality with the actual iterated
coordinate derivative, for every ordering of a prescribed multi-index.
Only germs inside the open set enter the recursion. -/
theorem iterated_of_adjacent {p : Fin n → ℕ} {W : Set (Fin n → k)} (op : IsOpen W)
    (J : (Fin n → ℕ) → (Fin n → k) → k)
    (adj : ∀ q ≤ p, ∀ i, q i ≠ 0 → ∀ x ∈ W,
      HasOrderDerivativeAt (fun u => J (Function.update q i (q i-1)) (Function.update x i u)) (x i) (J q x)) :
    ∀ w, wordIndex w ≤ p → EqOn (iteratedOrderPartial (J 0) w) (J (wordIndex w)) W := by
  classical
  intro w
  induction w with
  | nil => intro _ x _; rfl
  | cons i w ih =>
    intro hp x hx
    let q := wordIndex (i :: w)
    have zero : q i ≠ 0 := by simp [q,wordIndex]
    have pred : Function.update q i (q i-1) = wordIndex w := by
      ext j
      by_cases he : j = i
      · subst j; simp [q,wordIndex]
      · simp [q,wordIndex,he,Ne.symm he]
    have bound : wordIndex w ≤ p := by
      intro j
      exact (show wordIndex w j ≤ q j by simp [wordIndex,q,List.count_cons]).trans (hp j)
    have hd := adj q hp i zero x hx
    rw [pred] at hd
    have cont : Continuous (Function.update x i) := continuous_pi (fun j => by
      by_cases h : j = i
      · subst j; simp only [Function.update_self]; exact continuous_id
      · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : k => x j)))
    have inside : x i ∈ (Function.update x i) ⁻¹' W := by simpa only [mem_preimage,Function.update_eq_self]
    obtain ⟨d,dp,near⟩ := interval_around (op.preimage cont) inside
    have der := derivative_of_agreement_near hd dp (H := fun u => iteratedOrderPartial (J 0) w (Function.update x i u))
      (fun h hh => (ih bound (near h hh)).symm)
    change orderPartial i (iteratedOrderPartial (J 0) w) x = J q x
    unfold orderPartial
    rw [dite_eq_left ⟨_,der⟩]
    exact (Exists.choose_spec (⟨_,der⟩ : ∃ s, HasOrderDerivativeAt _ _ s)).unique der

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] [OrderTopology k] in
/-- Finite families of label exceptions admit one definable exceptional
set. The closure input is the residue dimension theorem. -/
theorem finite_label_exceptions {L : Language} [L.Structure k] {P : Set k} {I : Type*} [Finite I]
    (A : Set (Fin n → k)) (E : I → Set (Fin n → k))
    (data : ∀ i, E i ⊆ A ∧ P.Definable L (E i) ∧ projectionDimensionWithBot (E i) < (n : WithBot ℕ))
    (tame : ∀ B : Set (Fin n → k), P.Definable L B → interior B = ∅ → IsNowhereDense B) :
    ∃ V ⊆ A, P.Definable L V ∧ projectionDimensionWithBot V < (n : WithBot ℕ) ∧ ∀ i, E i ⊆ V := by
  let V := ⋃ i, E i
  have thin : IsNowhereDense V := IsNowhereDense.iUnion (fun i => tame _ (data i).2.1
    (dimensionWithBot_lt_arity_iff.mp (data i).2.2))
  exact ⟨V,iUnion_subset (fun i => (data i).1),definable_iUnion_of_finite (fun i => (data i).2.1),
    dimensionWithBot_lt_arity_iff.mpr (eq_empty_of_subset_empty ((interior_mono subset_closure).trans thin.subset)),
    fun i => subset_iUnion E i⟩

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] [OrderTopology k] in
/-- Corollary 3.32 with varying coefficients and jets of different
orders. Each jet contributes its good locus from 3.31, including the
earlier exceptional labels for contraction and smoothness. Coefficients
are contracted as polynomials; no uniform choice of representatives of
residue coefficients is required. -/
theorem differential_polynomial_off_exceptions {K : Type*} [Field K] (O : ValuationSubring K)
    {L : Language} [L.Structure k] {P : Set k} {X I : Type*} [Finite I]
    (label : X → Fin n → k) (A : Set (Fin n → k)) (E : I → Set (Fin n → k))
    (data : ∀ i, E i ⊆ A ∧ P.Definable L (E i) ∧ projectionDimensionWithBot (E i) < (n : WithBot ℕ))
    (tame : ∀ B : Set (Fin n → k), P.Definable L B → interior B = ∅ → IsNowhereDense B)
    (poly : X → MvPolynomial I O) (redPoly : (Fin n → k) → MvPolynomial I (Residue O))
    (coeff : ∀ x, label x ∈ A → MvPolynomial.map (IsLocalRing.residue O) (poly x) = redPoly (label x))
    (jet : I → X → O) (redJet : I → (Fin n → k) → Residue O)
    (compat : ∀ i x, label x ∈ A \ E i → IsLocalRing.residue O (jet i x) = redJet i (label x)) :
    ∃ V ⊆ A, P.Definable L V ∧ projectionDimensionWithBot V < (n : WithBot ℕ) ∧
      ∀ x, label x ∈ A \ V →
        IsLocalRing.residue O (MvPolynomial.eval (fun i => jet i x) (poly x)) =
          MvPolynomial.eval (fun i => redJet i (label x)) (redPoly (label x)) := by
  obtain ⟨V,sub,defV,dim,inc⟩ := finite_label_exceptions A E data tame
  refine ⟨V,sub,defV,dim,fun x hx => ?_⟩
  rw [←coeff x hx.1]
  exact residue_differential_polynomial O _ _ _ (fun i => compat i x ⟨hx.1,fun he => hx.2 (inc i he)⟩)

end GeneralizedEuler.Section3
