module

public import Section3.IteratedReduction
public import Section3.RegularPoints
import all Section3.RegularPoints
import all Section3.IteratedReduction
import all Section2.ResidueTopology

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set Filter
open scoped Topology

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [TopologicalSpace k] [OrderTopology k] {n : ℕ}

def LocallyInjectiveOn {X Y : Type*} [TopologicalSpace X] (f : X → Y) (A : Set X) : Prop :=
  ∀ x ∈ A, ∃ B, IsOpen B ∧ x ∈ B ∧ InjOn f (A ∩ B)

omit [IsStrictOrderedRing k] [OrderTopology k] in
/-- Generic rank in Remark 3.29. On every open box use a smaller
smooth constant-rank patch. The constant-rank theorem supplies a pair
in one fiber on any such open patch of deficient rank. -/
theorem dimension_singular_locus (A : Set (Fin n → k)) (f : (Fin n → k) → Fin n → k)
    (inj : LocallyInjectiveOn f A) (p : ℕ)
    (patch : ∀ B : Set (Fin n → k), IsOpen B → B.Nonempty → B ⊆ A →
      ∃ C ⊆ B, IsOpen C ∧ C.Nonempty ∧ ∃ J : OrderJetOn f (p+1) C,
        ∀ x ∈ C, ∀ y ∈ C, (J.jacobian x).rank = (J.jacobian y).rank)
    (fibers : ∀ C, IsOpen C → C.Nonempty → ∀ J : OrderJetOn f (p+1) C, ∀ r < n,
      (∀ x ∈ C, (J.jacobian x).rank = r) → ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ f x = f y) :
    projectionDimensionWithBot (A \ regularLocus f (p+1)) < (n : WithBot ℕ) ∧
    projectionDimensionWithBot (A \ regularLocus f 0) < (n : WithBot ℕ) := by
  have dense (B : Set (Fin n → k)) (op : IsOpen B) (ne : B.Nonempty) (sub : B ⊆ A) :
      ∃ x ∈ B, x ∈ regularLocus f (p+1) ∧ ContinuousAt f x := by
    obtain ⟨x,hx⟩ := ne
    obtain ⟨U,ou,xu,hi⟩ := inj x (sub hx)
    obtain ⟨C,cs,oc,⟨z,hz⟩,J,same⟩ := patch (B ∩ U) (op.inter ou) ⟨x,hx,xu⟩ (inter_subset_left.trans sub)
    have rank : (J.jacobian z).rank = n := by
      by_contra h
      have le : (J.jacobian z).rank ≤ n := by simpa using (J.jacobian z).rank_le_card_width
      obtain ⟨a,ha,b,hb,ne,he⟩ := fibers C oc ⟨z,hz⟩ J _ (lt_of_le_of_ne le h) (fun y hy => same y hy z hz)
      exact ne (hi ⟨sub (cs ha).1,(cs ha).2⟩ ⟨sub (cs hb).1,(cs hb).2⟩ he)
    refine ⟨z,(cs hz).1,⟨C,oc,hz,J,by simpa using rank⟩,?_⟩
    have cont := (J.continuous [] (by simp) z hz).continuousAt (oc.mem_nhds hz)
    rwa [J.base] at cont
  have dim (R : Set (Fin n → k)) (inc : ∀ x, x ∈ regularLocus f (p+1) → ContinuousAt f x → x ∈ R) :
      projectionDimensionWithBot (A \ R) < (n : WithBot ℕ) := by
    apply dimensionWithBot_lt_arity_iff.mpr
    apply not_nonempty_iff_eq_empty.mp
    intro ne
    obtain ⟨x,hx,hreg,hc⟩ := dense _ isOpen_interior ne (interior_subset.trans sdiff_subset)
    exact (interior_subset hx).2 (inc x hreg hc)
  exact ⟨dim _ (fun _ h _ => h),dim _ (fun _ _ h => h)⟩

/-- Relative definable connectedness, allowing parameters in the
residue field when testing a separation. -/
def DefinablyConnectedDomain {k : Type*} [TopologicalSpace k] (L : Language) [L.Structure k]
    (U : Set (Fin n → k)) : Prop :=
  ∀ B : Set (Fin n → k), (univ : Set k).Definable L B → IsClopen ((Subtype.val : U → _) ⁻¹' B) →
    Disjoint U B ∨ U ⊆ B

noncomputable def orderJacobian (g : (Fin n → k) → Fin n → k) (t : Fin n → k) :
    Matrix (Fin n) (Fin n) k := fun i j => orderPartial j (fun x => g x i) t

omit [OrderTopology k] in
theorem orderJacobian_eq_jet {g : (Fin n → k) → Fin n → k} {V : Set (Fin n → k)} (J : OrderJetOn g 1 V)
    {t} (ht : t ∈ V) : orderJacobian g t = J.jacobian t := by
  ext i j
  have h := J.derivative [] (by simp) t ht j i
  rw [J.base] at h
  change orderPartial j (fun x => g x i) t = _
  unfold orderPartial
  rw [dite_eq_left ⟨_,h⟩]
  exact (Exists.choose_spec (⟨_,h⟩ : ∃ s, HasOrderDerivativeAt _ _ s)).unique h

/-- Transfer the constant orientation supplied by the o-minimal
orientation theorem on the regular locus of the specified contraction.
The additional exceptional set comes from 3.32 for the determinant. -/
theorem orientation_of_residue_contraction {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) (hO : IsOrderConvex O) {L : Language} [L.Structure (Residue O)]
    {P : Set (Residue O)} {X : Type*} (label : X → Fin n → Residue O) (fieldDet : X → K)
    (U : Set (Fin n → Residue O)) (g : (Fin n → Residue O) → Fin n → Residue O) :
    letI := residueLinearOrder O hO
    letI := residue_isOrderedRing O hO
    letI := residueOrderTopology O hO
    IsOpen U → DefinablyConnectedDomain L U → ContinuousOn g U → LocallyInjectiveOn g U →
    (IsOpen U → DefinablyConnectedDomain L U → ContinuousOn g U → LocallyInjectiveOn g U →
      (∀ t ∈ U ∩ regularLocus g 1, 0 < (orderJacobian g t).det) ∨
        (∀ t ∈ U ∩ regularLocus g 1, (orderJacobian g t).det < 0)) →
    P.Definable L (U \ regularLocus g 1) →
    projectionDimensionWithBot (U \ regularLocus g 1) < (n : WithBot ℕ) →
    (∀ B : Set (Fin n → Residue O), P.Definable L B → interior B = ∅ → IsNowhereDense B) →
    (∃ E ⊆ U, P.Definable L E ∧ projectionDimensionWithBot E < (n : WithBot ℕ) ∧
      ∀ x, label x ∈ U \ E → ∃ d : O, (d : K) = fieldDet x ∧ IsLocalRing.residue O d = (orderJacobian g (label x)).det) →
    ∃ V ⊆ U, P.Definable L V ∧ projectionDimensionWithBot V < (n : WithBot ℕ) ∧
      ((∀ x, label x ∈ U \ V → 0 < fieldDet x) ∨ (∀ x, label x ∈ U \ V → fieldDet x < 0)) := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := residueOrderTopology O hO
  let : OrderTopology (Residue O) := ⟨rfl⟩
  intro op connected cont inj orientation ds dim tame hE
  obtain ⟨E,sub,de,dimE,val⟩ := hE
  let S := U \ regularLocus g 1
  let V := S ∪ E
  have thin := (tame S ds (dimensionWithBot_lt_arity_iff.mp dim)).union (tame E de (dimensionWithBot_lt_arity_iff.mp dimE))
  have good {t} (ht : t ∈ U \ V) : t ∈ U ∩ regularLocus g 1 ∧ t ∈ U \ E :=
    ⟨⟨ht.1,by_contra (fun no => ht.2 (Or.inl ⟨ht.1,no⟩))⟩,⟨ht.1,fun e => ht.2 (Or.inr e)⟩⟩
  refine ⟨V,union_subset sdiff_subset sub,ds.union de,dimensionWithBot_lt_arity_iff.mpr
    (eq_empty_of_subset_empty ((interior_mono subset_closure).trans thin.subset)),?_⟩
  rcases orientation op connected cont inj with pos | neg
  · left; intro x hx
    obtain ⟨d,he,hr⟩ := val x (good hx).2
    have h := pos _ (good hx).1
    rw [←hr,←(IsLocalRing.residue O).map_zero] at h
    exact he ▸ ((residue_lt_residue_iff O hO).mp h).1
  · right; intro x hx
    obtain ⟨d,he,hr⟩ := val x (good hx).2
    have h := neg _ (good hx).1
    rw [←hr,←(IsLocalRing.residue O).map_zero] at h
    exact he ▸ ((residue_lt_residue_iff O hO).mp h).1

end GeneralizedEuler.Section3
