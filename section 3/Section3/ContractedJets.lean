module

public import Section3.AdjacentCharts
public import Section3.ValueChartLocus
public import Mathlib.Order.Interval.Finset.Nat
import all Section3.AdjacentCharts
import all Section2.ResidueTopology

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set Filter
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) (hO : IsOrderConvex O) {n : ℕ}

private theorem pred_le (q : Fin n → ℕ) (i : Fin n) : Function.update q i (q i - 1) ≤ q := by
  intro j
  by_cases same : j = i
  · subst j; simp
  · simp [Function.update_of_ne same]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem residue_update (a : Fin n → O) (i : Fin n) (y : O) :
    (IsLocalRing.residue O) ∘ Function.update a i y =
      Function.update ((IsLocalRing.residue O) ∘ a) i (IsLocalRing.residue O y) := by
  ext j
  by_cases same : j = i
  · subst j; simp
  · simp [Function.update_of_ne same]

/-- Uniform open set of Lemma 3.31. The field hypotheses are the finite
unary mean-value partitions for consecutive jets. The residue hypotheses
are finite output values, definability of value equality, and continuous
first derivatives of the given contractions in their nonzero charts. -/
theorem contracted_jets_on_open_value_locus {L : Language} [L.Structure (Residue O)] {P : Set (Residue O)}
    (F : OrderedFieldTerms L) (p : Fin n → ℕ) (A : Set (Fin n → Residue O))
    (f : (Fin n → ℕ) → (Fin n → O) → K) (R : (Fin n → ℕ) → (Fin n → Residue O) → RV0 O)
    (dA : P.Definable L A) (contract : ∀ q ≤ p, ∀ a, (IsLocalRing.residue O) ∘ a ∈ A →
      rv O (f q a) = R q ((IsLocalRing.residue O) ∘ a))
    (base : ∀ a, (IsLocalRing.residue O) ∘ a ∈ A → f 0 a ∈ O)
    (fin : ∀ q ≤ p, ((unsignedValue O) ∘ R q '' A).Finite)
    (defEq : ∀ q ≤ p, P.Definable L {w : Fin n ⊕ Fin n → Residue O |
      unsignedValue O (R q (w ∘ Sum.inl)) = unsignedValue O (R q (w ∘ Sum.inr))}) :
    letI := residueLinearOrder O hO
    letI := residueOrderTopology O hO
    InterpretsOrderedFieldTerms (A := Residue O) F →
    (∀ S : Set (Fin n → Residue O), (univ : Set (Residue O)).Definable L S → IsNowhereDense (frontier S)) →
    (∀ q ≤ p, ∀ i, q i ≠ 0 → ∀ (a : Fin n → O) l u,
      MapsTo (Function.update ((IsLocalRing.residue O) ∘ a) i) (Ioo l u) A →
      PiecewiseSliceMVT O (Ioo l u) (fun y => f (Function.update q i (q i-1)) (Function.update a i y))
        (fun y => f q (Function.update a i y))) →
    (∀ q ≤ p, ∀ (a : Fin n → O) i l u,
      MapsTo (Function.update ((IsLocalRing.residue O) ∘ a) i) (Ioo l u) A →
      SmoothSliceChart O hO (Ioo l u) (fun y => f q (Function.update a i y))
        (fun s => R q (Function.update ((IsLocalRing.residue O) ∘ a) i s))) →
    ∃ W ⊆ A, P.Definable L W ∧ P.Definable L (A \ W) ∧ IsOpen W ∧
      projectionDimensionWithBot (A \ W) < (n : WithBot ℕ) ∧
      (∀ t ∈ W, ∀ q ≤ p, ∀ᶠ u in 𝓝 t, unsignedValue O (R q u) = unsignedValue O (R q t)) ∧
      ∀ a, (IsLocalRing.residue O) ∘ a ∈ W →
        (∀ q ≤ p, f q a ∈ O) ∧
        ∀ q ≤ p, ∀ i, q i ≠ 0 →
          let j := Function.update q i (q i - 1)
          let t := (IsLocalRing.residue O) ∘ a
          AdjacentComparison O hO (fun y => f j (Function.update a i y))
            (fun y => f q (Function.update a i y)) (fun s => R j (Function.update t i s)) (a i) ∧
          HasOrderDerivativeAt (fun s => rvResidue O (R j (Function.update t i s))) (t i) (rvResidue O (R q t)) := by
  classical
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := residueOrderTopology O hO
  let : OrderTopology (Residue O) := ⟨rfl⟩
  intro hF tame mvt smooth
  let J := {q : Fin n → ℕ // q ≤ p}
  let : Finite J := Finite.of_injective (fun q : J => fun i : Fin n => (⟨q.val i,Nat.lt_succ_of_le (q.property i)⟩ : Fin (p i+1))) (by
    intro a b h; exact Subtype.ext (funext (fun i => congrArg Fin.val (congrFun h i))))
  let v (j : J) := (unsignedValue O) ∘ R j.val
  obtain ⟨W,sub,dW,dE,op,dim,localVal⟩ := definable_value_chart_locus F hF A dA v
    (fun j => fin j.val j.property) (fun j => defEq j.val j.property) tame
  refine ⟨W,sub,dW,dE,op,dim,fun t ht q hq => localVal t ht ⟨q,hq⟩,?_⟩
  intro a ha
  let t := (IsLocalRing.residue O) ∘ a
  have adj (q) (hq : q ≤ p) (i) (hi : q i ≠ 0) :
      AdjacentComparison O hO (fun y => f (Function.update q i (q i-1)) (Function.update a i y))
        (fun y => f q (Function.update a i y)) (fun s => R (Function.update q i (q i-1)) (Function.update t i s)) (a i) := by
    let j := Function.update q i (q i-1)
    have hj : j ≤ p := (pred_le q i).trans hq
    let Q : J := ⟨q,hq⟩
    let J' : J := ⟨j,hj⟩
    have cont : Continuous (Function.update t i) := continuous_pi (fun k => by
      by_cases same : k = i
      · subst k; simp only [Function.update_self]; exact continuous_id
      · simpa only [Function.update_of_ne same] using (continuous_const : Continuous (fun _ : Residue O => t k)))
    have tend : Tendsto (Function.update t i) (𝓝 (t i)) (𝓝 t) := by
      simpa only [Function.update_eq_self] using (cont.continuousAt (x := t i)).tendsto
    have hmem : ∀ᶠ z in 𝓝 t, z ∈ W := op.mem_nhds ha
    have ev := tend.eventually ((hmem.and (localVal t ha Q)).and (localVal t ha J'))
    obtain ⟨l,u,center,box⟩ := mem_nhds_iff_exists_Ioo_subset.mp ev
    have maps : MapsTo (Function.update t i) (Ioo l u) A := fun _ hs => sub (box hs).1.1
    have cg (k) (hk : k ≤ p) (y : O) (hy : IsLocalRing.residue O y ∈ Ioo l u) :
        rv O (f k (Function.update a i y)) = R k (Function.update t i (IsLocalRing.residue O y)) := by
      rw [←residue_update]; exact contract k hk _ (by rw [residue_update]; exact maps hy)
    have value (k : J) (hc : ∀ s ∈ Ioo l u, v k (Function.update t i s) = v k t) :
        SingleSliceValue O (Ioo l u) (fun y => f k.val (Function.update a i y)) := by
      intro x y hx hy
      simpa only [v, Function.comp_apply, ←cg k.val k.property x hx, ←cg k.val k.property y hy,unsignedValue_rv]
        using (hc _ hx).trans (hc _ hy).symm
    exact adjacent_comparison_on_slice O hO _ _ _ _ (cg j hj) (cg q hq)
      (value J' (fun _ hs => (box hs).2)) (value Q (fun _ hs => (box hs).1.2))
      (mvt q hq i hi a l u maps) (smooth j hj a i l u maps) (smooth q hq a i l u maps)
      isOpen_Ioo _ center
  have integ : ∀ q ≤ p, f q a ∈ O := by
    apply all_partials_of_adjacent p (fun q => f q a ∈ O) (base a (sub ha))
    intro q hq i hi prev
    have hg := (adj q hq i hi).2.2
    simp only [Function.update_eq_self] at hg
    exact (hg prev).1
  refine ⟨integ,fun q hq i hi => ⟨adj q hq i hi,?_⟩⟩
  let j := Function.update q i (q i-1)
  have hg := (adj q hq i hi).2.2
  simp only [Function.update_eq_self] at hg
  have hd := (hg (integ j ((pred_le q i).trans hq))).2
  rw [←contract q hq a (sub ha),rvResidue_rv]
  exact hd

/-- The adjacent comparisons and residue identities without the additional
value-neighborhoods provided by the chart construction. -/
theorem contracted_jets_on_open_locus {L : Language} [L.Structure (Residue O)] {P : Set (Residue O)}
    (F : OrderedFieldTerms L) (p : Fin n → ℕ) (A : Set (Fin n → Residue O))
    (f : (Fin n → ℕ) → (Fin n → O) → K) (R : (Fin n → ℕ) → (Fin n → Residue O) → RV0 O)
    (dA : P.Definable L A) (contract : ∀ q ≤ p, ∀ a, (IsLocalRing.residue O) ∘ a ∈ A →
      rv O (f q a) = R q ((IsLocalRing.residue O) ∘ a))
    (base : ∀ a, (IsLocalRing.residue O) ∘ a ∈ A → f 0 a ∈ O)
    (fin : ∀ q ≤ p, ((unsignedValue O) ∘ R q '' A).Finite)
    (defEq : ∀ q ≤ p, P.Definable L {w : Fin n ⊕ Fin n → Residue O |
      unsignedValue O (R q (w ∘ Sum.inl)) = unsignedValue O (R q (w ∘ Sum.inr))}) :
    letI := residueLinearOrder O hO
    letI := residueOrderTopology O hO
    InterpretsOrderedFieldTerms (A := Residue O) F →
    (∀ S : Set (Fin n → Residue O), (univ : Set (Residue O)).Definable L S → IsNowhereDense (frontier S)) →
    (∀ q ≤ p, ∀ i, q i ≠ 0 → ∀ (a : Fin n → O) l u,
      MapsTo (Function.update ((IsLocalRing.residue O) ∘ a) i) (Ioo l u) A →
      PiecewiseSliceMVT O (Ioo l u) (fun y => f (Function.update q i (q i-1)) (Function.update a i y))
        (fun y => f q (Function.update a i y))) →
    (∀ q ≤ p, ∀ (a : Fin n → O) i l u,
      MapsTo (Function.update ((IsLocalRing.residue O) ∘ a) i) (Ioo l u) A →
      SmoothSliceChart O hO (Ioo l u) (fun y => f q (Function.update a i y))
        (fun s => R q (Function.update ((IsLocalRing.residue O) ∘ a) i s))) →
    ∃ W ⊆ A, P.Definable L W ∧ P.Definable L (A \ W) ∧ IsOpen W ∧
      projectionDimensionWithBot (A \ W) < (n : WithBot ℕ) ∧
      ∀ a, (IsLocalRing.residue O) ∘ a ∈ W →
        (∀ q ≤ p, f q a ∈ O) ∧
        ∀ q ≤ p, ∀ i, q i ≠ 0 →
          let j := Function.update q i (q i - 1)
          let t := (IsLocalRing.residue O) ∘ a
          AdjacentComparison O hO (fun y => f j (Function.update a i y))
            (fun y => f q (Function.update a i y)) (fun s => R j (Function.update t i s)) (a i) ∧
          HasOrderDerivativeAt (fun s => rvResidue O (R j (Function.update t i s))) (t i) (rvResidue O (R q t)) := by
  let := residueLinearOrder O hO
  let := residueOrderTopology O hO
  intro hF tame mvt smooth
  obtain ⟨W,sub,dW,dE,op,dim,_,adj⟩ := contracted_jets_on_open_value_locus O hO F p A f R
    dA contract base fin defEq hF tame mvt smooth
  exact ⟨W,sub,dW,dE,op,dim,adj⟩

end GeneralizedEuler.Section3
