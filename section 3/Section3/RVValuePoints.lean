module

public import Section3.DefinablePoints
public import Section2.SignedValue
public import Section2.ResidueOrder
import all Section2.SignedValue

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Cardinal Set
universe u

variable {X : Type u}

/-- Exchange eliminates a finite family of imaginary parameters if every
representative fiber is larger than the definable closure of a small set.
The induction permits the base already to include arbitrary representatives. -/
theorem remove_large_fiber_parameters (cl : Set X → Set X) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (small : ∀ B : Set X, #B ≤ μ → #(cl B) ≤ μ)
    (exchange : ∀ (B : Set X) (x y : X), x ∈ cl (insert y B) → x ∉ cl B → y ∈ cl (insert x B))
    {n : ℕ} (D : Fin n → Set X) (large : ∀ i, μ < #(D i))
    (B : Set X) (hB : #B ≤ μ) (x : X)
    (named : ∀ z : Fin n → X, (∀ i, z i ∈ D i) → x ∈ cl (B ∪ range z)) : x ∈ cl B := by
  classical
  induction n generalizing B with
  | zero => simpa using named Fin.elim0 (fun j => j.elim0)
  | succ n ih =>
    have bound (y : X) : #(insert y B : Set X) ≤ μ :=
      mk_insert_le.trans (Cardinal.add_le_of_le hμ hB (one_le_aleph0.trans hμ))
    have step (y : X) (hy : y ∈ D 0) : x ∈ cl (insert y B) := by
      apply ih (fun i => D i.succ) (fun i => large i.succ) _ (bound y)
      intro z hz
      have h := named (Fin.cons y z) (Fin.cases hy hz)
      simpa [Fin.range_cons,union_insert,insert_union] using h
    by_contra outside
    have sub : D 0 ⊆ cl (insert x B) := fun y hy => exchange B x y (step y hy) outside
    exact (large 0).not_ge ((mk_le_mk_of_subset sub).trans (small _ (bound x)))

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- A positive residue multiplies an RV representative without changing
its signed value. Thus each nonzero signed-value fiber has at least the
cardinality of the positive residue field. -/
theorem signedValue_fiber_card (t : RV O) :
    letI := residueLinearOrder O hO
    #(Ioi (0 : Residue O)) ≤ #({z : RV0 O | signedValue O hO z = signedValue O hO (t : RV0 O)}) := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := rvLinearOrder O hO
  have hp (r : Ioi (0 : Residue O)) : 0 < residueRV O r := by
    simpa only [residueRV_zero] using residueRV_strictMono O hO r.property
  have one (r : Ioi (0 : Residue O)) : signedValue O hO (residueRV O r) = 1 := by
    obtain ⟨w,hw⟩ := WithZero.ne_zero_iff_exists.mp (hp r).ne'
    have hker := (signedValueUnit_eq_one_iff O hO w).mpr ⟨hw ▸ hp r,hw ▸ unsignedValue_residueRV_of_ne_zero O r.property.ne'⟩
    rw [←hw,signedValue,WithZero.map'_coe,hker,WithZero.coe_one]
  let F (r : Ioi (0 : Residue O)) : {z : RV0 O | signedValue O hO z = signedValue O hO (t : RV0 O)} :=
    ⟨(t : RV0 O) * residueRV O r,by change signedValue O hO _ = _; rw [map_mul,one,mul_one]⟩
  apply mk_le_of_injective (f := F)
  intro r s h
  exact Subtype.ext (residueRV_injective O (rv_mul_left_cancel O (show (t : RV0 O) ≠ 0 from WithZero.coe_ne_zero) (congrArg Subtype.val h)))

/-- The RV assertion of 3.6. The base field names stay fixed. A point
definable over a tuple of signed values is definable over the original
two sorts. The two model inputs are RV exchange (2.27) and smallness of
definable closure in the ambient saturated model. -/
theorem rv_point_over_signed_values {L : Language} {E : Type*}
    (M : SortedStructure L E (CanonicalSort O)) (P : Set K) (B : Set (RV0 O))
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hB : #B ≤ μ) {n : ℕ} (t : Fin n → RV O) (x : RV0 O) :
    letI := residueLinearOrder O hO
    let cl (W : Set (RV0 O)) := {y | SortedDefinableOver M (fun s => match s with
      | .vf => P | .rv => W) {v : ∀ s, RVVariables Unit s → CanonicalSort O s | v .rv () = y}}
    μ < #(Ioi (0 : Residue O)) → (∀ W : Set (RV0 O), #W ≤ μ → #(cl W) ≤ μ) →
    (∀ (W : Set (RV0 O)) (a b : RV0 O), a ∈ cl (insert b W) → a ∉ cl W → b ∈ cl (insert a W)) →
    (∀ z : Fin n → RV0 O, (∀ i, signedValue O hO (z i) = signedValue O hO (t i : RV0 O)) →
      x ∈ cl (B ∪ range z)) → x ∈ cl B := by
  let := residueLinearOrder O hO
  intro cl big small exchange named
  exact remove_large_fiber_parameters cl hμ small exchange
    (fun i => {z : RV0 O | signedValue O hO z = signedValue O hO (t i : RV0 O)})
    (fun i => big.trans_le (signedValue_fiber_card O hO (t i))) B hB x named

end GeneralizedEuler.Section3
