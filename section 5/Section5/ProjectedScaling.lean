module

public import Section5.ProjectedFieldSplitting
public import Section5.RestoreCoordinates

/-! Lift a contracted bijection on two injectively projected pieces. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Two selections of the same size omit the same number of coordinates. -/
def omittedEquiv (p q : Fin k ↪ Fin n) : Omitted p ≃ Omitted q := by
  classical
  apply Fintype.equivOfCardEq
  simp only [Omitted, Fintype.card_compl_set, Fintype.card_range]

variable {U V : Set (labelAssignment n (CanonicalSort O))}
  (p q : Fin k ↪ Fin n) (e : U ≃ V)
  (hp : Set.InjOn (projectLabels p) U) (hq : Set.InjOn (projectLabels q) V)
  (A : fieldLiftDomain (canonicalStructure (L := L) O hO power) (projectLabels p '' U) → fieldLiftDomain (canonicalStructure (L := L) O hO power) U)
  (B : fieldLiftDomain (canonicalStructure (L := L) O hO power) (projectLabels q '' V) → fieldLiftDomain (canonicalStructure (L := L) O hO power) V)
  (hA : ∀ a, projectFields p (A a).val = a.val)
  (hB : ∀ b, projectFields q (B b).val = b.val)
  (nonzeroA : ∀ a (i : Omitted p), (A a).val .vf i.val ≠ 0)
  (nonzeroB : ∀ b (i : Omitted q), (B b).val .vf i.val ≠ 0)
  (f : fieldLiftDomain (canonicalStructure (L := L) O hO power) (projectLabels p '' U) ≃ fieldLiftDomain (canonicalStructure (L := L) O hO power) (projectLabels q '' V))

private def reindexOmitted (r : Omitted p ≃ Omitted q)
    (c : Omitted q → K) :
    {x : Omitted p → K // ∀ j, rv O (x j) = rv O (c (r j))} ≃
      {y : Omitted q → K // ∀ j, rv O (y j) = rv O (c j)} where
  toFun x := ⟨fun j => x.val (r.symm j),by
    intro j
    exact (x.property (r.symm j)).trans (congrArg (rv O ∘ c) (r.apply_symm_apply j))⟩
  invFun y := ⟨fun j => y.val (r j),fun j => y.property (r j)⟩
  left_inv x := by exact Subtype.ext (funext fun j => congrArg x.val (r.symm_apply_apply j))
  right_inv y := by exact Subtype.ext (funext fun j => congrArg y.val (r.apply_symm_apply j))

include hA hB nonzeroA nonzeroB in
/-- Restore deleted coordinates by a diagonal field scaling, using the
projected lift on the retained tuple. -/
theorem lift_projected_by_scaling
    (hf : ∀ x, liftedLabel (projectLabels q '' V) (f x) =
      projectedLabelEquiv e p q hp hq (liftedLabel (projectLabels p '' U) x)) :
    ∃ lift : fieldLiftDomain 𝓜 U ≃ fieldLiftDomain 𝓜 V,
      (∀ x, liftedLabel V (lift x) = e (liftedLabel U x)) ∧
      (∀ x, projectFieldLift q (lift x) = f (projectFieldLift p x)) ∧
      ∀ x (i : Omitted p),
        (lift x).val .vf (omittedEquiv p q i).val =
          (B (f (projectFieldLift p x))).val .vf (omittedEquiv p q i).val *
            x.val .vf i.val / (A (projectFieldLift p x)).val .vf i.val := by
  let P := splitProjectedFieldLift p A hA hp
  let Q := splitProjectedFieldLift q B hB hq
  let r := omittedEquiv p q
  let a (x : fieldLiftDomain 𝓜 (projectLabels p '' U)) (j : Omitted p) := (A x).val .vf j.val
  let b (y : fieldLiftDomain 𝓜 (projectLabels q '' V)) (j : Omitted q) := (B y).val .vf j.val
  let preScaled (x : fieldLiftDomain 𝓜 (projectLabels p '' U)) :
      omittedFieldFiber p A x ≃ {z : Omitted p → K // ∀ j, rv O (z j) = rv O (a x j)} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [canonicalStructure_rvMap, a])
  let postScaled (y : fieldLiftDomain 𝓜 (projectLabels q '' V)) :
      {z : Omitted q → K // ∀ j, rv O (z j) = rv O (b y j)} ≃ omittedFieldFiber q B y :=
    Equiv.subtypeEquivRight (fun _ => by simp only [canonicalStructure_rvMap, b])
  let F (x : fieldLiftDomain 𝓜 (projectLabels p '' U)) :
      omittedFieldFiber p A x ≃ omittedFieldFiber q B (f x) :=
    (preScaled x).trans
      ((scaleFibers O (a x) (b (f x) ∘ r) (nonzeroA x) (fun j => nonzeroB (f x) (r j))).trans
        ((reindexOmitted O p q r (b (f x))).trans (postScaled (f x))))
  let lift := P.trans ((Equiv.sigmaCongr f F).trans Q.symm)
  have retain (x : fieldLiftDomain 𝓜 U) :
      projectFieldLift q (lift x) = f (projectFieldLift p x) := by
    have e₁ := Q.apply_symm_apply ((Equiv.sigmaCongr f F) (P x))
    have e₂ : (Q (lift x)).1 = f (P x).1 := congrArg Sigma.fst e₁
    rw [splitProjectedFieldLift_retained, splitProjectedFieldLift_retained] at e₂
    exact e₂
  refine ⟨lift,?_,retain,?_⟩
  · intro x
    apply Subtype.ext
    apply hq (lift x).property (e (liftedLabel U x)).property
    rw [← projectFields_fieldLead]
    change (liftedLabel (projectLabels q '' V) (projectFieldLift q (lift x))).val = _
    rw [retain, hf]
    have hSrc : liftedLabel (projectLabels p '' U) (projectFieldLift p x) =
        ⟨projectLabels p (liftedLabel U x).val,Set.mem_image_of_mem _ (liftedLabel U x).property⟩ :=
      Subtype.ext (projectFields_fieldLead p x.val)
    rw [hSrc, projectedLabelEquiv_apply]
  · intro x j
    let x' := (P x).1
    let z := F x' (P x).2
    change (Q.symm ⟨f x',z⟩).val .vf (r j).val = _
    rw [splitProjectedFieldLift_symm_field, mergeCoordinates_omitted]
    change (scaleFibers O (a x') (b (f x') ∘ r) (nonzeroA x')
      (fun j => nonzeroB (f x') (r j)) (preScaled x' (P x).2)).val (r.symm (r j)) = _
    rw [r.symm_apply_apply, scaleFibers_apply]
    change b (f x') (r j) * (P x).2.val j / a x' j = _
    rw [splitProjectedFieldLift_omitted]
    rw [show x' = projectFieldLift p x from splitProjectedFieldLift_retained p A hA hp x]

end GeneralizedEuler.Section5
