module

public import Section2.VFLiftSubstructure

/-! Agreement with the old RV embedding in the new-value case of
Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {L : Language.{u, v}} {E : Type w} [L.Structure K] [L.Structure F]
  {O : ValuationSubring K} {Q : ValuationSubring F}
  [L.Structure (Residue O)] [L.Structure (Residue Q)]
  {hO : IsOrderConvex O} {hQ : IsOrderConvex Q}
  {P : E → RV0 O → RV0 O} {PQ : E → RV0 Q → RV0 Q}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO P)}
  (old : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))
  {H : Type*} [MulZeroOneClass H] (source : H →*₀ RV0 O) (target : H →*₀ RV0 Q)

/-- The intermediate leading term has its source image in the old RV
substructure and the old map sends that image to its target image. -/
def RVMapsAgree (x : H) : Prop :=
  ∃ hx : source x ∈ S.carrier .rv, old.toEmbedding .rv ⟨source x, hx⟩ = target x

theorem RVMapsAgree.zero : RVMapsAgree old source target 0 := by
  let z := S.structureOn.funMap (.rvZero : FunctionSymbol L E [] .rv) (fun i => i.elim0)
  have hz : (z : RV0 O) = source 0 := (map_zero source).symm
  refine ⟨hz ▸ z.property, ?_⟩
  have hz' : (⟨source 0, hz ▸ z.property⟩ : S.carrier .rv) = z := Subtype.ext hz.symm
  rw [hz', map_zero target]
  exact old.map_fun .rvZero (fun i => i.elim0)

variable {old source target}

theorem RVMapsAgree.mul {x y : H}
    (hx : RVMapsAgree old source target x) (hy : RVMapsAgree old source target y) :
    RVMapsAgree old source target (x * y) := by
  obtain ⟨hx, hxe⟩ := hx
  obtain ⟨hy, hye⟩ := hy
  let a : SortedArgs (fun s => S.carrier s) [.rv, .rv] :=
    Fin.cases ⟨source x, hx⟩ (fun j => by
      have hj : j = 0 := Fin.fin_one_eq_zero (j : Fin 1)
      subst j
      exact ⟨source y, hy⟩)
  let z := S.structureOn.funMap (.rvMul : FunctionSymbol L E [.rv, .rv] .rv) a
  have hz : (z : RV0 O) = source (x * y) := (map_mul source x y).symm
  refine ⟨hz ▸ z.property, ?_⟩
  have hz' : (⟨source (x * y), hz ▸ z.property⟩ : S.carrier .rv) = z := Subtype.ext hz.symm
  rw [hz', map_mul target]
  have h := old.map_fun .rvMul a
  change old.toEmbedding .rv z =
    old.toEmbedding .rv ⟨source x, hx⟩ * old.toEmbedding .rv ⟨source y, hy⟩ at h
  rw [hxe, hye] at h
  exact h

theorem RVMapsAgree.power (p : E → H → H) (e : E) {x : H}
    (hsource : source (p e x) = P e (source x))
    (htarget : target (p e x) = PQ e (target x))
    (hx : RVMapsAgree old source target x) : RVMapsAgree old source target (p e x) := by
  obtain ⟨hx, hxe⟩ := hx
  let a : SortedArgs (fun s => S.carrier s) [.rv] := fun j => by
    have hj : j = 0 := Fin.fin_one_eq_zero (j : Fin 1)
    subst j
    exact ⟨source x, hx⟩
  let z := S.structureOn.funMap (.power e : FunctionSymbol L E [.rv] .rv) a
  have hz : (z : RV0 O) = source (p e x) := hsource.symm
  refine ⟨hz ▸ z.property, ?_⟩
  have hz' : (⟨source (p e x), hz ▸ z.property⟩ : S.carrier .rv) = z := Subtype.ext hz.symm
  rw [hz', htarget]
  have h := old.map_fun (.power e) a
  change old.toEmbedding .rv z = PQ e (old.toEmbedding .rv ⟨source x, hx⟩) at h
  rw [hxe] at h
  exact h

/-- For a new-value adjunction, agreement on the old coefficients and on
the chosen generator implies agreement on every leading term in its
given monomial normal form. -/
theorem RVMapsAgree.of_monomials (p : E → H → H) (W : Set H) (t : H)
    (hsource : ∀ e, source (p e t) = P e (source t))
    (htarget : ∀ e, target (p e t) = PQ e (target t))
    (hW : ∀ w ∈ W, RVMapsAgree old source target w)
    (ht : RVMapsAgree old source target t)
    (hnormal : ∀ x : H, x ≠ 0 → ∃ w ∈ W, ∃ e : E, x = w * p e t) :
    ∀ x : H, RVMapsAgree old source target x := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact RVMapsAgree.zero old source target
  · obtain ⟨w, hw, e, rfl⟩ := hnormal x hx
    exact (hW w hw).mul (ht.power p e (hsource e) (htarget e))

/-- Agreement on the intermediate leading terms gives the sorted lift
with the specified VF embedding and exactly the old RV map. -/
theorem exists_vfLift_of_RV_agreement
    (B : L.Substructure K) (field : B ↪[L] F) (rep : B → H)
    (hs : ∀ x, source (rep x) = rv O x.val) (ht : ∀ x, target (rep x) = rv Q (field x))
    (ha : ∀ x, RVMapsAgree old source target (rep x)) :
    ∃ (hB : ∀ x ∈ B, rv O x ∈ S.carrier .rv)
      (j : SortedEmbedding (enlargeVF O hO P S B hB).structureOn
        (canonicalStructure (L := L) Q hQ PQ)),
      (∀ x : B, (j.toEmbedding .vf).toFun x = field x) ∧
      (∀ t : S.carrier .rv, (j.toEmbedding .rv).toFun t = old.toEmbedding .rv t) := by
  have hB (x : K) (hx : x ∈ B) : rv O x ∈ S.carrier .rv := by
    obtain ⟨h, _⟩ := ha ⟨x, hx⟩
    exact hs ⟨x, hx⟩ ▸ h
  have hcomm (x : B) : old.toEmbedding .rv ⟨rv O x.val, hB x x.property⟩ = rv Q (field x) := by
    obtain ⟨hm, he⟩ := ha x
    have hx : (⟨rv O x.val, hB x x.property⟩ : S.carrier .rv) =
        ⟨source (rep x), hm⟩ := Subtype.ext (hs x).symm
    rw [hx, he, ht]
  let j := liftVFEmbedding O hO P Q hQ PQ S B hB old field hcomm
  exact ⟨hB, j, liftVFEmbedding_vf_apply O hO P Q hQ PQ S B hB old field hcomm,
    liftVFEmbedding_rv_apply O hO P Q hQ PQ S B hB old field hcomm⟩

end GeneralizedEuler.Section2
