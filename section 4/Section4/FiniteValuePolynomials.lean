module

public import Section4.TaggedValueClasses
public import Section4.GradedEulerMaps
public import Section4.EulerRetractions
public import Section4.ResidueClasses
import all Section4.EulerRetractions
import all Section4.ValueScissors
import all Section4.ResidueClasses

/-! Finite value classes by cardinality and degree, and the graded and
ungraded scalar maps of Remark 4.15. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject Polynomial
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} {J : Language} [J.Structure V] (A : Set V) (a : V)
  (ha : A.Definable J ({fun _ => a} : Set (Fin 1 → V)))

include ha in
theorem constant_value_point_definable (k : ℕ) : A.Definable J ({fun _ => a} : Set (Fin k → V)) := by
  convert Set.definable_iInter_of_finite (fun i : Fin k => ha.preimage_comp (fun _ : Fin 1 => i)) using 1
  ext x
  simp [funext_iff,Function.comp_def]

include ha in
theorem constant_value_point_class (k : ℕ) :
    pieceClass _ (constant_value_point_definable A a ha k) = (pieceClass _ ha)^k := by
  induction k with
  | zero => rw [pow_zero]; exact pieceClass_degree_zero _ _
  | succ k ih =>
    have eq : cartesian ({fun _ => a} : Set (Fin k → V)) ({fun _ => a} : Set (Fin 1 → V)) =
        ({fun _ => a} : Set (Fin (k+1) → V)) := by
      ext x
      change (_ = _ ∧ _ = _) ↔ x = _
      constructor
      · rintro ⟨l,r⟩
        funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j with
        | inl t => exact congrFun l t
        | inr t => exact congrFun r t
      · rintro rfl; exact ⟨rfl,rfl⟩
    have prod := pieceClass_product (constant_value_point_definable A a ha k) ha
    rw [pow_succ,← ih,← prod]
    congr 1
    exact eq.symm

include ha in
theorem finite_value_piece_class {k} (D : Set (Fin k → V)) (hd : A.Definable J D) (fin : D.Finite)
    (point : ∀ (E : Set (Fin k → V)), A.Definable J E → E.Nonempty → ∃ x ∈ E, A.Definable J ({x} : Set _)) :
    pieceClass D hd = D.ncard • (pieceClass _ ha)^k := by
  classical
  induction hn : D.ncard using Nat.strong_induction_on generalizing D with
  | h n ih =>
    rcases D.eq_empty_or_nonempty with rfl | ne
    · simp only [Set.ncard_empty] at hn
      subst n; simp [pieceClass_empty]
    obtain ⟨x,hx,dx⟩ := point D hd ne
    let E := D \ {x}
    have de : A.Definable J E := hd.inter dx.compl
    have ef : E.Finite := fin.subset Set.sdiff_subset
    have small : E.ncard < n := hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hx fin
    have sum := pieceClass_cut dx de (Set.disjoint_sdiff_right : Disjoint {x} E)
    have un : {x} ∪ E = D := by
      dsimp [E]; grind
    have rest := ih E.ncard small E de ef rfl
    have card : E.ncard + 1 = n := (Set.ncard_sdiff_singleton_add_one hx fin).trans hn
    let U := ({fun _ => a} : Set (Fin k → V))
    have du := constant_value_point_definable A a ha k
    have single : pieceClass {x} dx = pieceClass U du := by
      let e : ({x} : Set (Fin k → V)) ≃ U :=
        { toFun := fun _ => ⟨_,rfl⟩
          invFun := fun _ => ⟨_,rfl⟩
          left_inv := fun y => Subtype.ext y.property.symm
          right_inv := fun y => Subtype.ext y.property.symm }
      apply pieceClass_iso _ _ e
      convert (dx.preimage_comp Sum.inl).inter (du.preimage_comp Sum.inr) using 1
      ext w
      exact ⟨fun ⟨y,l,r⟩ => ⟨l.symm.trans y.property,r.symm.trans (e y).property⟩,
        fun ⟨l,r⟩ => ⟨⟨_,l⟩,rfl,show (fun _ => a) = _ from r.symm⟩⟩
    rw [single,constant_value_point_class A a ha k,rest] at sum
    rw [← card,add_nsmul,one_nsmul,add_comm,← sum]
    congr 1
    exact un.symm

theorem graded_finite_scalar_injective {R : Type*} [CommSemiring R] (t : R)
    (χ : R →+* Polynomial ℤ) (ht : χ t = -X) :
    Function.Injective (eval₂RingHom (Nat.castRingHom R) t : Polynomial ℕ →+* R) := by
  let f := eval₂RingHom (Nat.castRingHom R) t
  have eq : signTwist.toRingHom.comp (χ.comp f) = mapRingHom (Nat.castRingHom ℤ) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [f]
    · simp [f,ht,signTwist]
  intro x y h
  apply map_injective (Nat.castRingHom ℤ) Nat.cast_injective
  exact (DFunLike.congr_fun eq x).symm.trans
    ((congrArg (fun z => signTwist (χ z)) h).trans (DFunLike.congr_fun eq y))

/-- In the ungraded residue semiring, a point plus an open line has
dimension one and Euler characteristic zero, so it equals its double. -/
theorem ungraded_finite_scalar_not_injective :
    ¬ Function.Injective (eval₂RingHom (Nat.castRingHom ResidueClass)
      (.inhabited 1 (-1) (by decide)) : Polynomial ℕ →+* ResidueClass) := by
  let f := eval₂RingHom (Nat.castRingHom ResidueClass) (.inhabited 1 (-1) (by decide))
  let p : Polynomial ℕ := 1 + X
  have zeroEuler : f p = ResidueClass.inhabited 1 0 (by decide) := by
    simp [p,f]; rfl
  intro inj
  have eq : f (p+p) = f p := by rw [map_add,zeroEuler]; rfl
  have co := congrArg (fun q : Polynomial ℕ => q.coeff 0) (inj eq)
  simp [p] at co

end GeneralizedEuler.Section4
