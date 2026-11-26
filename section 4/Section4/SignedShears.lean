module

public import Section4.ReductInvariance
public import Section2.RVSplitCoordinates
import all Section2.RVSplitCoordinates

/-! A change of positive value section acts on the whole signed RV sort.
Using two sections lets the same order comparison handle both signs and zero. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} (S T : RVValueSection O)

def changeSection (x : RV0 O) : RV0 O :=
  T.join (RVValueSection.valueCoordinate x) (S.residueCoordinate x)

theorem changeSection_join (γ : O.ValueGroupˣ) (r : Residue O) :
    changeSection S T (S.join γ r) = T.join γ r := by
  by_cases h : r = 0
  · subst r; simp [changeSection]
  · rw [changeSection,S.valueCoordinate_join γ h,S.residueCoordinate_join]

def changeSectionEquiv : RV0 O ≃* RV0 O where
  toFun := changeSection S T
  invFun := changeSection T S
  left_inv x := by
    rw [← S.join_coordinates x,changeSection_join,changeSection_join]
  right_inv x := by
    rw [← T.join_coordinates x,changeSection_join,changeSection_join]
  map_mul' x y := by
    rw [← S.join_coordinates x,← S.join_coordinates y, S.join_mul,
      changeSection_join,changeSection_join,changeSection_join,← T.join_mul]

theorem changeSection_value (x : RV0 O) :
    unsignedValue O (changeSection S T x) = unsignedValue O x := by
  rw [← S.join_coordinates x,changeSection_join]
  simp [RVValueSection.join]

theorem changeSection_fixes_residue (r : Residue O) :
    changeSection S T (residueRV O r) = residueRV O r := by
  exact (congrArg (changeSection S T) (S.join_one r).symm).trans
    ((changeSection_join S T 1 r).trans (T.join_one r))

theorem changeSection_fixes_fiber {x : RV0 O}
    (h : S.representative (RVValueSection.valueCoordinate x) =
      T.representative (RVValueSection.valueCoordinate x)) : changeSection S T x = x := by
  unfold changeSection
  rw [RVValueSection.join,← h]
  exact S.join_coordinates x

theorem changeSection_order (hO : IsOrderConvex O) (x y : RV0 O) :
    (rvLinearOrder O hO).le (changeSection S T x) (changeSection S T y) ↔
      (rvLinearOrder O hO).le x y := by
  rw [← S.join_coordinates x,← S.join_coordinates y,changeSection_join,changeSection_join,
    T.join_le_join_iff_coordinates hO,S.join_le_join_iff_coordinates hO]

theorem changeSection_power (hO : IsOrderConvex O)
    (g : PositiveField K →* PositiveField K) (P : RV0 O → RV0 O)
    (agrees : AgreesWithFieldPower O g P)
    (units : ∀ x : PositiveField K, O.valuation (x : K) = 1 → O.valuation (g x : K) = 1)
    (clamp : ∀ t, ¬ IsPositiveRV O t → P t = 0)
    (p : O.ValueGroupˣ → O.ValueGroupˣ)
    (hs : ∀ γ, P (S.representative γ) = S.representative (p γ))
    (ht : ∀ γ, P (T.representative γ) = T.representative (p γ)) (x : RV0 O) :
    changeSection S T (P x) = P (changeSection S T x) := by
  let := residueLinearOrder O hO
  obtain ⟨γ,r,hx⟩ : ∃ γ r, S.join γ r = x := ⟨_,_,S.join_coordinates x⟩
  subst x
  rw [changeSection_join]
  rcases lt_or_ge 0 r with hr | hr
  · rw [S.leadingTermPower_join_positive hO agrees units p hs γ r hr,
      T.leadingTermPower_join_positive hO agrees units p ht γ r hr,changeSection_join]
  · rw [S.leadingTermPower_join_nonpositive hO P clamp γ r hr,
      T.leadingTermPower_join_nonpositive hO P clamp γ r hr]
    exact map_zero (changeSectionEquiv S T)

set_option backward.isDefEq.respectTransparency false
section Linear
variable {F : Type*} [Field F]
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

def linearValueSection : RVValueSection O where
  lift := { toFun := fun γ => (s (Additive.ofMul γ)).toMul
            map_one' := congrArg Additive.toMul (map_zero s)
            map_mul' := fun γ δ => congrArg Additive.toMul (map_add s (Additive.ofMul γ) (Additive.ofMul δ)) }
  value_lift γ := by
    have eq : v (s (Additive.ofMul γ)) = Additive.ofMul γ := DFunLike.congr_fun hs _
    rw [hv] at eq; exact congrArg Additive.toMul eq

variable (G : Submodule F (Additive O.ValueGroupˣ))
  (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker)

include hs in
theorem shearedSection_rightInverse : v.comp ((shear (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G L).toLinearMap.comp s) = LinearMap.id := by
  apply LinearMap.ext
  intro γ
  exact (shear_preserves_value (T := Additive (PositiveRV O)) v G L (s γ)).trans (DFunLike.congr_fun hs γ)

def signedShear : RV0 O ≃* RV0 O := changeSectionEquiv (linearValueSection v hv s hs)
  (linearValueSection v hv _ (shearedSection_rightInverse v s hs G L))

theorem signedShear_base (x : RV0 O) (hx : Additive.ofMul (RVValueSection.valueCoordinate x) ∈ G) :
    signedShear v hv s hs G L x = x := by
  let γ := Additive.ofMul (RVValueSection.valueCoordinate x)
  have eq : v (s γ) = γ := DFunLike.congr_fun hs γ
  have hg : v (s γ) ∈ G := eq.symm ▸ hx
  have fixed := shear_fixes_base (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ)
    v G L (t := s γ) hg
  let old := linearValueSection v hv s hs
  let new := linearValueSection v hv _ (shearedSection_rightInverse v s hs G L)
  apply changeSection_fixes_fiber old new (x := x)
  change positiveRVToRV0 O (s γ).toMul =
    positiveRVToRV0 O ((shear (T := Additive (PositiveRV O)) v G L) (s γ)).toMul
  rw [fixed]

/-- On positive leading terms the signed extension is precisely the original
linear shear. Thus its action on independent tuples is transitive. -/
theorem signedShear_positive (x : Additive (PositiveRV O)) :
    signedShear v hv s hs G L (positiveRVToRV0 O x.toMul) =
      positiveRVToRV0 O (shear (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G L x).toMul := by
  let old := linearValueSection v hv s hs
  let new := linearValueSection v hv _ (shearedSection_rightInverse v s hs G L)
  let t := positiveRVToRV0 O x.toMul
  let γ := RVValueSection.valueCoordinate t
  have hn : t ≠ 0 := by
    obtain ⟨a,ha⟩ := positiveRVToRV0_pos O x.toMul
    change positiveRVToRV0 O x.toMul ≠ 0
    rw [← ha]; exact (rv_eq_zero_iff O).not.mpr a.property.ne'
  have hvx : Additive.ofMul γ = v x := by
    rw [hv]; apply congrArg Additive.ofMul
    exact Units.ext ((RVValueSection.coe_valueCoordinate hn).trans (positiveValueMap_coe O _).symm)
  let diff := L (G.mkQ (v x))
  let d := positiveRVToRV0 O diff.val.toMul
  have hrep : new.representative γ = old.representative γ * d := by
    change positiveRVToRV0 O (shear (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G L (s (Additive.ofMul γ))).toMul = _
    rw [shear_def]
    have eq : v (s (Additive.ofMul γ)) = v x := (DFunLike.congr_fun hs _).trans hvx
    rw [eq]
    exact positiveRVToRV0_mul O _ _
  have recover : old.representative γ * residueRV O (old.residueCoordinate t) = t :=
    old.join_coordinates t
  change new.representative γ * residueRV O (old.residueCoordinate t) = _
  rw [hrep,mul_right_comm (G := RV0 O) _ d _,recover,shear_def]
  exact (positiveRVToRV0_mul O x.toMul diff.val.toMul).symm

variable {J : Language} [J.Structure K] [J.Structure (Residue O)]

/-- All positive shears over the base act by automorphisms of the canonical
signed reduct, including the clamped powers and residue operations. -/
theorem signedShear_reduct (hO : IsOrderConvex O)
    (g : F → PositiveField K →* PositiveField K) (P : F → RV0 O → RV0 O)
    (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
    (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
    (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul =
      P e (positiveRVToRV0 O x.toMul)) :
    PreservesRVReduct (canonicalStructure (L := J) O hO P) (signedShear v hv s hs G L).toEquiv := by
  let old := linearValueSection v hv s hs
  let new := linearValueSection v hv _ (shearedSection_rightInverse v s hs G L)
  apply preserves_canonical_reduct O hO P _ (changeSection_fixes_residue old new) _
    (changeSection_value old new) (changeSection_order old new hO)
  intro e t
  apply changeSection_power old new hO (g e) (P e) (agrees e) (units e) (clamp e)
    (fun γ => (e • Additive.ofMul γ).toMul) _ _ t
  · intro γ
    exact (powers e _).symm.trans
      (congrArg (fun x : Additive (PositiveRV O) => positiveRVToRV0 O x.toMul) (s.map_smul e _).symm)
  · intro γ
    let s' := (shear (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G L).toLinearMap.comp s
    exact (powers e _).symm.trans
      (congrArg (fun x : Additive (PositiveRV O) => positiveRVToRV0 O x.toMul) (s'.map_smul e _).symm)
end Linear

end GeneralizedEuler.Section4
