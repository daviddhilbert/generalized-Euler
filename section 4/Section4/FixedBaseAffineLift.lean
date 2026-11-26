module

public import Section4.SignedValueReflection
public import Section4.SignedRectangleFactors
public import Section4.ValuePadding
import all Section4.SignedValueGeneration
import all Section2.LeadingTerm
import all Section4.ValuePullback
import all Section4.RectangleClasses
import all Section4.CanonicalChartMaps
import all Section4.AffineLifts
import all Section4.SignedRectangleFactors
import all Section2.SortedStructure
import all Section2.RVMonomials

/-! Fixed-base lifts on a single affine piece of Lemma 4.12. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) (hO : IsOrderConvex O) {J : Language}
  [J.Structure K] [J.Structure (Residue O)] (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
local notation "model" => canonicalStructure (L := J) O hO P
local notation "lab" => signedLabel O hO
local notation "V" => Additive O.ValueGroupˣ

omit [Field F] in
/-- Multiplication by a nonzero old representative in each coordinate
restores any prescribed sign, keeping the unsigned value fixed. -/
theorem restore_sign_lift {k} (b : Fin k → SignTypeˣ) (D : Set (Fin k → V))
    (u : Fin k → S.carrier .rv) (nz : ∀ i, (u i).val ≠ 0)
    (hu : ∀ i, lab (u i).val = (b i,1))
    (hd : isRVSet model S (sharp model lab (signInsert (fun _ => (1 : SignTypeˣ)) '' D))) :
    ∃ e : sharp model lab (signInsert (fun _ => (1 : SignTypeˣ)) '' D) ≃ sharp model lab (signInsert b '' D),
      SortedDefinableOver model S.carrier (rvGraph (fun x => (e x).val)) ∧
      ∀ x i, lab ((e x).val i) = (b i,(lab (x.val i)).2) := by
  let H := sharp model lab (signInsert (fun _ => (1 : SignTypeˣ)) '' D)
  let f (x : Fin k → RV0 O) (i : Fin k) : RV0 O := (u i).val * x i
  have law (x : H) (i : Fin k) : lab (f x.val i) = (b i,(lab (x.val i)).2) := by
    obtain ⟨a,_,ha⟩ := x.property.2
    have sgn := congrArg Prod.fst (congrFun ha i)
    change 1 = (lab (x.val i)).1 at sgn
    change lab ((u i).val * x.val i) = _
    rw [signedLabel_mul O hO (nz i) (x.property.1 i),hu]
    exact Prod.ext (by simp [← sgn]) (one_mul _)
  have image_eq : f '' H = sharp model lab (signInsert b '' D) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨a,ha,eq⟩ := hx.2
      refine ⟨fun i => mul_ne_zero (nz i) (hx.1 i),a,ha,funext fun i => ?_⟩
      change (b i,a i) = lab (f x i)
      rw [law ⟨x,hx⟩ i]
      exact congrArg (Prod.mk (b i)) (congrArg Prod.snd (congrFun eq i))
    · rintro ⟨ny,a,ha,eq⟩
      let x (i : Fin k) : RV0 O := y i / (u i).val
      have nx i : x i ≠ 0 := div_ne_zero (G₀ := RV0 O) (ny i) (nz i)
      have fx : f x = y := funext fun i => mul_div_cancel₀ (G₀ := RV0 O) _ (nz i)
      refine ⟨x,⟨nx,a,ha,funext fun i => ?_⟩,fx⟩
      have h := congrFun eq i
      rw [← fx] at h
      change (b i,a i) = lab ((u i).val * x i) at h
      rw [signedLabel_mul O hO (nz i) (nx i),hu] at h
      apply mul_left_cancel (a := (b i,(1 : O.ValueGroupˣ)))
      exact (show (b i,(1 : O.ValueGroupˣ)) * signInsert (fun _ => (1 : SignTypeˣ)) a i =
        (b i,a i) by ext <;> simp [signInsert]).trans h
  have inj : Function.Injective f := fun x y h => funext fun i => rv_mul_left_cancel O (nz i) (congrFun h i)
  let e := (Equiv.Set.imageOfInjOn f H inj.injOn).trans (Set.equivOfEq image_eq)
  refine ⟨e,?_,law⟩
  let Var := RVVariables (Fin k ⊕ Fin k)
  let vars := fun t => (S.carrier t : Type _) ⊕ Var t
  let row (i : Fin k) : SortedTerm J F vars .rv := rvMulTerm (.var (.inl (u i))) (.var (.inr (.inl i)))
  have dom : isRVSet model S {w : Fin k ⊕ Fin k → RV0 O | w ∘ Sum.inl ∈ H} := isRVSet_precomp Sum.inl hd
  have graph := dom.inter (SortedDefinableOver.iInter fun i : Fin k =>
    SortedDefinableOver.coordinate_eq_term (M := model) (A := S.carrier) (Var := Var) .rv (.inr i) (row i))
  convert graph using 1
  ext w
  change (∃ x : H, x.val = w .rv ∘ Sum.inl ∧ f x.val = w .rv ∘ Sum.inr) ↔
    _ ∧ w ∈ ⋂ i : Fin k, {t | t .rv (.inr i) = (row i).realize model (fun s => Sum.elim Subtype.val (t s))}
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,row,realize_rvMulTerm,SortedTerm.realize]
  change (∃ x : H, x.val = w .rv ∘ Sum.inl ∧ f x.val = w .rv ∘ Sum.inr) ↔
    _ ∧ ∀ i, w .rv (.inr i) = f (w .rv ∘ Sum.inl) i
  exact ⟨fun ⟨x,h,h'⟩ => ⟨h ▸ x.property,fun i => h ▸ (congrFun h' i).symm⟩,
    fun ⟨hx,h⟩ => ⟨⟨_,hx⟩,rfl,funext fun i => (h i).symm⟩⟩

variable [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul =
    P e (positiveRVToRV0 O x.toMul))

include hv powers in
theorem positive_affine_lift {k} (A : (Matrix (Fin k) (Fin k) F)ˣ) (u : Fin k → Additive (PositiveRV O))
    (old : ∀ i, codeTuple O u i ∈ S.carrier .rv) (D : Set (Fin k → V))
    (hd : isRVSet model S (positiveSharp O v D)) :
    ∃ e : positiveSharp O v D ≃ positiveSharp O v (affineLift A (v ∘ u) '' D),
      SortedDefinableOver model S.carrier (rvGraph (fun x => (e x).val)) ∧
      ∀ x, (fun i => Additive.ofMul (lab ((e x).val i)).2) =
        affineLift A (v ∘ u) (fun i => Additive.ofMul (lab (x.val i)).2) := by
  let f := rvAffineMonomial O P A.val (codeTuple O u)
  have law (x : Fin k → Additive (PositiveRV O)) : f (codeTuple O x) = codeTuple O (affineLift A u x) :=
    code_affine O P powers A.val u x
  have image_eq : f '' positiveSharp O v D = positiveSharp O v (affineLift A (v ∘ u) '' D) := by
    ext y
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨_,⟨_,hx,(affineLift_value v A u x).symm⟩,(law x).symm⟩
    · rintro ⟨y,⟨a,ha,eq⟩,rfl⟩
      let x := (affineLift A u).symm y
      have ex : affineLift A u x = y := Equiv.apply_symm_apply _ _
      have vx : v ∘ x = a := (affineLift A (v ∘ u)).injective
        ((affineLift_value v A u x).symm.trans ((congrArg (v ∘ ·) ex).trans eq.symm))
      exact ⟨_,⟨x,show v ∘ x ∈ D by rwa [vx],rfl⟩,(law x).trans (congrArg (codeTuple O) ex)⟩
  have inj : Set.InjOn f (positiveSharp O v D) := by
    rintro _ ⟨x,_,rfl⟩ _ ⟨y,_,rfl⟩ eq
    exact congrArg (codeTuple O) ((affineLift A u).injective
      (codeTuple_injective O ((law x).symm.trans (eq.trans (law y)))))
  let e := (Equiv.Set.imageOfInjOn f _ inj).trans (Set.equivOfEq image_eq)
  refine ⟨e,definable_monomial_map O hO P S _ hd A.val (fun i => ⟨_,old i⟩),?_⟩
  have codeval (x : Fin k → Additive (PositiveRV O)) :
      (fun i => Additive.ofMul (lab (codeTuple O x i)).2) = v ∘ x := by
    funext i
    rw [codeTuple,signedLabel_code]; exact (hv (x i)).symm
  rintro ⟨_,x,hx,rfl⟩
  change (fun i => Additive.ofMul (lab (f (codeTuple O x) i)).2) = _
  rw [law,codeval,codeval]; exact affineLift_value v A u x

end GeneralizedEuler.Section4
