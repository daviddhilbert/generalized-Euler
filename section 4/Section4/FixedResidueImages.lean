module

public import Section4.OldValueCharts
import all Section4.CanonicalChartCover
import all Section4.SignedRectangleFactors
import all Section4.GraphChartBasis
import all Section4.SignedShears
import all Section4.ReductInvariance
import all Section4.CanonicalChartMaps
import all Section4.Objects

/-! Orthogonality for the images needed in Remark 4.8. A bijection sends
a finite-value carrier to a positive model with finite value image. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2

theorem fixed_image_of_graph {J : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure J F Z}
    {S : SortedSubstructure M} {I H : Type} {D : Set (I → Z .rv)} {E : Set (H → Z .rv)}
    (iso : RVDefinablyEquivalent M S.carrier D E) (g : Z .rv → Z .rv)
    (invariant : ∀ R : Set (I ⊕ H → Z .rv), isRVSet M S R → ∀ w ∈ R, g ∘ w ∈ R)
    (fixed : ∀ x ∈ D, g ∘ x = x) : ∀ y ∈ E, g ∘ y = y := by
  obtain ⟨e,he⟩ := iso
  intro y hy
  let x := e.symm ⟨y,hy⟩
  let R := {w : I ⊕ H → Z .rv | ∃ z : D, z.val = w ∘ Sum.inl ∧ (e z).val = w ∘ Sum.inr}
  have hx : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply _)
  have hit : Sum.elim x.val y ∈ R := ⟨x,rfl,hx⟩
  obtain ⟨z,hz,hz'⟩ := invariant R he _ hit
  have eq : z = x := Subtype.ext (hz.trans (fixed x.val x.property))
  exact hz'.symm.trans (eq ▸ hx)

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ)) {J JG : Language} [JG.Structure O.ValueGroupˣ]
  [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
  (base : ∀ t : S.carrier .rv, Additive.ofMul (RVValueSection.valueCoordinate t.val) ∈ G)

include witness base in
theorem residue_source_fixed {n} (U : Set (Fin n → RV0 O)) (hu : isRVSet _ S U)
    (fin : (Set.range fun x : U => signedLabel O hO ∘ x.val).Finite)
    (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker) (x : U) : signedShear v hv s hs G L ∘ x.val = x.val := by
  obtain ⟨y,_,hy,eq⟩ := residue_unsigned_representatives O hO P S @witness U hu fin x
  funext i
  apply signedShear_base
  exact (congrArg Additive.ofMul (valueCoordinate_eq_of_unsigned O (congrFun eq i))) ▸ base ⟨y i,hy i⟩

local instance fixedImageAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) := inferInstanceAs (JG.Structure O.ValueGroupˣ)

include hv hs witness base in
theorem positive_residue_image {m n} (D : Set (Fin m → RV0 O)) (E : Set (Fin n → RV0 O))
    (hd : isRVSet _ S D) (fin : (Set.range fun x : D => signedLabel O hO ∘ x.val).Finite)
    (pos : ∀ y ∈ E, ∀ j, IsPositiveRV O (y j))
    (iso : RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier D E)
    (atlas : AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' E))
    (inv : ∀ L (R : Set (Fin m ⊕ Fin n → RV0 O)), isRVSet _ S R → ∀ w ∈ R, signedShear v hv s hs G L ∘ w ∈ R) :
    (Set.range fun y : E => signedLabel O hO ∘ y.val).Finite := by
  obtain ⟨d,hne⟩ := positive_kernel_nonzero O hO v hv
  let Y := codeTuple O ⁻¹' E
  have old (z : Fin n → Additive (PositiveRV O)) (hz : z ∈ Y) (i : Fin n) : v (z i) ∈ G := by
    apply old_value_of_fixed (F := F) (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G d hne (z i)
    intro L
    have fixed := fixed_image_of_graph iso _ (inv L) (fun x hx => residue_source_fixed O v hv s hs G hO P S @witness base D hd fin L ⟨x,hx⟩)
    have t := congrFun (fixed _ hz) i
    exact Additive.toMul.injective (positiveRVToRV0_injective O ((signedShear_positive v hv s hs G L (z i)).symm.trans t))
  obtain ⟨_,p,_,ne,_,cv⟩ := atlas
  have values := finite_values_of_old_charts v G s hs p Y ne cv old
  apply (values.image (fun a => positiveValueLabel O ∘ a)).subset
  rintro _ ⟨y,rfl⟩
  choose z hz using fun i => exists_positiveRV_of_positive O (pos _ y.property i)
  let t i := Additive.ofMul (z i)
  have encoded : codeTuple O t = y.val := funext hz
  refine ⟨_,⟨t,(congrArg (· ∈ E) encoded).mpr y.property,rfl⟩,?_⟩
  funext i
  exact (congrArg (positiveValueLabel O) (hv (t i))).trans ((signedLabel_code O hO (z i)).symm.trans (congrArg (signedLabel O hO) (hz i)))

end GeneralizedEuler.Section4
