module

public import Section4.FixedParameterSpans
public import Section4.LiftQuotientProfiles
import all Section4.SignedWholeMatches
import all Section4.SignedFiberCoordinates
import all Section4.QuotientSpanProfiles
import all Section4.TaggedFiberMatching
import all Section4.RVFamilyOperations
import all Section4.RVProducts
import all Section4.TaggedLiftRealization
import all Section4.RVScissorRealization
import all Section4.RVFamilySemiring
import all Section4.UnaryTaggedComparison
public import Section4.CanonicalRectangles
import all Section4.SignedShears
import all Section4.RVTaggedEquivalence
import all Section4.Factors

/-! Adding a nonempty fixed-value residue factor preserves the ability
to recover all quotient-span profiles from an RV product class. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J JS : Language} [J.Structure K] [J.Structure (Residue O)]
  [JS.Structure (SignedValueGroup O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (liftIso : ∀ {k} (D E : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS E →
    ∀ f : D ≃ E, A.Definable JS {z : Fin k ⊕ Fin k → SignedValueGroup O | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D) (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) E))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO
local notation "sh" => taggedSharp (S := S) val A defSharp


local notation "fam" => signedFamily O A
local notation "code" => signedLiftEquiv O hO v hv P S A defSharp

private def residueProductCode (R : RVFamily M S) {k} (U : Over (J := JS) A k) :
    R.Points × (fam U).Lift (F := F) (T := Additive (PositiveRV O)) v ≃ (R.product (sh U)).Points :=
  (Equiv.prodCongr (Equiv.refl _) (code U)).trans (RVFamily.cartesianPoints R (sh U))

local notation "pack" => residueProductCode O v hv hO P S A defSharp

private theorem code_shear (R : RVFamily M S) {k} (U : Over (J := JS) A k)
    (fixed : ∀ p : R.Points, ∀ i, Additive.ofMul (RVValueSection.valueCoordinate (p.2.val i)) ∈ G)
    (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker) (p : R.Points) (x : (fam U).Lift (F := F) (T := Additive (PositiveRV O)) v) :
    signedShear v hv s hs G L ∘ ((pack R U) (p,x)).2.val =
      ((pack R U) (p,(fam U).move (T := Additive (PositiveRV O)) v G L x)).2.val := by
  funext i; cases i with
  | inl j => exact signedShear_base v hv s hs G L _ (fixed p j)
  | inr j => exact signedFiberCode_shear O hO v hv s hs G L (x.1.2 j) (x.2.val j)

include hv hs agrees units clamp powers in
set_option maxHeartbeats 1500000 in
theorem quotient_profiles_of_residue_product_iso
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    (R : RVFamily M S) (p : R.Points)
    (fixed : ∀ a : R.Points, ∀ i, Additive.ofMul (RVValueSection.valueCoordinate (a.2.val i)) ∈ G)
    {k l} (U : Over (J := JS) A k) (W : Over (J := JS) A l)
    (iso : (R.product (sh U)).Iso (R.product (sh W)))
    {I : Type*} (H : I → Submodule F (Additive O.ValueGroupˣ)) (extendsBase : ∀ i, G ≤ H i) :
    Set.range (fun a : U.points A => fun i => quotientTupleSpan (H i) (unsignedPoint O A U a)) =
    Set.range (fun b : W.points A => fun i => quotientTupleSpan (H i) (unsignedPoint O A W b)) := by
  obtain ⟨f,hf⟩ := iso
  have cover {m n} (D : Over (J := JS) A m) (E : Over (J := JS) A n)
      (q : (R.product (sh D)).Points ≃ (R.product (sh E)).Points)
      (graph : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ q i j)) (a : D.points A) :
      ∃ b : E.points A, ∀ i, quotientTupleSpan (H i) (unsignedPoint O A D a) =
        quotientTupleSpan (H i) (unsignedPoint O A E b) := by
    let e := (pack R D).trans (q.trans (pack R E).symm)
    have comm (L) (r) (x) : e (r,(fam D).move (T := Additive (PositiveRV O)) v G L x) =
        ((e (r,x)).1,(fam E).move (T := Additive (PositiveRV O)) v G L (e (r,x)).2) := by
      let y := e (r,x)
      let u := pack R D (r,x)
      let w := pack R E y
      have eq : q u = w := ((pack R E).apply_symm_apply _).symm
      have orig : Sum.elim u.2.val w.2.val ∈ RVFamily.graphPiece _ _ q u.1 w.1 := ⟨u.2,w.2,rfl,rfl,eq⟩
      have action := ((signedShear_reduct (J := J) v hv s hs G L hO g P agrees units clamp powers).setInvariant S
        (fun t => signedShear_base v hv s hs G L _ (base t)) qe (graph u.1 w.1) _).mpr orig
      obtain ⟨left,right,hl,hr,eq'⟩ := action
      have l : (⟨u.1,left⟩ : (R.product (sh D)).Points) = pack R D (r,(fam D).move (T := Additive (PositiveRV O)) v G L x) :=
        Sigma.ext rfl (heq_of_eq (Subtype.ext (hl.trans (code_shear O v hv s hs G hO P S A defSharp R D fixed L r x))))
      have r' : (⟨w.1,right⟩ : (R.product (sh E)).Points) = pack R E (y.1,(fam E).move (T := Additive (PositiveRV O)) v G L y.2) :=
        Sigma.ext rfl (heq_of_eq (Subtype.ext (hr.trans (code_shear O v hv s hs G hO P S A defSharp R E fixed L y.1 y.2))))
      exact (pack R E).symm_apply_eq.mpr ((congrArg q l).symm.trans (eq'.trans r'))
    have surj : Function.Surjective v := fun t => ⟨s t,DFunLike.congr_fun hs t⟩
    let labels := signedFamilyLabels O A D
    obtain ⟨x,hx⟩ := FiberFamily.label_surjective (T := Additive (PositiveRV O)) v (fam D) surj (labels.symm a)
    let read (t : (fam D).Label) : Fin m → Additive O.ValueGroupˣ := t.2.val
    have coords := congrArg read hx
    change v ∘ x.2.val = unsignedPoint O A D a at coords
    obtain ⟨d,hd⟩ := positive_kernel_nonzero O hO v hv
    have keep := FiberFamily.spans_with_fixed_parameters (F := F) (V := Additive O.ValueGroupˣ)
      (A := fam D) (B := fam E) (T := Additive (PositiveRV O)) (P := R.Points) (Q := R.Points) v G e
      (fun L r z => comm L r z) d hd p x
    let y := (e (p,x)).2
    refine ⟨signedFamilyLabels O A E ((fam E).label (T := Additive (PositiveRV O)) v y),fun i => ?_⟩
    rw [← coords]
    change quotientTupleSpan (H i) (v ∘ x.2.val) = quotientTupleSpan (H i) (v ∘ y.2.val)
    exact keep (H i) (extendsBase i)
  apply Set.Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    obtain ⟨b,h⟩ := cover U W f hf u
    exact ⟨b,(funext h).symm⟩
  · rintro _ ⟨w,rfl⟩
    obtain ⟨a,h⟩ := cover W U f.symm (RVFamily.inverse_graph _ _ f hf) w
    exact ⟨a,(funext h).symm⟩

end GeneralizedEuler.Section4
