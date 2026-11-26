module

public import Section4.SignedWholeMatches
import all Section4.SignedWholeMatches
import all Section4.SignedFiberCoordinates
import all Section4.TaggedFiberMatching
import all Section4.UnaryTaggedComparison
import all Section4.Factors
import all Section4.FiberMatching

/-! A single image label witnesses equality of all quotient spans,
including the quotients by each convex scale used in Question 4.16. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] def quotientTupleSpan {ι : Type*} (G : Submodule F V) (x : ι → V) : Submodule F (V ⧸ G) :=
  Submodule.span F (Set.range (G.mkQ ∘ x))

theorem map_quotientTupleSpan {ι : Type*} {G H : Submodule F V} (le : G ≤ H) (x : ι → V) :
    (quotientTupleSpan G x).map (Submodule.factor le) = quotientTupleSpan H x := by
  rw [quotientTupleSpan, Submodule.map_span, ← Set.range_comp]
  rfl

theorem quotientTupleSpan_of_le {ι κ : Type*} {G H : Submodule F V} (le : G ≤ H)
    {x : ι → V} {y : κ → V} (eq : quotientTupleSpan G x = quotientTupleSpan G y) :
    quotientTupleSpan H x = quotientTupleSpan H y := by
  rw [← map_quotientTupleSpan le x, ← map_quotientTupleSpan le y, eq]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J H : Language} [J.Structure K] [J.Structure (Residue O)] [H.Structure (SignedValueGroup O)]
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable H D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  {k l : ℕ} (U : Over (J := H) A k) (W : Over (J := H) A l)

local notation "fam" => signedFamily O A
local notation "sh" => taggedSharp (S := S) (signedLabel O hO) A defSharp
local notation "eu" => signedLiftEquiv O hO v hv P S A defSharp U
local notation "ew" => signedLiftEquiv O hO v hv P S A defSharp W

def unsignedPoint (a : U.points A) : Fin k → Additive O.ValueGroupˣ :=
  (fun u : SignedValueGroup O => Additive.ofMul u.2) ∘ pointTuple U a

theorem signed_label_quotient_spans
    (f : (sh U).Points ≃ (sh W).Points)
    (action : ∀ i j L (w : Fin k ⊕ Fin l → RV0 O), w ∈ RVFamily.graphPiece _ _ f i j →
      signedShear v hv s hs G L ∘ w ∈ RVFamily.graphPiece _ _ f i j)
    (a : U.points A) : ∃ b : W.points A, ∀ H' : Submodule F (Additive O.ValueGroupˣ), G ≤ H' →
      quotientTupleSpan H' (unsignedPoint O A U a) = quotientTupleSpan H' (unsignedPoint O A W b) := by
  let labels := signedFamilyLabels O A U
  let g := (eu).trans (f.trans (ew).symm)
  have surj : Function.Surjective v := fun t => ⟨s t, DFunLike.congr_fun hs t⟩
  obtain ⟨x, hx⟩ := FiberFamily.label_surjective (F := F) (T := Additive (PositiveRV O)) v (fam U) surj (labels.symm a)
  let read (t : (fam U).Label) : Fin k → Additive O.ValueGroupˣ := t.2.val
  have coord := congrArg read hx
  change v ∘ x.2.val = unsignedPoint O A U a at coord
  obtain ⟨d, hd⟩ := positive_kernel_nonzero O hO v hv
  have eq := FiberFamily.span_preserved (A := fam U) (B := fam W) (F := F) (T := Additive (PositiveRV O)) v G g
    (signed_conjugate_commutes O hO v hv s hs G P S A defSharp U W f action) d hd x
  refine ⟨signedFamilyLabels O A W (FiberFamily.label (F := F) (T := Additive (PositiveRV O)) v (fam W) (g x)), fun H' le => quotientTupleSpan_of_le le ?_⟩
  change quotientTupleSpan G (unsignedPoint O A U a) = quotientTupleSpan G (v ∘ (g x).2.val)
  rw [← coord]
  exact eq

end GeneralizedEuler.Section4
