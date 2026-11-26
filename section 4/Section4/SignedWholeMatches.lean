module

public import Section4.SignedFiberCoordinates
public import Section4.GraphChartBasis
import all Section4.RVTaggedEquivalence
import all Section4.TaggedMatchGraph
import all Section4.SignedFiberCoordinates
import all Section4.TaggedFiberMatching
import all Section4.UnaryFiberMatching
import all Section4.UnaryTaggedComparison
import all Section4.Factors
import all Section4.SignedValueGeneration

/-! Every independent value label of an equipotent pair of tagged sharp
objects belongs to their definable matching. The original signs and the
original component tags are included in the conclusion. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false

theorem wholeMatch_iff {X Y I J : Type*} (a : X → I) (b : Y → J) (f : X ≃ Y) (i j) :
    WholeMatch a b f i j ↔ ∀ x, a x = i ↔ b (f x) = j := by
  constructor
  · intro h x; constructor
    · exact fun hx => (congrArg (f x ∈ ·) h).mp ⟨x,hx,rfl⟩
    · intro hy
      obtain ⟨u,hu,he⟩ := (congrArg (f x ∈ ·) h).mpr hy
      exact f.injective he ▸ hu
  · intro h; apply Set.ext; intro y; obtain ⟨x,rfl⟩ := f.surjective y
    exact ⟨fun ⟨u,hu,he⟩ => (h x).mp (f.injective he ▸ hu),fun hy => ⟨x,(h x).mpr hy,rfl⟩⟩

theorem wholeMatch_inverse {X Y I J : Type*} (a : X → I) (b : Y → J) (f : X ≃ Y) (i j) :
    WholeMatch b a f.symm j i ↔ WholeMatch a b f i j := by
  rw [wholeMatch_iff,wholeMatch_iff]
  exact ⟨fun h x => by simpa using (h (f x)).symm,fun h y => by simpa using (h (f.symm y)).symm⟩

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
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
  {k : ℕ} (U W : Over (J := H) A k)

local notation "fam" => signedFamily O A
local notation "code" => signedFamilyCode O hO v hv P S A defSharp
local notation "sh" => taggedSharp (S := S) (signedLabel O hO) A defSharp
local notation "lab" => sharpLabel (S := S) (signedLabel O hO) A defSharp
local notation "move" => FiberFamily.move (F := F) (T := Additive (PositiveRV O)) v G
local notation "liftLabel" => FiberFamily.label (F := F) (T := Additive (PositiveRV O)) v

def signedLiftEquiv := Equiv.ofBijective (code U) (signedFamilyCode_bijective O hO v hv P S A defSharp U)

variable (f : (taggedSharp (S := S) (signedLabel O hO) A defSharp U).Points ≃ (taggedSharp (S := S) (signedLabel O hO) A defSharp W).Points)
  (action : ∀ i j L (w : Fin k ⊕ Fin k → RV0 O), w ∈ RVFamily.graphPiece _ _ f i j →
    signedShear v hv s hs G L ∘ w ∈ RVFamily.graphPiece _ _ f i j)
local notation "eU" => signedLiftEquiv O hO v hv P S A defSharp U
local notation "eW" => signedLiftEquiv O hO v hv P S A defSharp W

include action in
private theorem conjugate_commutes (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker) (x) :
    ((eU).trans (f.trans (eW).symm)) (move (fam U) L x) =
      move (fam W) L (((eU).trans (f.trans (eW).symm)) x) := by
  let y := (eW).symm (f (eU x))
  let a := code U x
  let b := code W y
  have eq : f a = b := ((eW).apply_symm_apply _).symm
  have orig : Sum.elim a.2.val b.2.val ∈ RVFamily.graphPiece _ _ f a.1 b.1 := ⟨a.2,b.2,rfl,rfl,eq⟩
  obtain ⟨u,w,hu,hw,graph⟩ := action _ _ L _ orig
  have leftEq : u = (code U (move (fam U) L x)).2 := Subtype.ext (hu.trans
    (funext fun i => signedFiberCode_shear O hO v hv s hs G L (x.1.2 i) (x.2.val i)))
  have rightEq : w = (code W (move (fam W) L y)).2 := Subtype.ext (hw.trans
    (funext fun i => signedFiberCode_shear O hO v hv s hs G L (y.1.2 i) (y.2.val i)))
  change (eW).symm (f (code U (move (fam U) L x))) = move (fam W) L y
  apply (eW).symm_apply_eq.mpr
  have l : (⟨a.1,u⟩ : (sh U).Points) = code U (move (fam U) L x) := Sigma.ext rfl (heq_of_eq leftEq)
  have r : (⟨b.1,w⟩ : (sh W).Points) = code W (move (fam W) L y) := Sigma.ext rfl (heq_of_eq rightEq)
  exact (congrArg f l).symm.trans (graph.trans r)

include action in
theorem independent_signed_match (a : U.points A)
    (ind : LinearIndependent F (G.mkQ ∘ ((fun u : SignedValueGroup O => Additive.ofMul u.2) ∘ pointTuple (V := SignedValueGroup O) U a))) :
    ∃ b, WholeMatch (lab U) (lab W) f a b := by
  let eu := signedFamilyLabels O A U
  let ew := signedFamilyLabels O A W
  let g := (eU).trans (f.trans (eW).symm)
  have surj : Function.Surjective v := fun t => ⟨s t,DFunLike.congr_fun hs t⟩
  obtain ⟨x,ex⟩ := FiberFamily.label_surjective (F := F) (T := Additive (PositiveRV O)) v (fam U) surj (eu.symm a)
  have ia : LinearIndependent F (G.mkQ ∘ v ∘ x.2.val) := by
    let read (t : (fam U).Label) : Fin k → Additive O.ValueGroupˣ := t.2.val
    have eq := congrArg read ex
    change v ∘ x.2.val = (fun u : SignedValueGroup O => Additive.ofMul u.2) ∘ pointTuple U a at eq
    rw [eq]; exact ind
  obtain ⟨d,nd⟩ := positive_kernel_nonzero O hO v hv
  obtain ⟨_,whole⟩ := FiberFamily.maximal_whole_match (F := F) (T := Additive (PositiveRV O)) v G g
    (conjugate_commutes O hO v hv s hs G P S A defSharp U W f action) d nd x ia le_rfl
  refine ⟨ew (liftLabel (fam W) (g x)),(wholeMatch_iff _ _ _ _ _).mpr ?_⟩
  intro z; obtain ⟨t,rfl⟩ := (eU).surjective z
  have aeq : eu (liftLabel (fam U) x) = a := (congrArg eu ex).trans (eu.apply_symm_apply a)
  have beq : f (eU t) = eW (g t) := ((eW).apply_symm_apply _).symm
  rw [beq,← aeq]
  change lab U (code U t) = _ ↔ lab W (code W (g t)) = _
  rw [signedFamilyCode_label,signedFamilyCode_label]
  exact (eu.injective.eq_iff).trans (((wholeMatch_iff _ _ _ _ _).mp whole t).trans ew.injective.eq_iff.symm)

end GeneralizedEuler.Section4
