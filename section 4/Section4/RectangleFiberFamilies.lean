module

public import Section4.NormalRectangles
public import Section4.TaggedFiberMatching
public import Section4.RVTaggedEquivalence
public import Section4.SignedShears
import all Section4.NormalRectangles
import all Section4.ResidueWeights
import all Section4.RectangleClasses
import all Section4.DefinableResidueMatrices
import all Section4.CanonicalChartMaps
import all Section4.RVTaggedEquivalence
import all Section4.TaggedFiberMatching
import all Section4.Scissors

/-! Whole-fiber matching for a definable bijection between finite
unions of normalized rectangles of different heights. Each label retains
the rectangle index and the entire residue tuple. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k l : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

@[expose] def rvFamily : RVFamily (canonicalStructure (L := J) O hO P) S where
  Tag := I
  Coord i := Fin (c i).m ⊕ Fin (c i).r
  piece i := (c i).points
  definable i := (c i).points_definable pull

@[expose] def fiberFamily : FiberFamily (Additive O.ValueGroupˣ) where
  Tag := (i : I) × (c i).units
  height t := (c t.1).r
  domain t := (c t.1).values

def pack (x : (fiberFamily c).Lift (T := (Additive (PositiveRV O))) v) : (rvFamily c pull).Points :=
  ⟨x.1.1,Sum.elim (unitTuple O v (Equiv.refl _) x.1.2.val) (codeTuple O x.2.val),
   ⟨x.1.2.val,x.1.2.property,rfl⟩,⟨x.2.val,x.2.property,rfl⟩⟩

def fiberEquiv : (fiberFamily c).Lift (T := (Additive (PositiveRV O))) v ≃ (rvFamily c pull).Points := by
  apply Equiv.ofBijective (pack c pull)
  constructor
  · rintro ⟨⟨i,u⟩,x⟩ ⟨⟨j,w⟩,y⟩ eq
    obtain rfl : i = j := congrArg Sigma.fst eq
    have same := congrArg Subtype.val (Sigma.mk.inj_iff.mp eq).2.eq
    have sameUnits := unitTuple_injective O v (Equiv.refl _) (congrArg (· ∘ Sum.inl) same)
    obtain rfl : u = w := Subtype.ext sameUnits
    have sameFree := codeTuple_injective O (congrArg (· ∘ Sum.inr) same)
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext sameFree))
  · rintro ⟨i,t,⟨u,hu,eu⟩,⟨x,hx,ex⟩⟩
    refine ⟨⟨⟨i,u,hu⟩,x,hx⟩,Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))⟩
    exact funext (Sum.rec (congrFun eu) (congrFun ex))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : (Additive O.ValueGroupˣ) →ₗ[F] (Additive (PositiveRV O))) (hs : v.comp s = LinearMap.id)

omit [Finite I] in
theorem pack_shear (L : (Additive O.ValueGroupˣ ⧸ G) →ₗ[F] v.ker)
    (i : I) (u : Fin (c i).m → v.ker) (x : Fin (c i).r → Additive (PositiveRV O)) :
    signedShear v hv s hs G L ∘ Sum.elim (unitTuple O v (Equiv.refl _) u) (codeTuple O x) =
      Sum.elim (unitTuple O v (Equiv.refl _) u) (codeTuple O (shear (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G L ∘ x)) := by
  funext j
  cases j with
  | inl j =>
    have fixed : v (u j).val ∈ G := (u j).property ▸ G.zero_mem
    change signedShear v hv s hs G L (positiveRVToRV0 O (u j).val.toMul) = positiveRVToRV0 O (u j).val.toMul
    have eq := shear_fixes_base (T := Additive (PositiveRV O))
      (V := Additive O.ValueGroupˣ) v G L (t := (u j).val) fixed
    rw [signedShear_positive,eq]
  | inr j =>
    change signedShear v hv s hs G L (positiveRVToRV0 O (x j).toMul) =
      positiveRVToRV0 O (shear (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G L (x j)).toMul
    exact signedShear_positive v hv s hs G L (x j)

variable (d : H → (NormalRectangle (JG := JG) (G := G) O v hO P S) l) (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)
  (graph : ∀ i j, isRVSet (canonicalStructure (L := J) O hO P) S (RVFamily.graphPiece _ _ f i j))

def onFibers : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v ≃ (fiberFamily d).Lift (T := Additive (PositiveRV O)) v := (fiberEquiv c pull).trans (f.trans (fiberEquiv d pull).symm)

variable (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : (Additive (PositiveRV O))), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x, q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

include graph agrees units clamp powers base qe in
theorem onFibers_commutes (L : ((Additive O.ValueGroupˣ) ⧸ G) →ₗ[F] v.ker) (x : (fiberFamily c).Lift (T := (Additive (PositiveRV O))) v) :
    onFibers c pull d f ((fiberFamily c).move (T := (Additive (PositiveRV O))) v G L x) =
      (fiberFamily d).move (T := (Additive (PositiveRV O))) v G L (onFibers c pull d f x) := by
  let y := onFibers c pull d f x
  let u := pack c pull x
  let w := pack d pull y
  have eq : f u = w := ((fiberEquiv d pull).apply_symm_apply _).symm
  have orig : Sum.elim u.2.val w.2.val ∈ RVFamily.graphPiece _ _ f u.1 w.1 := ⟨u.2,w.2,rfl,rfl,eq⟩
  have action := ((signedShear_reduct (J := J) v hv s hs G L hO g P agrees units clamp powers).setInvariant S
    (fun t => signedShear_base v hv s hs G L _ (base t)) qe (graph u.1 w.1) _).mpr orig
  obtain ⟨left,right,hl,hr,eq'⟩ := action
  have a : (⟨u.1,left⟩ : (rvFamily c pull).Points) = pack c pull ((fiberFamily c).move (T := (Additive (PositiveRV O))) v G L x) :=
    Sigma.ext rfl (heq_of_eq (Subtype.ext (hl.trans (pack_shear c hv s hs L x.1.1 x.1.2.val x.2.val))))
  have b : (⟨w.1,right⟩ : (rvFamily d pull).Points) = pack d pull ((fiberFamily d).move (T := (Additive (PositiveRV O))) v G L y) :=
    Sigma.ext rfl (heq_of_eq (Subtype.ext (hr.trans (pack_shear d hv s hs L y.1.1 y.1.2.val y.2.val))))
  exact (fiberEquiv d pull).symm_apply_eq.mpr ((congrArg f a).symm.trans (eq'.trans b))

include graph agrees units clamp powers base qe in
/-- A single point above an independent maximal-height label determines an
entire matched fiber, even if the bijection changes rectangle and residue tags. -/
theorem maximal_match (x : (fiberFamily c).Lift (T := (Additive (PositiveRV O))) v)
    (ind : LinearIndependent F (G.mkQ ∘ v ∘ x.2.val))
    (maximal : ∀ j, (d j).r ≤ (c x.1.1).r) :
    let e : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v ≃ (fiberFamily d).Lift (T := Additive (PositiveRV O)) v := onFibers c pull d f
    (d (e x).1.1).r = (c x.1.1).r ∧
      WholeMatch ((fiberFamily c).label (T := Additive (PositiveRV O)) v) ((fiberFamily d).label (T := Additive (PositiveRV O)) v) e
        ((fiberFamily c).label (T := Additive (PositiveRV O)) v x) ((fiberFamily d).label (T := Additive (PositiveRV O)) v (e x)) := by
  obtain ⟨z,hz⟩ := positive_kernel_nonzero O hO v hv
  exact FiberFamily.maximal_whole_match (A := fiberFamily c) (B := fiberFamily d) (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G (onFibers c pull d f)
    (onFibers_commutes c pull hv s hs d f graph g agrees units clamp powers base qe)
    z hz x ind (maximal ((onFibers c pull d f) x).1.1)

end GeneralizedEuler.Section4.NormalRectangle
