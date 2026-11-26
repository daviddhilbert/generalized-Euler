module

public import Section4.WholeMatchRectangles
import all Section4.WholeMatchRectangles
import all Section4.MixedMatchFactors
import all Section4.RectangleFiberFamilies
import all Section4.RectangleMatchGraph
import all Section4.SignedShears
import all Section4.SignedRectangleFactors
import all Section4.RepresentedFiberMatches
import all Section4.ResidueWeights
import all Section4.CanonicalChartMaps
import all Section4.DefinableResidueMatrices
import all Section4.TaggedFiberMatching
import all Section4.NormalRectangles
import all Section4.CanonicalRectangles
import all Section2.RVSplitCoordinates

/-! Connect the shear orbits to the separated matching graph using one
representative of each value. The section is used only to evaluate the
relation defined over the original base. -/
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

def encodeFiberLabel (z : (fiberFamily c).Label) :
    (i : I) × ((Fin (c i).m → RV0 O) × (Fin (c i).r → SignedValueGroup O)) :=
  ⟨z.1.1,unitTuple O v (Equiv.refl _) z.1.2.val,positiveValueLabel O ∘ z.2.val⟩

omit [Finite I] in
theorem encodeFiberLabel_injective : Function.Injective (encodeFiberLabel c) := by
  rintro ⟨⟨i,u⟩,a⟩ ⟨⟨j,w⟩,b⟩ eq
  obtain rfl : i = j := congrArg Sigma.fst eq
  have e := (Sigma.mk.inj_iff.mp eq).2.eq
  obtain rfl : u = w := Subtype.ext (unitTuple_injective O v (Equiv.refl _) (congrArg Prod.fst e))
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun t => ?_)))
  exact congrArg Prod.snd (congrFun (congrArg Prod.snd e) t)

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

include hv in
theorem label_pack (x : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v) :
    pointLabel c pull (fiberEquiv c pull x) =
      encodeFiberLabel c ((fiberFamily c).label (T := Additive (PositiveRV O)) v x) := by
  refine Sigma.ext rfl (heq_of_eq (Prod.ext rfl (funext fun j => ?_)))
  exact (signedLabel_code O hO _).trans (congrArg (positiveValueLabel O) (hv _).symm)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S l)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

include hv in
theorem pack_whole_match (x : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v) :
    let e := onFibers c pull d f
    WholeMatch ((fiberFamily c).label (T := Additive (PositiveRV O)) v)
      ((fiberFamily d).label (T := Additive (PositiveRV O)) v) e
      ((fiberFamily c).label (T := Additive (PositiveRV O)) v x)
      ((fiberFamily d).label (T := Additive (PositiveRV O)) v (e x)) ↔
    WholeMatch (pointLabel c pull) (pointLabel d pull) f (pointLabel c pull (fiberEquiv c pull x))
      (pointLabel d pull (f (fiberEquiv c pull x))) := by
  let e := onFibers c pull d f
  have eq (t) : f (fiberEquiv c pull t) = fiberEquiv d pull (e t) := ((fiberEquiv d pull).apply_symm_apply _).symm
  dsimp only
  rw [wholeMatch_iff,wholeMatch_iff]
  have test (t) : (pointLabel c pull (fiberEquiv c pull t) = pointLabel c pull (fiberEquiv c pull x) ↔
      pointLabel d pull (f (fiberEquiv c pull t)) = pointLabel d pull (f (fiberEquiv c pull x))) ↔
      ((fiberFamily c).label (T := Additive (PositiveRV O)) v t = (fiberFamily c).label (T := Additive (PositiveRV O)) v x ↔
       (fiberFamily d).label (T := Additive (PositiveRV O)) v (e t) = (fiberFamily d).label (T := Additive (PositiveRV O)) v (e x)) := by
    rw [eq,eq,label_pack c pull hv,label_pack c pull hv,label_pack d pull hv,label_pack d pull hv,
      (encodeFiberLabel_injective c).eq_iff,(encodeFiberLabel_injective d).eq_iff]
  constructor
  · intro all z
    obtain ⟨t,rfl⟩ := (fiberEquiv c pull).surjective z
    exact (test t).mpr (all t)
  · exact fun all t => (test t).mp (all _)

def sectionLift (u : (fiberFamily c).Label) : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v :=
  ⟨u.1,s ∘ u.2.val,by
    have h : v ∘ (s ∘ u.2.val) = u.2.val := funext fun t => DFunLike.congr_fun hs _
    exact h.symm ▸ u.2.property⟩

omit [Finite I] in
theorem sectionLift_label (u : (fiberFamily c).Label) :
    (fiberFamily c).label (T := Additive (PositiveRV O)) v (sectionLift c s hs u) = u :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun _ => DFunLike.congr_fun hs _)))

include hv hs in
theorem residueRV_kernel (z : v.ker) : residueRV O (kernelResidue v z) = positiveRVToRV0 O z.val.toMul := by
  have eq := kernelResidue_join v hv s hs 0 z
  change (linearValueSection v hv s hs).join 1 _ = _ at eq
  simpa only [RVValueSection.join_one,map_zero,zero_add] using eq

omit [Finite I] in
include hv hs in
theorem sectionLift_tuple (u : (fiberFamily c).Label) :
    Sum.elim (unitTuple O v (Equiv.refl _) u.1.2.val) (codeTuple O (s ∘ u.2.val)) =
      mixedPair (linearValueSection v hv s hs) (kernelResidue v ∘ u.1.2.val)
        (Additive.toMul ∘ u.2.val) := by
  funext t
  cases t with
  | inl j => exact (residueRV_kernel hv s hs _).symm
  | inr j => rfl

variable (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j))
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

include graph agrees units clamp powers base qe in
theorem independent_label_match (a : (fiberFamily c).Label)
    (ind : LinearIndependent F (G.mkQ ∘ a.2.val))
    (maximal : ∀ j, (d j).r ≤ (c a.1.1).r) :
    ∃ b : (fiberFamily d).Label, (d b.1.1).r = (c a.1.1).r ∧
      ((Additive.toMul ∘ a.2.val,Additive.toMul ∘ b.2.val),
        kernelResidue v ∘ a.1.2.val,kernelResidue v ∘ b.1.2.val) ∈
        labelMatching c pull (linearValueSection v hv s hs) d f a.1.1 b.1.1 := by
  let x := sectionLift c s hs a
  let y := onFibers c pull d f x
  let b := (fiberFamily d).label (T := Additive (PositiveRV O)) v y
  have values : v ∘ x.2.val = a.2.val := funext fun _ => DFunLike.congr_fun hs _
  have independent : LinearIndependent F (G.mkQ ∘ v ∘ x.2.val) := by
    rw [values]
    exact ind
  obtain ⟨height,matchFiber⟩ := maximal_match c pull hv s hs d f graph g agrees units clamp powers base qe
    x independent maximal
  have matchPoints := (pack_whole_match c pull hv d f x).mp matchFiber
  let z := sectionLift d s hs b
  have fy : f (fiberEquiv c pull x) = fiberEquiv d pull y := ((fiberEquiv d pull).apply_symm_apply _).symm
  have lab : pointLabel d pull (f (fiberEquiv c pull x)) = pointLabel d pull (fiberEquiv d pull z) := by
    rw [fy,label_pack d pull hv,label_pack d pull hv,sectionLift_label]
  rw [lab] at matchPoints
  exact ⟨b,height,(fiberEquiv c pull x).2,(fiberEquiv d pull z).2,
    sectionLift_tuple c hv s hs a,sectionLift_tuple d hv s hs b,matchPoints⟩

end GeneralizedEuler.Section4.NormalRectangle
