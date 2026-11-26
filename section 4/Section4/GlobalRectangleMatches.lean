module

public import Section4.RectanglePairCuts
import all Section4.RectanglePairCuts
import all Section4.HomogeneousMatchedPieces
import all Section4.RectangleLabelMatching
import all Section4.RectangleFiberFamilies
import all Section4.Subrectangles
import all Section4.NormalRectangles
import all Section4.TaggedFiberMatching

/-! Whole-fiber uniqueness makes the matched projections disjoint
across every source and target tag, including distinct rectangles of
the same height. -/
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
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S k)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)

variable {height : ℕ}
variable (cuts : ∀ i j, PairCut (C := C) c pull hv s hs d f res val i j height)

def PairCut.flip {i j} (p : PairCut (C := C) c pull hv s hs d f res val i j height) :
    PairCut (C := C) d pull hv s hs c f.symm res val j i height where
  count := p.count
  left := p.right
  right := p.left
  matched t w b u a := p.matched t u a w b
  weights t := (p.weights t).symm
  dom := p.ran
  ran := p.dom
  unique t t' w b u a := p.unique t t' u a w b
  full w b u a := by
    rw [p.full,keyMatch_inverse]
    exact and_left_comm

def packedLabels : ((i : I) × ((c i).units × (c i).values)) ≃ (fiberFamily c).Label where
  toFun z := localLabel c z.1 z.2.1 z.2.2
  invFun z := ⟨z.1.1,z.1.2,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def leftCut (i : I) (t : (j : H) × Fin (cuts i j).count) := (cuts i t.1).left t.2

theorem leftCut_disjoint (i : I) : Pairwise (fun t t' => Disjoint
    (leftCut c pull hv s hs d f res val cuts i t).labels
    (leftCut c pull hv s hs d f res val cuts i t').labels) := by
  rintro ⟨j,t⟩ ⟨j',t'⟩ ne
  apply Set.disjoint_left.mpr
  rintro ⟨u,a⟩ h h'
  let l := (cuts i j).left t
  let U : (c i).units := ⟨u,l.unitsSub h.1⟩
  let A : (c i).values := ⟨a,l.valuesSub h.2⟩
  obtain ⟨w,b,r⟩ := ((cuts i j).dom t U A).mp h
  obtain ⟨w',b',r'⟩ := ((cuts i j').dom t' U A).mp h'
  have first := ((cuts i j).full U A w b).mp ⟨t,r⟩
  have second := ((cuts i j').full U A w' b').mp ⟨t',r'⟩
  have eq := keyMatch_single c pull hv s hs d f first.2.2 second.2.2
  have target : (⟨j,(w,b)⟩ : (j : H) × ((d j).units × (d j).values)) = ⟨j',(w',b')⟩ :=
    (packedLabels d).injective eq
  obtain rfl : j=j' := congrArg Sigma.fst target
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sigma.mk.inj_iff.mp target).2.eq
  exact ne (congrArg (Sigma.mk j) ((cuts i j).unique t t' U A w b r r'))

theorem leftCut_coverage (i : I) (top : (c i).r = height)
    (independent : ∀ a : (fiberFamily c).Label, a.1.1 = i → LinearIndependent F (G.mkQ ∘ a.2.val) →
      ∃ b : (fiberFamily d).Label, (d b.1.1).r = height ∧ keyMatch c pull hv s hs d f a b)
    (u : Fin (c i).m → v.ker) (hu : u ∈ (c i).units) (a : Fin (c i).r → Additive O.ValueGroupˣ)
    (ha : a ∈ (c i).values) (hi : LinearIndependent F (G.mkQ ∘ a)) :
    ∃ t, (u,a) ∈ (leftCut c pull hv s hs d f res val cuts i t).labels := by
  obtain ⟨⟨⟨j,w⟩,b⟩,hj,h⟩ := independent (localLabel c i ⟨u,hu⟩ ⟨a,ha⟩) rfl hi
  obtain ⟨t,r⟩ := ((cuts i j).full ⟨u,hu⟩ ⟨a,ha⟩ w b).mpr ⟨top,hj,h⟩
  exact ⟨⟨j,t⟩,((cuts i j).dom t ⟨u,hu⟩ ⟨a,ha⟩).mpr ⟨w,b,r⟩⟩

theorem leftCut_iff (a : (fiberFamily c).Label) :
    (∃ t, (a.1.2.val,a.2.val) ∈ (leftCut c pull hv s hs d f res val cuts a.1.1 t).labels) ↔
      (c a.1.1).r = height ∧ ∃ b : (fiberFamily d).Label, (d b.1.1).r = height ∧ keyMatch c pull hv s hs d f a b := by
  obtain ⟨⟨i,u⟩,a⟩ := a
  constructor
  · rintro ⟨⟨j,t⟩,mem⟩
    obtain ⟨w,b,h⟩ := ((cuts i j).dom t u a).mp mem
    have full := ((cuts i j).full u a w b).mp ⟨t,h⟩
    exact ⟨full.1,localLabel d j w b,full.2⟩
  · rintro ⟨hi,⟨⟨j,w⟩,b⟩,hj,h⟩
    obtain ⟨t,hit⟩ := ((cuts i j).full u a w b).mpr ⟨hi,hj,h⟩
    exact ⟨⟨j,t⟩,((cuts i j).dom t u a).mpr ⟨w,b,hit⟩⟩

def flippedCuts (j : H) (i : I) := (cuts i j).flip c pull hv s hs d f res val

theorem matched_membership_preserved (x : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v) :
    let y := onFibers c pull d f x
    (∃ t, (x.1.2.val,v ∘ x.2.val) ∈ (leftCut c pull hv s hs d f res val cuts x.1.1 t).labels) ↔
      ∃ t, (y.1.2.val,v ∘ y.2.val) ∈ (leftCut d pull hv s hs c f.symm res val
        (flippedCuts c pull hv s hs d f res val cuts) y.1.1 t).labels := by
  let e := onFibers c pull d f
  let a := (fiberFamily c).label (T := Additive (PositiveRV O)) v x
  let b := (fiberFamily d).label (T := Additive (PositiveRV O)) v (e x)
  have action (a' b') (h : keyMatch c pull hv s hs d f a' b') : a = a' ↔ b = b' :=
    (wholeMatch_iff _ _ _ _ _).mp ((keyMatch_iff c pull hv s hs d f a' b').mp h) x
  refine (leftCut_iff c pull hv s hs d f res val cuts a).trans (Iff.trans ?_
    (leftCut_iff d pull hv s hs c f.symm res val (flippedCuts c pull hv s hs d f res val cuts) b).symm)
  constructor
  · rintro ⟨ha,b',hb,h⟩
    obtain rfl : b = b' := (action a b' h).mp rfl
    exact ⟨hb,a,ha,(keyMatch_inverse c pull hv s hs d f a b).mpr h⟩
  · rintro ⟨hb,a',ha,hinv⟩
    have h := (keyMatch_inverse c pull hv s hs d f a' b).mp hinv
    obtain rfl : a = a' := (action a' b h).mpr rfl
    exact ⟨ha,b,hb,h⟩

end GeneralizedEuler.Section4.NormalRectangle
