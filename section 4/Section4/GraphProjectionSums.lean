module

public import Section4.GraphPieceTensors
public import Section4.PackedGraph
public import Section4.CanonicalChartCover
import all Section4.CanonicalChartCover
import all Section4.ChartIndependence
import all Section4.SliceWeights
import all Section4.PackedGraph

/-! Tensor invariance for definable bijections on positive sets of the
same degree, by decomposing their packed graph. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem subset_cover {X I : Type*} (A : I → Set X) (D : Set X) (cover : (⋃ i, A i) = D) (i : I) : A i ⊆ D := by
  rw [← cover]; exact Set.subset_iUnion A i

private theorem projected_disjoint_union {X Y : Type*} {I : Type*} (A : I → Set X) (B : I → Set Y) (D : Set X)
    (f : X → Y) (h : Set.InjOn f D) (cover : (⋃ i, A i) = D)
    (disj : Pairwise (fun i j => Disjoint (A i) (A j))) (images : ∀ i, B i = f '' A i) :
    Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (⋃ i, B i) = f '' D := by
  have sub i : A i ⊆ D := cover ▸ Set.subset_iUnion A i
  constructor
  · intro i j ne
    rw [images,images]; apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,eq⟩
    exact Set.disjoint_left.mp (disj ne) hx (h (sub j hy) (sub i hx) eq ▸ hy)
  · rw [← cover,Set.image_iUnion]; exact congrArg (fun d : I → Set Y => ⋃ i, d i) (funext images)

private theorem graph_sum {X Y B T : Type*} [AddCommMonoid T] {l u w : ℕ}
    (carrier : B → Set Y) (weight : B → T) (a : Fin l → Set X) (D : Set X)
    (cover : (⋃ i, a i) = D) (disjoint : Pairwise (fun i j => Disjoint (a i) (a j)))
    (f g : X → Y) (hf : Set.InjOn f D) (hg : Set.InjOn g D)
    (pair : ∀ i, ∃ b c, carrier b = f '' a i ∧ carrier c = g '' a i ∧ weight b = weight c)
    (b : Fin u → B) (c : Fin w → B) (bd : Pairwise (fun i j => Disjoint (carrier (b i)) (carrier (b j))))
    (cd : Pairwise (fun i j => Disjoint (carrier (c i)) (carrier (c j))))
    (bc : (⋃ i, carrier (b i)) = f '' D) (cc : (⋃ j, carrier (c j)) = g '' D)
    (ind : ∀ {u w : ℕ} (a : Fin u → B) (b : Fin w → B),
      Pairwise (fun i j => Disjoint (carrier (a i)) (carrier (a j))) →
      Pairwise (fun i j => Disjoint (carrier (b i)) (carrier (b j))) →
      (⋃ i, carrier (a i)) = (⋃ i, carrier (b i)) → (∑ i, weight (a i)) = ∑ j, weight (b j)) :
    (∑ i, weight (b i)) = ∑ j, weight (c j) := by
  choose left right hl hr eq using pair
  obtain ⟨dl,cl⟩ := projected_disjoint_union a (carrier ∘ left) D f hf cover disjoint hl
  obtain ⟨dr,cr⟩ := projected_disjoint_union a (carrier ∘ right) D g hg cover disjoint hr
  exact (ind b left bd dl (bc.trans cl.symm)).trans
    ((Finset.sum_congr rfl (fun i _ => eq i)).trans (ind right c dr cd (cr.trans cc.symm)))

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)}
  (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable {n : ℕ}


variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)


variable {k : ℕ}
def ChartPiece.tensorWeight (a : ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG k)
    (ha : a.measurable O v hO P S) : TensorProduct C R W :=
  Rmap (a.residueWeight O v hv hO P S ha) ⊗ₜ[C] Vmap (pieceClass a.value.domain a.value.definable)

set_option maxHeartbeats 800000 in
include powers hs resBalance valBalance lang in
theorem graph_projection_sums
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))
    {N l u w : ℕ} (a : Fin l → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG N)
    (ha : ∀ i, (a i).measurable O v hO P S) (nonempty : ∀ i, (a i).residue.Nonempty)
    (disjoint : Pairwise (fun i j => Disjoint ((a i).carrier s) ((a j).carrier s)))
    (D : Set (Fin N → Additive (PositiveRV O))) (cover : (⋃ i, (a i).carrier s) = D)
    (lft rgt : Fin k → Fin N) (il : Set.InjOn (fun z : Fin N → Additive (PositiveRV O) => z ∘ lft) D)
    (ir : Set.InjOn (fun z : Fin N → Additive (PositiveRV O) => z ∘ rgt) D)
    (b : Fin u → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG k)
    (c : Fin w → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG k)
    (hb : ∀ i, (b i).measurable O v hO P S) (hc : ∀ j, (c j).measurable O v hO P S)
    (bd : Pairwise (fun i j => Disjoint ((b i).carrier s) ((b j).carrier s)))
    (cd : Pairwise (fun i j => Disjoint ((c i).carrier s) ((c j).carrier s)))
    (bc : (⋃ i, (b i).carrier s) = (fun z => z ∘ lft) '' D)
    (cc : (⋃ i, (c i).carrier s) = (fun z => z ∘ rgt) '' D) :
    ∑ i, (b i).tensorWeight O v hv hO P S Rmap Vmap (C := C) (hb i) =
      ∑ j, (c j).tensorWeight O v hv hO P S Rmap Vmap (C := C) (hc j) := by
  let B := {t : ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG k // t.measurable O v hO P S}
  let carrier (b : B) := b.val.carrier s
  let weight (b : B) := b.val.tensorWeight O v hv hO P S Rmap Vmap (C := C) b.property
  let raw (i : Fin l) := (a i).carrier s
  let f (z : Fin N → Additive (PositiveRV O)) := z ∘ lft
  let g (z : Fin N → Additive (PositiveRV O)) := z ∘ rgt
  have pair (i : Fin l) : ∃ b c : B, carrier b = f '' raw i ∧ carrier c = g '' raw i ∧ weight b = weight c := by
    have sub := subset_cover raw D cover i
    obtain ⟨b,c,hb,hc,ble,cle,eq⟩ := graph_piece_tensors O v hv hO P powers S lang Rmap Vmap (C := C) s hs
      (a i) lft rgt (ha i) (nonempty i) (il.mono sub) (ir.mono sub)
    exact ⟨⟨b,hb⟩,⟨c,hc⟩,ble,cle,eq⟩
  apply graph_sum carrier weight raw D cover disjoint f g il ir pair
    (fun i => ⟨b i,hb i⟩) (fun j => ⟨c j,hc j⟩) bd cd bc cc
  intro h t x y
  exact equal_chart_sums O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
    (fun i => (x i).val) (fun j => (y j).val) (fun i => (x i).property) (fun j => (y j).property)

end GeneralizedEuler.Section4
