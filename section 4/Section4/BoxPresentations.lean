module

public import Section4.AlphabetRankProfiles
public import Section4.ValueEmbedding
public import Section4.TaggedValueClasses
import all Section4.ValueEmbedding
import all Section4.ValueScaleAlphabet
import all Section4.AlphabetRankProfiles
import all Section4.BoxClassComparison
import all Section4.OrderedBoxCuts
import all Section4.BoxMultiplicity
import all Section4.ValueBoxProducts
import all Section4.Factors

/-! Concrete tagged box objects and their scissor sums in each degree.
An embedding of the coordinate space transports the entire presentation,
including its tags and its fixed-base definitions. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open FirstOrder Set ValueObject
variable {F V C : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  [LinearOrder C] [BoundedOrder C] [Nontrivial C] [Fintype C]
  {J : Language} [J.Structure V] (G : Submodule F V)

structure Alphabet (C : Type*) [LinearOrder C] [BoundedOrder C] where
  width : C → V
  old : ∀ c, width c ∈ G
  positive : ∀ c, c ≠ ⊥ → c ≠ ⊤ → 0 < width c
  increasing : ∀ a b, a ≠ ⊥ → b ≠ ⊤ → a < b → width b ∉ scaleSpace F (width a)
  filler : C
  interior : filler ≠ ⊥ ∧ filler ≠ ⊤

structure BoxLanguage : Prop where
  arithmetic : ValueLanguage (J := J) G
  leDef : ∀ t ∈ G, (G : Set V).Definable J {x : Unit → V | x () ≤ t}
  intervals : ∀ t ∈ G, (G : Set V).Definable J (intervalPiece t)
  point : (G : Set V).Definable J ({0} : Set (Fin 1 → V))
  ray : (G : Set V).Definable J (upperRay 0)

variable {G} (B : Alphabet G C) (L : BoxLanguage (J := J) G)

def boxCarrier {k} (a : Fin k → C) := coordinateBox (scalePiece B.width ∘ a)

omit [Nontrivial C] [Fintype C] in
include L in
theorem boxCarrier_definable {k} (a : Fin k → C) : (G : Set V).Definable J (boxCarrier B a) :=
  coordinateBox_definable _ (fun i => scalePiece_definable G B.width B.old L.intervals L.point L.ray (a i))

def sideClass (c : C) := pieceClass _ (scalePiece_definable G B.width B.old L.intervals L.point L.ray c)

def unionValue {m k} (a : Fin m → Fin k → C) := ∑ i, pieceClass _ (boxCarrier_definable B L (a i))

def shapes {m k : ℕ} (a : Fin m → Fin k → C) : Multiset (Shape C k) :=
  Finset.univ.val.map (fun i => normalize (a i))

omit [Nontrivial C] [Fintype C] in
theorem unionValue_weight {m k} (a : Fin m → Fin k → C) :
    unionValue B L a = BoxMultiplicity.weight (boxWeight (sideClass B L)) (shapes a) := by
  calc unionValue B L a = ∑ i, boxWeight (sideClass B L) (normalize (a i)) := by
         apply Finset.sum_congr rfl; intro i _
         rw [boxWeight,weight_normalize]
         exact coordinateBox_class _ _ (fun j => scalePiece_definable G B.width B.old L.intervals L.point L.ray (a i j))
       _ = _ := by simp only [BoxMultiplicity.weight,shapes,Finset.sum,Multiset.map_map]; rfl

omit [BoundedOrder C] [Nontrivial C] [Fintype C] in
theorem shape_profiles {m k} (a : Fin m → Fin k → C) : profiles (shapes a) = range (fun i => tails (a i)) := by
  ext q
  change (∃ z ∈ (Finset.univ : Finset (Fin m)).val.map (fun i => normalize (a i)), tails z = q) ↔ _
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hb
    exact ⟨i,(tails_normalize (a i)).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨normalize (a i),Multiset.mem_map.mpr ⟨i,by simp,rfl⟩,tails_normalize _⟩


theorem unionValue_eq_of_counts (k : ℕ) {m n} (a : Fin m → Fin (k+1) → C) (b : Fin n → Fin (k+1) → C)
    (same : {q | Maximal (· ∈ range (fun i => boxScaleCounts (F := F) (side B.width ∘ a i) (cutoff B.width))) q} =
      {q | Maximal (· ∈ range (fun j => boxScaleCounts (F := F) (side B.width ∘ b j) (cutoff B.width))) q})
    (bounded geometric : SemiringOfSets (J := J) (G : Set V) →+* ℤ)
    (bp : bounded (pieceClass _ L.point) = 1) (br : bounded (pieceClass _ L.ray) = 0)
    (gp : geometric (pieceClass _ L.point) = 1) (gr : geometric (pieceClass _ L.ray) = -1)
    (eb : bounded (unionValue B L a) = bounded (unionValue B L b))
    (eg : geometric (unionValue B L a) = geometric (unionValue B L b)) :
    unionValue B L a = unionValue B L b := by
  have maxima := maxima_of_geometric_counts B.width B.positive B.increasing a b same
  rw [← shape_profiles a,← shape_profiles b] at maxima
  rw [unionValue_weight,unionValue_weight] at eb eg ⊢
  exact value_products_eq_of_maximal_profiles G B.width B.old L.intervals L.point L.ray k L.arithmetic L.leDef
    B.filler B.interior B.positive B.increasing bounded geometric bp br gp gr (shapes a) (shapes b) maxima eb eg

variable {W : Type*} {H : Language} [H.Structure W] (A : Set W) (ι : V ↪ W)
  (defMap : ∀ {n} {D : Set (Fin n → V)}, (G : Set V).Definable J D → A.Definable H (mapTuples ι '' D))

def taggedBoxes {m k} (a : Fin m → Fin k → C) : Over (J := H) A k where
  tags := m
  piece i := mapTuples ι '' boxCarrier B (a i)
  isDefinable i := defMap (boxCarrier_definable B L (a i))

omit [Nontrivial C] [Fintype C] in
theorem taggedBoxes_class {m k} (a : Fin m → Fin k → C) :
    taggedValueClass A (taggedBoxes B L A ι defMap a) =
      (embeddingMeasure (G : Set V) A ι defMap).descend (unionValue B L a) := by
  rw [taggedValueClass_eq_sum,unionValue,map_sum]
  exact Finset.sum_congr rfl (fun i _ => (PieceMeasure.descend_piece (embeddingMeasure (G : Set V) A ι defMap) _ (boxCarrier_definable B L (a i))).symm)

end GeneralizedEuler.Section4.PaddedBox
