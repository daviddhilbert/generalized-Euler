module

public import Section4.FiniteScaleAlphabet
import all Section4.BoxPresentations
import all Section4.ValueScaleAlphabet
import all Section4.ValueBoxProducts
import all Section4.BoundedIntervalScissors

/-! Arbitrary positive- and base-width box presentations normalize
simultaneously to one finite scale alphabet. This preserves the actual
scissor sums in their ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open FirstOrder Set ValueObject
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup V] [LinearOrder V]
  [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V] {J : Language} [J.Structure V] (G : Submodule F V)

def unarySide : BoxSide V → Set (Fin 1 → V)
  | .point => {0}
  | .bounded b => intervalPiece b
  | .ray => upperRay 0

structure Presentation (k : ℕ) where
  tags : ℕ
  axes : Fin tags → Fin k → BoxSide V
  widths : ∀ i j t, axes i j = .bounded t → t ∈ G ∧ 0 < t

variable {G} {k : ℕ} (L : BoxLanguage (J := J) G)

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
include L in
private theorem unary_definable (d : BoxSide V) (old : ∀ t, d = .bounded t → t ∈ G) :
    (G : Set V).Definable J (unarySide d) := by
  cases d with
  | point => exact L.point
  | ray => exact L.ray
  | bounded t => exact L.intervals _ (old t rfl)

def presentationValue (D : Presentation G k) : SemiringOfSets (J := J) (G : Set V) :=
  ∑ i, pieceClass _ (coordinateBox_definable _ (fun j => unary_definable L (D.axes i j) (fun b h => (D.widths i j b h).1)))

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem presentationValue_zero (D : Presentation G 0) :
    presentationValue L D = (D.tags : SemiringOfSets (J := J) (G : Set V)) := by
  calc presentationValue L D = ∑ _ : Fin D.tags, (1 : SemiringOfSets (J := J) (G : Set V)) := by
         apply Finset.sum_congr rfl; intro i _
         simpa using coordinateBox_class (G : Set V) (fun j => unarySide (D.axes i j))
           (fun j => unary_definable L _ (fun b h => (D.widths i j b h).1))
       _ = _ := by simp

include L in
theorem normalize_presentations (D E : Presentation G k) (step : V) (oldStep : step ∈ G) (positive : 0 < step) :
    ∃ (n : ℕ) (B : Alphabet G (Fin (n+3))) (a : Fin D.tags → Fin k → Fin (n+3))
      (b : Fin E.tags → Fin k → Fin (n+3)),
      presentationValue L D = unionValue B L a ∧ presentationValue L E = unionValue B L b := by
  classical
  let len : BoxSide V → V | .bounded t => t | _ => step
  let lengths (d : Presentation G k) := Finset.univ.image (fun z : Fin d.tags × Fin k => len (d.axes z.1 z.2))
  let pool := insert step (lengths D ∪ lengths E)
  have valid (d : Presentation G k) (t : V) (mem : t ∈ lengths d) : t ∈ G ∧ 0 < t := by
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp mem
    cases h : d.axes i j with
    | point | ray => exact ⟨oldStep,positive⟩
    | bounded t => exact d.widths i j t h
  have good t (ht : t ∈ pool) : t ∈ G ∧ 0 < t := by
    rcases Finset.mem_insert.mp ht with rfl|rest
    · exact ⟨oldStep,positive⟩
    · rcases Finset.mem_union.mp rest with l|r; exact valid D t l; exact valid E t r
  obtain ⟨n,B,cover⟩ := exists_finite_alphabet G pool (fun t h => (good t h).1) (fun t h => (good t h).2)
    ⟨step,Finset.mem_insert_self _ _⟩
  have normalizeOne (d : Presentation G k) (inc : lengths d ⊆ pool) :
      ∃ a : Fin d.tags → Fin k → Fin (n+3), presentationValue L d = unionValue B L a := by
    have chooseAxis (i : Fin d.tags) (j : Fin k) (axis : BoxSide V) (e : d.axes i j = axis)
        (hd : (G : Set V).Definable J (unarySide axis)) :
        ∃ c : Fin (n+3), pieceClass _ hd = sideClass B L c := by
      cases axis with
      | point => exact ⟨⊥,by simp [sideClass,scalePiece,unarySide]⟩
      | ray => exact ⟨⊤,by simp [sideClass,scalePiece,unarySide]⟩
      | bounded t =>
        have present : len (d.axes i j) ∈ lengths d := Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩
        have ht : t ∈ lengths d := by simpa [e,len] using present
        obtain ⟨c,lo,hi,eq⟩ := cover t (inc ht)
        obtain ⟨old,pos⟩ := d.widths i j t e
        have same := interval_class_of_same_scale G L.arithmetic L.leDef L.intervals t (B.width c) old (B.old c)
          pos (B.positive c lo hi) ((scaleSpace_le_iff F).mp eq.ge) ((scaleSpace_le_iff F).mp eq.le)
        exact ⟨c,by simpa [sideClass,scalePiece,unarySide,lo,hi] using same⟩
    let hd (i : Fin d.tags) (j : Fin k) := unary_definable L (d.axes i j) (fun b h => (d.widths i j b h).1)
    choose a law using fun i j => chooseAxis i j _ rfl (hd i j)
    refine ⟨a,Finset.sum_congr rfl (fun i _ => ?_)⟩
    rw [coordinateBox_class _ _ (hd i)]
    change _ = pieceClass (coordinateBox _) _
    rw [coordinateBox_class _ (scalePiece B.width ∘ a i) (fun j => scalePiece_definable G B.width B.old L.intervals L.point L.ray (a i j))]
    exact Finset.prod_congr rfl fun j _ => law i j
  obtain ⟨a,ha⟩ := normalizeOne D (fun t ht => Finset.mem_insert_of_mem (Finset.mem_union_left _ ht))
  obtain ⟨b,hb⟩ := normalizeOne E (fun t ht => Finset.mem_insert_of_mem (Finset.mem_union_right _ ht))
  exact ⟨n,B,a,b,ha,hb⟩

end GeneralizedEuler.Section4.PaddedBox
