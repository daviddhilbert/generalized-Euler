module

public import Section4.BoxClassComparison
public import Section4.IntervalScaleCuts
public import Section4.RaySquareScissors
import all Section4.BoundedIntervalScissors

/-! A finite alphabet of positive base widths, together with padding and
the ray. All partitions used for ordered box comparison live in the
unsigned value semiring over the original base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open FirstOrder Set ValueObject
variable {C : Type*} [LinearOrder C] [BoundedOrder C]
  {R : Type*} [CommSemiring R] (w : C → R)

private def threeSideCut {a b c : C} (ac : a ≤ b) (bc : c ≤ b) (sum : w b = w b + (w a + w c)) :
    SideCut w a b where
  size := 3
  side := ![b,a,c]
  below i := by fin_cases i; exact le_rfl; exact ac; exact bc
  large := ⟨0,rfl⟩
  small := ⟨1,rfl⟩
  sum := by simpa [Fin.sum_univ_three,add_assoc] using sum

theorem side_cuts_from_intervals (filler : C) (interior : filler ≠ ⊥ ∧ filler ≠ ⊤)
    (mid : ∀ c, c ≠ ⊥ → c ≠ ⊤ → w c = w c + (w c + w ⊥))
    (nested : ∀ a b, a ≠ ⊥ → b ≠ ⊤ → a < b → w b = w b + (w a + w ⊥))
    (ray : ∀ c, c ≠ ⊥ → c ≠ ⊤ → w ⊤ = w ⊤ + (w c + w ⊥)) :
    ∀ a b, a ≤ b → Nonempty (SideCut w a b) := by
  intro a b h
  rcases h.eq_or_lt with rfl|lt
  · exact ⟨⟨1,fun _ => a,fun _ => le_rfl,⟨0,rfl⟩,⟨0,rfl⟩,by simp⟩⟩
  by_cases rb : b = ⊤
  · subst b; by_cases pa : a = ⊥
    · subst a
      exact ⟨threeSideCut w bot_le le_top (by simpa [add_comm (w filler)] using ray filler interior.1 interior.2)⟩
    · exact ⟨threeSideCut w le_top bot_le (ray a pa lt.ne)⟩
  · by_cases pa : a = ⊥
    · subst a
      exact ⟨threeSideCut w bot_le le_rfl (by simpa [add_comm (w b) (w ⊥)] using mid b lt.ne' rb)⟩
    · exact ⟨threeSideCut w lt.le bot_le (nested a b pa rb lt)⟩

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup V] [LinearOrder V]
  [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {J : Language} [J.Structure V] (G : Submodule F V)
  (width : C → V) (old : ∀ c, width c ∈ G)
  (dom : ∀ t ∈ G, (G : Set V).Definable J (intervalPiece t))
  (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V))) (dr : (G : Set V).Definable J (upperRay 0))

def scalePiece (c : C) : Set (Fin 1 → V) :=
  if c=⊥ then {0} else if c=⊤ then upperRay 0 else intervalPiece (width c)

omit [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F V] [IsOrderedAddMonoid V] in
include old dom dp dr in
theorem scalePiece_definable (c : C) : (G : Set V).Definable J (scalePiece width c) := by
  unfold scalePiece
  split <;> first | exact dp | (split <;> first | exact dr | exact dom _ (old c))

local notation "weightOf" => fun c => pieceClass _ (scalePiece_definable G width old dom dp dr c)

variable [Nontrivial C] [Fintype C]
theorem value_products_eq_of_maximal_profiles (k : ℕ) (lang : ValueLanguage (J := J) G)
    (leDef : ∀ t ∈ G, (G : Set V).Definable J {x : Unit → V | x () ≤ t})
    (filler : C) (interior : filler ≠ ⊥ ∧ filler ≠ ⊤)
    (pos : ∀ c, c ≠ ⊥ → c ≠ ⊤ → 0 < width c)
    (scales : ∀ a b, a ≠ ⊥ → b ≠ ⊤ → a < b → width b ∉ scaleSpace F (width a))
    (bounded geometric : SemiringOfSets (J := J) (G : Set V) →+* ℤ)
    (bp : bounded (pieceClass _ dp) = 1) (br : bounded (pieceClass _ dr) = 0)
    (gp : geometric (pieceClass _ dp) = 1) (gr : geometric (pieceClass _ dr) = -1)
    (s t : Multiset (Shape C (k+1)))
    (maximal : {q | Maximal (· ∈ profiles s) q} = {q | Maximal (· ∈ profiles t) q})
    (eb : bounded (BoxMultiplicity.weight (boxWeight weightOf) s) = bounded (BoxMultiplicity.weight (boxWeight weightOf) t))
    (eg : geometric (BoxMultiplicity.weight (boxWeight weightOf) s) = geometric (BoxMultiplicity.weight (boxWeight weightOf) t)) :
    BoxMultiplicity.weight (boxWeight weightOf) s = BoxMultiplicity.weight (boxWeight weightOf) t := by
  let W := weightOf
  have point : W ⊥ = pieceClass _ dp := by simp [W,scalePiece]
  have top : W ⊤ = pieceClass _ dr := by simp [W,scalePiece]
  have inside {c : C} (lo : c ≠ ⊥) (hi : c ≠ ⊤) : W c = pieceClass _ (dom _ (old c)) := by simp [W,scalePiece,lo,hi]
  have mid (c : C) (lo : c ≠ ⊥) (hi : c ≠ ⊤) : W c = W c + (W c + W ⊥) := by
    rw [inside lo hi,point]; exact interval_midpoint_scissors G lang leDef dom dp _ (old c) (pos c lo hi)
  have nested (a b : C) (lo : a ≠ ⊥) (hi : b ≠ ⊤) (lt : a < b) : W b = W b + (W a + W ⊥) := by
    have na := (lt_of_lt_of_le lt le_top).ne
    have nb := (lt_of_le_of_lt bot_le lt).ne'
    rw [inside nb hi,inside lo na,point]
    exact smaller_interval_scissors G lang leDef dom dp _ _ (old a) (old b) (pos a lo na) (pos b nb hi) (scales a b lo hi lt)
  have ray (a : C) (lo : a ≠ ⊥) (hi : a ≠ ⊤) : W ⊤ = W ⊤ + (W a + W ⊥) := by
    rw [inside lo hi,top,point,add_comm (pieceClass _ dr)]
    exact ray_interval_scissors G lang _ (old a) (pos a lo hi) (dom _ (old a)) dr dp
  apply compare_products_of_box_profiles W k (side_cuts_from_intervals W filler interior mid nested ray) mid
    _ bounded geometric (point ▸ bp) (top ▸ br) (point ▸ gp) (top ▸ gr) s t maximal eb eg
  rw [point,top,← pow_two]
  exact ray_square_scissors G lang dr dp

end GeneralizedEuler.Section4.PaddedBox
