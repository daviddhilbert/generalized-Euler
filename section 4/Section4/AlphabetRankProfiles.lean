module

public import Section4.ValueScaleAlphabet
public import Section4.BoxRanksFromLifts
public import Section4.ValueBoxProducts
import all Section4.ValueScaleAlphabet
import all Section4.BoxScaleProfiles
import all Section4.ValueBoxes
import all Section4.NormalizedBoxes
import all Section4.BoxClassComparison
import all Section4.ValueBoxProducts
import all Section4.BoundedIntervalScissors

/-! Identify geometric scale counts of an actual padded value box with
the cumulative multiplicities of its ordered factors. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open Set
variable {C F V : Type*} [LinearOrder C] [BoundedOrder C] [Nontrivial C]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup V] [LinearOrder V]
  [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V] (width : C → V)

def side (c : C) : BoxSide V := if c=⊥ then .point else if c=⊤ then .ray else .bounded (width c)
def cutoff (c : C) : V := if c=⊥ ∨ c=⊤ then 0 else width c

omit [Nontrivial C] [IsOrderedAddMonoid V] in
theorem side_domain (c : C) (x : V) : x ∈ (side width c).domain ↔ (fun _ : Fin 1 => x) ∈ scalePiece width c := by
  unfold side scalePiece
  split
  · simp [BoxSide.domain,funext_iff]
  · split <;> rfl

variable (pos : ∀ c, c ≠ ⊥ → c ≠ ⊤ → 0 < width c)
  (scales : ∀ a b, a ≠ ⊥ → b ≠ ⊤ → a < b → width b ∉ scaleSpace F (width a))

include pos scales in
private theorem survives_cutoff (c x : C) (hc : c ≠ ⊤) :
    (side width x).survives (scaleSpace F (cutoff width c)) ↔ c < x := by
  by_cases lo : x=⊥
  · subst x; simp [side,BoxSide.survives]
  by_cases hi : x=⊤
  · subst x; simp [side,BoxSide.survives,lt_top_iff_ne_top,hc]
  by_cases bottom : c=⊥
  · subst c; simp [side,lo,hi,cutoff,scaleSpace_zero,BoxSide.survives,(pos x lo hi).ne',bot_lt_iff_ne_bot]
  simp only [side,lo,hi,cutoff,bottom,hc,or_self,ite_false,BoxSide.survives]
  constructor
  · intro out
    by_contra! bad
    rcases bad.eq_or_lt with rfl|lt
    · exact out (self_mem_scaleSpace F _)
    · rcases width_scale_total (F := F) (pos x lo hi).le (pos c bottom hc).le with le|le
      · exact out (le (self_mem_scaleSpace F _))
      · exact scales x c lo hc lt (le (self_mem_scaleSpace F _))
  · exact scales c x bottom hi

omit [Nontrivial C] in
private theorem top_tail {k} (x : Fin k → C) : tails x ⊤ = 0 := by simp [tails]

include pos scales in
theorem counts_of_box_word {k} (x : Fin k → C) (c : C) :
    boxScaleCounts (F := F) (side width ∘ x) (cutoff width) c = tails x (if c=⊤ then ⊥ else c) := by
  have count (d : C) (hd : d ≠ ⊤) :
      boxScaleCounts (F := F) (side width ∘ x) (cutoff width) d = tails x d := by
    classical
    simp only [boxScaleCounts,Nat.card_eq_fintype_card,Fintype.card_subtype,tails,Function.comp_apply]
    congr 1; ext j; simp [survives_cutoff width pos scales d (x j) hd]
  by_cases h : c=⊤
  · subst c
    simpa [boxScaleCounts,cutoff] using count ⊥ bot_ne_top
  · simpa [h] using count c h

omit [Nontrivial C] in
/-- Repeating the dimension cutoff at the top does not change comparisons
of actual profiles, whose count strictly above the ray is zero. -/
private theorem repeat_le_iff {a b : C → ℕ} (za : a ⊤ = 0) (zb : b ⊤ = 0) :
    (fun x => a (if x=⊤ then ⊥ else x)) ≤ (fun x => b (if x=⊤ then ⊥ else x)) ↔ a ≤ b := by
  constructor
  · intro h x
    by_cases e : x=⊤
    · simp [e,za,zb]
    · simpa [e] using h x
  · exact fun h x => h _

include pos scales in
theorem maxima_of_geometric_counts {k} {I J : Type} (a : I → Fin k → C) (b : J → Fin k → C)
    (same : {q | Maximal (· ∈ range (fun i => boxScaleCounts (F := F) (side width ∘ a i) (cutoff width))) q} =
      {q | Maximal (· ∈ range (fun j => boxScaleCounts (F := F) (side width ∘ b j) (cutoff width))) q}) :
    {q | Maximal (· ∈ range (fun i => tails (a i))) q} = {q | Maximal (· ∈ range (fun j => tails (b j))) q} := by
  let rep (p : C → ℕ) (x : C) := p (if x=⊤ then ⊥ else x)
  have read {L : Type} (d : L → Fin k → C) {q : C → ℕ} (z : q ⊤ = 0) :
      Maximal (· ∈ range (fun i => tails (d i))) q ↔
      Maximal (· ∈ range (fun i => boxScaleCounts (F := F) (side width ∘ d i) (cutoff width))) (rep q) := by
    have eq i : boxScaleCounts (F := F) (side width ∘ d i) (cutoff width) = rep (tails (d i)) :=
      funext (counts_of_box_word width pos scales (d i))
    simp_rw [eq]
    constructor
    · rintro ⟨hit,max⟩
      obtain ⟨u,rfl⟩ := hit
      refine ⟨⟨u,rfl⟩,?_⟩
      rintro _ ⟨v,rfl⟩ le
      exact (repeat_le_iff (top_tail _) z).mpr (max ⟨v,rfl⟩ ((repeat_le_iff z (top_tail _)).mp le))
    · rintro ⟨⟨u,hu⟩,max⟩
      have h := le_antisymm ((repeat_le_iff (top_tail _) z).mp hu.le) ((repeat_le_iff z (top_tail _)).mp hu.ge)
      refine ⟨⟨u,h⟩,?_⟩
      rintro _ ⟨v,rfl⟩ le
      exact (repeat_le_iff (top_tail _) z).mp (max ⟨v,rfl⟩ ((repeat_le_iff z (top_tail _)).mpr le))
  ext q
  by_cases z : q ⊤ = 0
  · exact (read a z).trans (((congrArg (rep q ∈ ·) same).to_iff).trans (read b z).symm)
  · have out {L : Type} (d : L → Fin k → C) : ¬ Maximal (· ∈ range (fun i => tails (d i))) q := by
      rintro ⟨⟨i,rfl⟩,_⟩; exact z (top_tail _)
    exact iff_of_false (out a) (out b)

end GeneralizedEuler.Section4.PaddedBox
