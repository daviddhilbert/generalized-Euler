module

public import Section4.NormalizedBoxes
public import Section4.MaximalBoxComparison
import all Section4.NormalizedBoxes
import all Section4.BoxMultiplicity

/-! Realize a dominance inequality by a positive product partition on
sorted box types. The remainder stays in the same downward closure. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open BoxMultiplicity
variable {C R : Type*} [LinearOrder C] [CommSemiring R] (w : C → R)

def boxWeight {k} (b : Shape C k) : R := ∏ i, w (b i)

structure SideCut (a b : C) where
  size : ℕ
  side : Fin size → C
  below : ∀ i, side i ≤ b
  large : ∃ i, side i = b
  small : ∃ i, side i = a
  sum : w b = ∑ i, w (side i)

theorem ordered_box_extract (split : ∀ a b, a ≤ b → Nonempty (SideCut w a b))
    {k} (a b : Shape C k) (lt : a < b) :
    ∃ rest : Multiset (Shape C k),
      boxWeight w b = boxWeight w b + (boxWeight w a + weight (boxWeight w) rest) ∧
      ∀ t ∈ rest, t ≤ b := by
  classical
  let cut (i : Fin k) := (split (a i) (b i) (lt.le i)).some
  let choice := (i : Fin k) → Fin (cut i).size
  let shape (u : choice) := normalize (fun i => (cut i).side (u i))
  let parts : Multiset (Shape C k) := (Finset.univ : Finset choice).val.map shape
  have atOld : b ∈ parts := by
    choose u eq using fun i => (cut i).large
    exact Multiset.mem_map.mpr ⟨u,Finset.mem_univ _,by simpa only [shape,eq] using normalize_sorted b⟩
  have atSmall : a ∈ parts := by
    choose u eq using fun i => (cut i).small
    exact Multiset.mem_map.mpr ⟨u,Finset.mem_univ _,by simpa only [shape,eq] using normalize_sorted a⟩
  have sub {t : Shape C k} (h : t ∈ parts) : t ≤ b := by
    obtain ⟨u,_,rfl⟩ := Multiset.mem_map.mp h
    exact (normalize_mono (fun i => (cut i).below (u i))).trans_eq (normalize_sorted b)
  have total : boxWeight w b = weight (boxWeight w) parts := by
    calc boxWeight w b = ∏ i, ∑ j, w ((cut i).side j) := Finset.prod_congr rfl fun i _ => (cut i).sum
         _ = ∑ u : choice, ∏ i, w ((cut i).side (u i)) := Fintype.prod_sum _
         _ = ∑ u : choice, boxWeight w (shape u) := Finset.sum_congr rfl fun u _ =>
           (weight_normalize w (fun i => (cut i).side (u i))).symm
         _ = _ := by simp only [weight,parts,Finset.sum,Multiset.map_map]; rfl
  let rest := (parts.erase b).erase a
  have left : a ∈ parts.erase b := (Multiset.mem_erase_of_ne lt.ne).mpr atSmall
  have decomposition : parts = b ::ₘ a ::ₘ rest := by rw [Multiset.cons_erase left,Multiset.cons_erase atOld]
  refine ⟨rest,?_,fun t ht => sub (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ht))⟩
  calc boxWeight w b = weight (boxWeight w) parts := total
       _ = _ := by rw [decomposition]; simp [weight]

end GeneralizedEuler.Section4.PaddedBox
