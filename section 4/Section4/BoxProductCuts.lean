module

public import Section4.BoxUnionComparison
import all Section4.BoxMultiplicity

/-! Positive product partitions of padded boxes. Choosing a smaller type
and the old type in each unary partition gives two distinct summands
whenever the two box shapes differ. -/
public section
namespace GeneralizedEuler.Section4
namespace BoxProductCuts
open BoxMultiplicity
variable {C R : Type*} [CommSemiring R]

def pieces : List (List C) → List (List C)
  | [] => [[]]
  | s :: t => s.flatMap fun a => (pieces t).map (List.cons a)

def product (w : C → R) (s : List C) : R := (s.map w).prod

theorem total (w : C → R) (cuts : List (List C)) :
    ((pieces cuts).map (product w)).sum = (cuts.map (fun s => (s.map w).sum)).prod := by
  induction cuts with
  | nil => simp [pieces,product]
  | cons s t ih =>
    simp only [List.map_cons,List.prod_cons,pieces]
    induction s with
    | nil => simp
    | cons a b hb =>
      change (((pieces t).map (List.cons a) ++ b.flatMap _).map (product w)).sum = _
      rw [List.map_append,List.sum_append,hb]
      simp only [List.map_cons,List.sum_cons,add_mul]
      congr 1
      rw [← ih]
      induction pieces t with
      | nil => simp
      | cons x xs ih' =>
        simpa only [List.map_cons,List.sum_cons,product,List.prod_cons,mul_add] using
          congrArg (fun z => w a * product w x + z) ih'

theorem occurs {s : List C} {cuts : List (List C)} :
    s ∈ pieces cuts ↔ List.Forall₂ (fun x d => x ∈ d) s cuts := by
  induction cuts generalizing s with
  | nil => cases s <;> simp [pieces]
  | cons d ds ih =>
    cases s with
    | nil => simp [pieces]
    | cons a t => simp [pieces,ih]

theorem factorwise_le {s t : List C} {cuts : List (List C)} (r : C → C → Prop)
    (top : List.Forall₂ (fun d b => ∀ x ∈ d, r x b) cuts t) (mem : s ∈ pieces cuts) :
    List.Forall₂ r s t := by
  have h := occurs.mp mem
  induction top generalizing s with
  | nil => cases h; exact .nil
  | cons h₀ h₁ ih => cases h with | cons ha ht => exact .cons (h₀ _ ha) (ih (occurs.mpr ht) ht)

private theorem factor_sum (w : C → R) {old : List C} {cuts : List (List C)}
    (split : List.Forall₂ (fun x (d : List C) => w x = (d.map w).sum) old cuts) :
    (cuts.map (fun d => (d.map w).sum)).prod = product w old := by
  induction split with
  | nil => simp [product]
  | cons h _ ih => simpa only [List.map_cons,List.prod_cons,product,h] using congrArg (fun y => _ * y) ih

/-- Map the explicit product partition to box types. Coordinates can be
permuted or forgotten in the type, and repeated summands retain their
multiplicity. All remainder types occur in the original partition. -/
theorem extract_product {T : Type*} [DecidableEq T] (w : C → R) (typeOf : List C → T)
    (value : T → R) (consistent : ∀ s, value (typeOf s) = product w s)
    (old small : List C) (cuts : List (List C))
    (oldMem : List.Forall₂ (fun x d => x ∈ d) old cuts)
    (smallMem : List.Forall₂ (fun x d => x ∈ d) small cuts)
    (split : List.Forall₂ (fun x (d : List C) => w x = (d.map w).sum) old cuts)
    (different : typeOf old ≠ typeOf small) :
    ∃ rest : Multiset T,
      value (typeOf old) = value (typeOf old) + (value (typeOf small) + weight value rest) ∧
      ∀ z ∈ rest, ∃ s ∈ pieces cuts, typeOf s = z := by
  classical
  let boxes : Multiset T := ((pieces cuts).map typeOf : List T)
  have a : typeOf old ∈ boxes := List.mem_map.mpr ⟨old,occurs.mpr oldMem,rfl⟩
  have b : typeOf small ∈ boxes := List.mem_map.mpr ⟨small,occurs.mpr smallMem,rfl⟩
  let rem := (boxes.erase (typeOf old)).erase (typeOf small)
  have b' : typeOf small ∈ boxes.erase (typeOf old) := (Multiset.mem_erase_of_ne different.symm).mpr b
  have terms : boxes = typeOf old ::ₘ typeOf small ::ₘ rem := by
    rw [Multiset.cons_erase b',Multiset.cons_erase a]
  have sum : weight value boxes = value (typeOf old) := by
    rw [consistent]
    change (((pieces cuts).map typeOf).map value).sum = _
    simp only [List.map_map,Function.comp_def,consistent,total]
    exact factor_sum w split
  refine ⟨rem,?_,?_⟩
  · calc value (typeOf old) = weight value boxes := sum.symm
         _ = _ := by rw [terms]; simp [weight]
  · intro z hz
    exact List.mem_map.mp (show z ∈ boxes from Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hz))

end BoxProductCuts
end GeneralizedEuler.Section4
