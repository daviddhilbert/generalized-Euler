module

public import Section4.BoxFaces
import all Section4.NormalizedBoxes
import all Section4.OrderedBoxCuts
import all Section4.BoxFaces
import all Section4.BoxMultiplicity

/-! Equality of sums of padded box products from two Euler numbers
and the maximal vectors of cumulative scale counts. Only the unary
cut formulas and the diagonal cut of the ray square enter. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open BoxMultiplicity Finset
variable {C R : Type*} [LinearOrder C] [BoundedOrder C] [Nontrivial C] [CommSemiring R]
variable {k : ℕ}

def profiles (s : Multiset (Shape C k)) : Set (C → ℕ) := (fun x : Shape C k => tails x) '' {x | x ∈ s}

omit [BoundedOrder C] [Nontrivial C] in
theorem maximal_profile_iff (s : Multiset (Shape C k)) (q : Shape C k) :
    Maximal (· ∈ s) q ↔ Maximal (· ∈ profiles s) (tails q) := by
  constructor
  · rintro ⟨hit,top⟩
    refine ⟨⟨q,hit,rfl⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩ le
    exact (tails_le_iff _ _).mpr (top hx ((tails_le_iff _ _).mp le))
  · rintro ⟨⟨t,ht,eq⟩,top⟩
    have same : t=q := le_antisymm ((tails_le_iff _ _).mp eq.le) ((tails_le_iff _ _).mp eq.ge)
    refine ⟨same ▸ ht,?_⟩
    intro x hx le
    exact (tails_le_iff _ _).mp (top ⟨x,hx,rfl⟩ ((tails_le_iff _ _).mpr le))

variable [Fintype C] (w : C → R)

theorem compare_products_of_box_profiles (k : ℕ)
    (split : ∀ a b, a ≤ b → Nonempty (SideCut w a b))
    (mid : ∀ c : C, c ≠ ⊥ → c ≠ ⊤ → w c = w c + (w c + w ⊥))
    (rays : w ⊤ * w ⊤ = w ⊤ * w ⊤ + (w ⊤ * w ⊤ + w ⊥ * w ⊤))
    (bounded geometric : R →+* ℤ) (bp : bounded (w ⊥) = 1) (br : bounded (w ⊤) = 0)
    (gp : geometric (w ⊥) = 1) (gr : geometric (w ⊤) = -1)
    (s t : Multiset (Shape C (k+1)))
    (maximal : {q | Maximal (· ∈ profiles s) q} = {q | Maximal (· ∈ profiles t) q})
    (eb : bounded (weight (boxWeight w) s) = bounded (weight (boxWeight w) t))
    (eg : geometric (weight (boxWeight w) s) = geometric (weight (boxWeight w) t)) :
    weight (boxWeight w) s = weight (boxWeight w) t := by
  classical
  let P := pointShape (C := C) (k+1)
  let H := rayShape (C := C) k
  have ne : P ≠ H := by
    intro same
    let v (i : Fin (k+1)) : C := if i=0 then ⊤ else ⊥
    have eq := congrArg (fun z : Shape C (k+1) => z ((Tuple.sort v).symm 0)) same
    change ⊥ = v ((Tuple.sort v) ((Tuple.sort v).symm 0)) at eq
    simp [v] at eq
  let face (q : Shape C (k+1)) := if h : q ≠ P ∧ q ≠ H then (duplicated_box_face w mid rays q h).choose else q
  have spec (q) (h : q ≠ P ∧ q ≠ H) : face q ≤ q ∧ boxDim (face q) < boxDim q ∧
      boxWeight w q = boxWeight w q + (boxWeight w q + boxWeight w (face q)) := by
    simpa only [face,dite_eq_left h] using (duplicated_box_face w mid rays q h).choose_spec
  have pw : boxWeight w P = w ⊥ ^(k+1) := by simp [boxWeight,P,pointShape]
  have hw : boxWeight w H = w ⊤ * (w ⊥)^k := by
    unfold H rayShape boxWeight
    rw [weight_normalize,Fin.prod_univ_succ]; simp
  let : Fintype (Shape C (k+1)) := Fintype.ofInjective (fun z : Shape C (k+1) => z.toFun) DFunLike.coe_injective
  refine compare_by_maximal_types (boxWeight w) P H ne boxDim face (fun q h => (spec q h).2.2)
    (fun q h => (spec q h).2.1) (fun q h => (spec q h).1) (ordered_box_extract w split)
    bounded.toAddMonoidHom geometric.toAddMonoidHom ?_ ?_ ?_ ?_ s t ?_ eb eg
  · simp [pw,bp]
  · simp [hw,br]
  · simp [pw,gp]
  · simp [hw,gr,gp]
  · ext q
    exact (maximal_profile_iff s q).trans (((congrArg (tails q ∈ ·) maximal).to_iff).trans (maximal_profile_iff t q).symm)

end GeneralizedEuler.Section4.PaddedBox
