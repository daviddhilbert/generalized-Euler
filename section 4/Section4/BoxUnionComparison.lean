module

public import Section4.BoxMultiplicity
import all Section4.BoxMultiplicity

/-! From a common collection of dominated box types and the two Euler
characteristics to equality of positive classes, keeping the point and
single ray as the two exceptional types. -/
public section
namespace GeneralizedEuler.Section4.BoxMultiplicity
variable {T M : Type*} [DecidableEq T] [Fintype T] [AddCommMonoid M]

omit [Fintype T] in
/-- Add one copy of each requested type while retaining every original
summand. Each available cut supplies a copy and a finite remainder. -/
theorem insert_dominated_types (w : T → M) (s : Multiset T) (wanted : Finset T)
    (extract : ∀ p ∈ wanted, p ∈ s ∨ ∃ b ∈ s, ∃ r : Multiset T, w b = w b + (w p + weight w r)) :
    ∃ add : Multiset T, weight w s = weight w (s + add) ∧ ∀ p ∈ wanted, p ∈ s + add := by
  classical
  induction wanted using Finset.induction_on with
  | empty => exact ⟨0,by simp,by simp⟩
  | @insert p a hp ih =>
    obtain ⟨more,eq,all⟩ := ih (fun q h => extract q (Finset.mem_insert_of_mem h))
    rcases extract p (Finset.mem_insert_self p a) with already|⟨b,hb,r,cut⟩
    · refine ⟨more,eq,?_⟩
      intro q hq; rcases Finset.mem_insert.mp hq with rfl|h
      · exact Multiset.mem_add.mpr (.inl already)
      · exact all q h
    · let rest := p ::ₘ r
      have has : b ∈ s + more := Multiset.mem_add.mpr (.inl hb)
      obtain ⟨tail,tailEq⟩ := Multiset.exists_cons_of_mem has
      refine ⟨more + rest,?_,?_⟩
      · rw [← add_assoc,weight_add,← eq]
        apply (show weight w s + weight w rest = weight w s from ?_).symm
        rw [eq,tailEq]
        simp only [weight,rest,Multiset.map_cons,Multiset.sum_cons]
        calc w b + (Multiset.map w tail).sum + (w p + (Multiset.map w r).sum) =
            (w b + (w p + weight w r)) + (Multiset.map w tail).sum := by unfold weight; ac_rfl
             _ = _ := by rw [← cut]
      · intro q hq
        rw [← add_assoc]
        rcases Finset.mem_insert.mp hq with rfl|h
        · exact Multiset.mem_add.mpr (.inr (Multiset.mem_cons_self _ _))
        · exact Multiset.mem_add.mpr (.inl (all q h))

omit [Fintype T] in
private theorem split_exceptional (s : Multiset T) {p r : T} (ne : p ≠ r) :
    s = s.filter (fun x => x ≠ p ∧ x ≠ r) + s.count p • {p} + s.count r • {r} := by
  classical
  ext q
  simp only [Multiset.count_add,Multiset.count_nsmul,Multiset.count_singleton,Multiset.count_filter]
  by_cases hp : q = p <;> by_cases hr : q = r <;> simp_all

theorem compare_box_unions (w : T → M) (p r : T) (ne : p ≠ r) (dim : T → ℕ) (face : T → T)
    (cut : ∀ x, x ≠ p ∧ x ≠ r → w x = w x + (w x + w (face x)))
    (lower : ∀ x, x ≠ p ∧ x ≠ r → dim (face x) < dim x)
    (bounded geometric : M →+ ℤ) (bp : bounded (w p) = 1) (br : bounded (w r) = 0)
    (gp : geometric (w p) = 1) (gr : geometric (w r) = -1)
    (s t : Multiset T)
    (available : ∀ u ∈ ({s,t} : Set (Multiset T)), ∀ q, q ≠ p ∧ q ≠ r →
      q ∈ u ∨ ∃ b ∈ u, ∃ rest : Multiset T, w b = w b + (w q + weight w rest))
    (eb : bounded (weight w s) = bounded (weight w t))
    (eg : geometric (weight w s) = geometric (weight w t)) : weight w s = weight w t := by
  classical
  let reg (x : T) := x ≠ p ∧ x ≠ r
  let needed := Finset.univ.filter reg
  have requested (x : T) : x ∈ needed ↔ reg x := by simp [needed]
  obtain ⟨a,ha,pa⟩ := insert_dominated_types w s needed (fun x hx => available s (by simp) x ((requested x).mp hx))
  obtain ⟨b,hb,pb⟩ := insert_dominated_types w t needed (fun x hx => available t (by simp) x ((requested x).mp hx))
  obtain ⟨u,v,hu,hv,counts⟩ := equalize reg dim face w cut lower (s+a) (t+b)
    (fun x reg => ⟨pa x ((requested x).mpr reg),pb x ((requested x).mpr reg)⟩)
  have es := ha.trans hu
  have et := hb.trans hv
  rw [es,et] at eb eg ⊢
  have common : u.filter reg = v.filter reg := by
    ext x; by_cases hx : reg x
    · simpa only [Multiset.count_filter_of_pos hx] using counts x hx
    · simp only [Multiset.count_filter_of_neg hx]
  have eval (m : Multiset T) :
      weight w m = weight w (m.filter reg) + m.count p • w p + m.count r • w r := by
    conv_lhs => rw [split_exceptional m ne]
    simp [weight,reg,Multiset.nsmul_singleton,Multiset.map_replicate]
  rw [eval u,eval v,common] at eb eg ⊢
  simp only [map_add,map_nsmul,bp,br,gp,gr,nsmul_eq_mul,mul_one,mul_neg_one] at eb eg
  have points : u.count p = v.count p := by omega
  have rays : u.count r = v.count r := by omega
  rw [points,rays]

end GeneralizedEuler.Section4.BoxMultiplicity
