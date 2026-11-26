module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Tactic

/-! Positive comparison of finite box unions after all dominated types have
been made present. Midpoint and diagonal cuts duplicate a nonexceptional
box and add one face of strictly smaller dimension. -/
public section
namespace GeneralizedEuler.Section4
namespace BoxMultiplicity
open Finset
variable {T M : Type*} [Fintype T] [DecidableEq T] [AddCommMonoid M]

def weight (w : T → M) (s : Multiset T) : M := (s.map w).sum

omit [Fintype T] [DecidableEq T] in
theorem weight_add (w : T → M) (s t : Multiset T) : weight w (s+t) = weight w s + weight w t := by
  simp [weight]

omit [Fintype T] [DecidableEq T] in
private theorem absorb_cut (w : T → M) (s : Multiset T) {p t : T} (present : p ∈ s)
    (cut : w p = w p + (w p + w t)) (n : ℕ) :
    weight w (s + n • ({p} + {t} : Multiset T)) = weight w s := by
  have one : weight w s + (w p + w t) = weight w s := by
    obtain ⟨r,hr⟩ := Multiset.exists_cons_of_mem present
    rw [hr]
    simp only [weight,Multiset.map_cons,Multiset.sum_cons]
    calc w p + (Multiset.map w r).sum + (w p + w t) =
        (w p + (w p + w t)) + (Multiset.map w r).sum := by ac_rfl
         _ = _ := by rw [← cut]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul,← add_assoc,weight_add,ih,weight_add]
    simpa [weight] using one

variable (regular : T → Prop) [DecidablePred regular] (dim : T → ℕ) (face : T → T)
  (w : T → M) (cut : ∀ t, regular t → w t = w t + (w t + w (face t)))
  (lower : ∀ t, regular t → dim (face t) < dim t)

private def additions (s t : Multiset T) (active : Finset T) : Multiset T :=
  ∑ p ∈ active, (t.count p - s.count p) • ({p} + {face p})

omit [Fintype T] [DecidablePred regular] in
include cut in
private theorem keep_weight (s t : Multiset T) (active : Finset T)
    (eligible : ∀ p ∈ active, regular p ∧ p ∈ s) :
    weight w (s + additions face s t active) = weight w s := by
  classical
  induction active using Finset.induction_on with
  | empty => simp [additions]
  | @insert p a hp ih =>
    have ⟨reg,mem⟩ := eligible p (Finset.mem_insert_self p a)
    have prev := ih (fun q hq => eligible q (Finset.mem_insert_of_mem hq))
    rw [additions,Finset.sum_insert hp,add_comm ((t.count p - s.count p) • _),← add_assoc]
    rw [absorb_cut w _ (Multiset.mem_add.mpr (Or.inl mem)) (cut p reg),← prev]
    rfl

omit [Fintype T] in
private theorem count_additions (s t : Multiset T) (active : Finset T) (q : T)
    (off : ∀ p ∈ active, face p ≠ q) :
    (additions face s t active).count q = if q ∈ active then t.count q - s.count q else 0 := by
  classical
  induction active using Finset.induction_on with
  | empty => simp [additions]
  | @insert p a hp ih =>
    have prev := ih (fun r hr => off r (Finset.mem_insert_of_mem hr))
    have nf := off p (Finset.mem_insert_self p a)
    simp only [additions,Finset.sum_insert hp,Multiset.count_add] at *
    rw [prev]
    by_cases eq : p=q
    · subst q; simp [nf.symm,hp]
    · simp [nf.symm,Ne.symm eq]

include cut lower in
/-- Equalize every regular multiplicity down to dimension zero without
cancelling a common summand in the positive monoid. -/
theorem equalize (s t : Multiset T) (present : ∀ p, regular p → p ∈ s ∧ p ∈ t) :
    ∃ s' t' : Multiset T, weight w s = weight w s' ∧ weight w t = weight w t' ∧
      ∀ p, regular p → s'.count p = t'.count p := by
  classical
  suffices descend : ∀ h (u v : Multiset T),
      (∀ p, regular p → p ∈ u ∧ p ∈ v) →
      (∀ p, regular p → h ≤ dim p → u.count p = v.count p) →
      ∃ u' v' : Multiset T, weight w u = weight w u' ∧ weight w v = weight w v' ∧
        ∀ p, regular p → u'.count p = v'.count p by
    exact descend ((Finset.univ.sup dim)+1) s t present (fun p _ h =>
      False.elim ((Nat.not_succ_le_self _) (h.trans (Finset.le_sup (Finset.mem_univ p)))))
  intro h
  induction h with
  | zero => exact fun u v _ agree => ⟨u,v,rfl,rfl,fun p hp => agree p hp (Nat.zero_le _)⟩
  | succ h ih =>
    intro u v present agree
    let active := Finset.univ.filter (fun p => regular p ∧ dim p = h)
    have mem (p : T) : p ∈ active ↔ regular p ∧ dim p = h := by simp [active]
    let u' := u + additions face u v active
    let v' := v + additions face v u active
    obtain ⟨U,V,eU,eV,same⟩ := ih u' v' (fun p reg =>
      ⟨Multiset.mem_add.mpr (.inl (present p reg).1),Multiset.mem_add.mpr (.inl (present p reg).2)⟩) (by
        intro p reg high
        have off : ∀ q ∈ active, face q ≠ p := by
          intro q hq eq
          obtain ⟨rq,dq⟩ := (mem q).mp hq
          have lt := lower q rq
          rw [eq,dq] at lt; omega
        simp only [u',v',Multiset.count_add,count_additions face _ _ active p off]
        by_cases d : dim p = h
        · simp only [ite_eq_left ((mem p).mpr ⟨reg,d⟩)]; omega
        · have out : p ∉ active := fun hyp => d ((mem p).mp hyp).2
          simpa [out] using agree p reg (by omega))
    exact ⟨U,V,(keep_weight regular face w cut u v active (fun p h =>
      ⟨((mem p).mp h).1,(present p ((mem p).mp h).1).1⟩)).symm.trans eU,
      (keep_weight regular face w cut v u active (fun p h =>
      ⟨((mem p).mp h).1,(present p ((mem p).mp h).1).2⟩)).symm.trans eV,same⟩

end BoxMultiplicity
end GeneralizedEuler.Section4
