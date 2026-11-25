module

public import Section3.DefinableFunctions
public import Section3.DefinablePartitions
public import Section2.ContinuousDefinitions
import all Section2.ContinuousDefinitions

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

variable {K I : Type*} [Field K] [LinearOrder K] {L : Language} [L.Structure K]
  {P : Set K} (F : OrderedFieldTerms L) (hF : InterpretsOrderedFieldTerms (A := K) F)

include hF

private theorem definable_first_or_zero (S : (I → K) → Finset K)
    (hd : P.Definable L {v : Option I → K | v none ∈ S (v ∘ some)})
    (first : (I → K) → K) (spec : ∀ a, if h : (S a).Nonempty then first a = (S a).min' h else first a = 0) :
    P.DefinableFun L first := by
  let small : Set ((Option I ⊕ Unit) → K) := {u | u (.inr ()) ∈ S ((u ∘ Sum.inl) ∘ some)}
  let rename : Option I → Option I ⊕ Unit := fun | none => .inr () | some i => .inl (some i)
  have ds : P.Definable L small := hd.preimage_comp rename
  have leq : P.Definable L {u : Option I ⊕ Unit → K | u (.inl none) ≤ u (.inr ())} :=
    definable_le_of_definableFunctions F hF (DefinableFun.proj L) (DefinableFun.proj L)
  have lb : P.Definable L {v : Option I → K | ∀ z ∈ S (v ∘ some), v none ≤ z} := by
    apply definable_forall_scalar
    convert ds.compl.union leq using 1
    ext u
    exact imp_iff_not_or
  have empty : P.Definable L {v : Option I → K | ∀ z, z ∉ S (v ∘ some)} :=
    definable_forall_scalar ds.compl
  have zero : P.Definable L {v : Option I → K | v none = 0} := by
    have h := definable_const_of_closed_term (A := P) (I := I) F.zero 0 hF.zero
    change P.Definable L _ at h
    convert h using 1
    ext v
    exact eq_comm
  change P.Definable L (Function.tupleGraph first)
  convert (hd.inter lb).union (empty.inter zero) using 1
  ext v
  let a := v ∘ some
  change first a = v none ↔ (v none ∈ S a ∧ ∀ z ∈ S a, v none ≤ z) ∨
    ( (∀ z, z ∉ S a) ∧ v none = 0)
  by_cases h : (S a).Nonempty
  · have hmin : first a = (S a).min' h := by simpa [h] using spec a
    have hm := (S a).min'_mem h
    exact ⟨fun hv => Or.inl ⟨hv ▸ hmin.symm ▸ hm,fun z hz => hv ▸ hmin.symm ▸ (S a).min'_le z hz⟩,
      fun hh => hh.elim (fun ⟨hx,hl⟩ => hmin.trans ((Finset.min'_le _ _ hx).antisymm (hl _ hm)))
        (fun ⟨no,_⟩ => (no _ hm).elim)⟩
  · have hzero : first a = 0 := by simpa [h] using spec a
    have no (z) : z ∉ S a := fun hz => h ⟨z,hz⟩
    exact ⟨fun hv => Or.inr ⟨no,hv.symm.trans hzero⟩,
      fun hh => hh.elim (fun ⟨hz,_⟩ => (no _ hz).elim) (fun h => hzero.trans h.2.symm)⟩

/-- Uniformly finite fibers in a definable family can be enumerated by
a fixed finite list of total functions over the same parameters. The
least remaining point is taken at each step, with zero on empty fibers. -/
theorem ordered_branches_of_finite_family (N : ℕ) (S : (I → K) → Finset K)
    (hd : P.Definable L {v : Option I → K | v none ∈ S (v ∘ some)})
    (bound : ∀ a, (S a).card ≤ N) :
    ∃ g : Fin N → (I → K) → K, (∀ i, P.DefinableFun L (g i)) ∧
      ∀ a y, y ∈ S a → ∃ i, g i a = y := by
  classical
  induction N generalizing S with
  | zero =>
    refine ⟨Fin.elim0,fun i => i.elim0,?_⟩
    intro a y hy
    exact ((Finset.card_pos.mpr ⟨y,hy⟩).not_ge (bound a)).elim
  | succ N ih =>
    let first (a : I → K) := if h : (S a).Nonempty then (S a).min' h else 0
    have df := definable_first_or_zero F hF S hd first (fun a => by
      by_cases h : (S a).Nonempty <;> simp [first,h])
    let rest (a : I → K) := (S a).erase (first a)
    have dr : P.Definable L {v : Option I → K | v none ∈ rest (v ∘ some)} := by
      convert hd.inter df.compl using 1
      ext v
      change _ ∈ (S _).erase _ ↔ _ ∈ S _ ∧ ¬ first (v ∘ some) = v none
      rw [Finset.mem_erase]
      exact and_comm.trans (and_congr_right (fun _ => ne_comm))
    have rb (a) : (rest a).card ≤ N := by
      by_cases h : (S a).Nonempty
      · have hm : first a ∈ S a := by simpa only [first,dite_eq_left h] using (S a).min'_mem h
        change ((S a).erase _).card ≤ _
        rw [Finset.card_erase_of_mem hm]
        have := bound a
        omega
      · simp [rest,Finset.not_nonempty_iff_eq_empty.mp h]
    obtain ⟨g,dg,cg⟩ := ih rest dr rb
    refine ⟨Fin.cons first g,Fin.cases df dg,fun a y hy => ?_⟩
    by_cases he : y = first a
    · exact ⟨0,by simpa using he.symm⟩
    · obtain ⟨j,hj⟩ := cg a y (Finset.mem_erase.mpr ⟨he,hy⟩)
      exact ⟨j.succ,by simpa using hj⟩

end GeneralizedEuler.Section3
