module

public import Section2.ValuativeDisc
public import Mathlib.Data.Finset.Lattice.Fold

/-! Valuative intervals and their end discs in §2.4. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K]
  (O : ValuationSubring K)

/-- The end disc may be an open disc, a closed disc, or a singleton. -/
def IsEndDisc (D : Set K) : Prop :=
  (∃ c, D = {c}) ∨ ∃ c r, r ≠ 0 ∧ (D = openDisc O c r ∨ D = closedDisc O c r)

structure ValuativeIntervalEnd where
  disc : Set K
  included : Bool

def allowedBelow (e : Option (ValuativeIntervalEnd (K := K))) (x : K) : Prop :=
  match e with
  | none => True
  | some ⟨D, true⟩ => ∃ d ∈ D, x ≤ d
  | some ⟨D, false⟩ => ∀ d ∈ D, x < d

def allowedAbove (e : Option (ValuativeIntervalEnd (K := K))) (x : K) : Prop :=
  match e with
  | none => True
  | some ⟨D, true⟩ => ∃ d ∈ D, d ≤ x
  | some ⟨D, false⟩ => ∀ d ∈ D, d < x

/-- The set between two possibly unbounded end discs. Included endpoints
use the existential inequality in the manuscript. -/
def valuativeInterval (lo hi : Option (ValuativeIntervalEnd (K := K))) : Set K :=
  {x | allowedAbove lo x ∧ allowedBelow hi x}

def IsValuativeInterval (U : Set K) : Prop :=
  U.Nonempty ∧ ∃ lo hi : Option (ValuativeIntervalEnd (K := K)),
    (∀ e ∈ lo, IsEndDisc O e.disc) ∧ (∀ e ∈ hi, IsEndDisc O e.disc) ∧
    U = valuativeInterval lo hi

omit [Field K] in
private theorem allowedAbove_upward (e : Option (ValuativeIntervalEnd (K := K)))
    {x y : K} (hxy : x ≤ y) (h : allowedAbove e x) : allowedAbove e y := by
  rcases e with _ | ⟨D, b⟩
  · trivial
  cases b
  · exact fun z hz => (h z hz).trans_le hxy
  · obtain ⟨z, hz, hzx⟩ := h
    exact ⟨z, hz, hzx.trans hxy⟩

omit [Field K] in
private theorem allowedBelow_downward (e : Option (ValuativeIntervalEnd (K := K)))
    {x y : K} (hxy : x ≤ y) (h : allowedBelow e y) : allowedBelow e x := by
  rcases e with _ | ⟨D, b⟩
  · trivial
  cases b
  · exact fun z hz => hxy.trans_lt (h z hz)
  · obtain ⟨z, hz, hyz⟩ := h
    exact ⟨z, hz, hxy.trans hyz⟩

omit [Field K] in
theorem valuativeInterval_ordConnected (lo hi : Option (ValuativeIntervalEnd (K := K))) :
    Set.OrdConnected (valuativeInterval lo hi) := by
  refine ⟨?_⟩
  intro x hx y hy z ⟨hxz, hzy⟩
  exact ⟨allowedAbove_upward lo hxz hx.1, allowedBelow_downward hi hzy hy.2⟩

omit [Field K] in
theorem valuativeInterval_closed_singletons (a b : K) :
    valuativeInterval (some ⟨{a}, true⟩) (some ⟨{b}, true⟩) = Set.Icc a b := by
  ext x
  simp [valuativeInterval, allowedAbove, allowedBelow]

omit [Field K] in
theorem valuativeInterval_open_singletons (a b : K) :
    valuativeInterval (some ⟨{a}, false⟩) (some ⟨{b}, false⟩) = Set.Ioo a b := by
  ext x
  simp [valuativeInterval, allowedAbove, allowedBelow]

/-- The component sets in a Holly normal form. Different descriptions of
the same interval by ends give the same component. -/
def IsHollyDecomposition (U : Set K) (pieces : Finset (Set K)) : Prop :=
  (∀ D ∈ pieces, IsValuativeInterval O D) ∧ U = ⋃ D ∈ pieces, D ∧
    ∀ D ∈ pieces, ∀ B ∈ pieces, D ≠ B → ¬ IsValuativeInterval O (D ∪ B)

private theorem cuts_comparable {A : Type*} {rel : A → A → Prop} {P Q : A → Prop}
    (hTotal : ∀ x y, rel x y ∨ rel y x)
    (hP : ∀ {x y}, rel x y → P x → P y) (hQ : ∀ {x y}, rel x y → Q x → Q y) :
    (∀ x, P x → Q x) ∨ (∀ x, Q x → P x) := by
  classical
  by_cases h : ∀ x, P x → Q x
  · exact Or.inl h
  · push Not at h
    obtain ⟨x, hxP, hxQ⟩ := h
    refine Or.inr fun y hy => ?_
    exact hP ((hTotal x y).resolve_right (fun hle => hxQ (hQ hle hy))) hxP

private theorem intersect_cuts {A Tag : Type*} {ray : Tag → A → Prop} (a b : Tag)
    (hcmp : (∀ x, ray a x → ray b x) ∨ (∀ x, ray b x → ray a x)) :
    ∃ e, (e = a ∨ e = b) ∧ ∀ x, ray e x ↔ ray a x ∧ ray b x := by
  rcases hcmp with h | h
  · exact ⟨a, Or.inl rfl, fun x => ⟨fun hx => ⟨hx, h x hx⟩, And.left⟩⟩
  · exact ⟨b, Or.inr rfl, fun x => ⟨fun hx => ⟨h x hx, hx⟩, And.right⟩⟩

theorem IsValuativeInterval.inter {U V : Set K}
    (hU : IsValuativeInterval O U) (hV : IsValuativeInterval O V)
    (hne : (U ∩ V).Nonempty) : IsValuativeInterval O (U ∩ V) := by
  obtain ⟨_, a, b, ha, hb, rfl⟩ := hU
  obtain ⟨_, c, d, hc, hd, rfl⟩ := hV
  obtain ⟨lo, hlo, hl⟩ := intersect_cuts (ray := allowedAbove) a c
    (cuts_comparable le_total (allowedAbove_upward a) (allowedAbove_upward c))
  obtain ⟨hi, hhi, hh⟩ := intersect_cuts (ray := allowedBelow) b d
    (cuts_comparable (rel := fun x y : K => y ≤ x) (fun x y => le_total y x)
      (fun hxy => allowedBelow_downward b hxy) (fun hxy => allowedBelow_downward d hxy))
  refine ⟨hne, lo, hi, ?_, ?_, ?_⟩
  · rcases hlo with rfl | rfl
    · exact ha
    · exact hc
  · rcases hhi with rfl | rfl
    · exact hb
    · exact hd
  · ext x
    change (allowedAbove a x ∧ allowedBelow b x) ∧
      (allowedAbove c x ∧ allowedBelow d x) ↔ allowedAbove lo x ∧ allowedBelow hi x
    rw [hl, hh]
    tauto

/-- Finite unions of valuative intervals, allowing the empty union. -/
inductive ValuativeUnion : Set K → Prop where
  | empty : ValuativeUnion ∅
  | insert {D U : Set K} : IsValuativeInterval O D → ValuativeUnion U → ValuativeUnion (D ∪ U)

namespace ValuativeUnion

variable {O} {U V : Set K}

theorem of_interval (h : IsValuativeInterval O U) : ValuativeUnion O U := by
  simpa only [Set.union_empty] using insert h empty

theorem of_ends (lo hi : Option (ValuativeIntervalEnd (K := K)))
    (hlo : ∀ e ∈ lo, IsEndDisc O e.disc) (hhi : ∀ e ∈ hi, IsEndDisc O e.disc) :
    ValuativeUnion O (valuativeInterval lo hi) := by
  by_cases hne : (valuativeInterval lo hi).Nonempty
  · exact of_interval ⟨hne, lo, hi, hlo, hhi, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact empty

theorem union (hU : ValuativeUnion O U) (hV : ValuativeUnion O V) : ValuativeUnion O (U ∪ V) := by
  induction hU with
  | empty => simpa only [Set.empty_union] using hV
  | insert hD _ ih => rw [Set.union_assoc]; exact insert hD ih

theorem inter (hU : ValuativeUnion O U) (hV : ValuativeUnion O V) : ValuativeUnion O (U ∩ V) := by
  have singleInter {D : Set K} (hD : IsValuativeInterval O D) : ValuativeUnion O (D ∩ V) := by
    induction hV with
    | empty => simpa only [Set.inter_empty] using (empty (O := O))
    | @insert B V hB _ ih =>
      rw [Set.inter_union_distrib_left]
      by_cases hne : (D ∩ B).Nonempty
      · exact (of_interval (IsValuativeInterval.inter O hD hB hne)).union ih
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_union]
        exact ih
  induction hU with
  | empty => simpa only [Set.empty_inter] using (empty (O := O))
  | insert hD _ ih => rw [Set.union_inter_distrib_right]; exact (singleInter hD).union ih

private theorem not_allowedAbove (lo : Option (ValuativeIntervalEnd (K := K)))
    (hlo : ∀ e ∈ lo, IsEndDisc O e.disc) :
    ValuativeUnion O {x | ¬ allowedAbove lo x} := by
  classical
  rcases lo with _ | ⟨D, included⟩
  · have h : {x : K | ¬ allowedAbove none x} = ∅ := by
      ext x
      simp [allowedAbove]
    rw [h]
    exact empty
  · have heq : {x : K | ¬ allowedAbove (some ⟨D, included⟩) x} =
        valuativeInterval none (some ⟨D, !included⟩) := by
      ext x
      cases included <;> simp [valuativeInterval, allowedAbove, allowedBelow, not_lt, not_le]
    rw [heq]
    apply of_ends
    · simp
    · intro e he
      obtain rfl : e = ⟨D, !included⟩ := (Option.some.inj (Option.mem_def.mp he)).symm
      exact hlo ⟨D, included⟩ rfl

private theorem not_allowedBelow (hi : Option (ValuativeIntervalEnd (K := K)))
    (hhi : ∀ e ∈ hi, IsEndDisc O e.disc) :
    ValuativeUnion O {x | ¬ allowedBelow hi x} := by
  classical
  rcases hi with _ | ⟨D, included⟩
  · have h : {x : K | ¬ allowedBelow none x} = ∅ := by
      ext x
      simp [allowedBelow]
    rw [h]
    exact empty
  · have heq : {x : K | ¬ allowedBelow (some ⟨D, included⟩) x} =
        valuativeInterval (some ⟨D, !included⟩) none := by
      ext x
      cases included <;> simp [valuativeInterval, allowedAbove, allowedBelow, not_lt, not_le]
    rw [heq]
    apply of_ends
    · intro e he
      obtain rfl : e = ⟨D, !included⟩ := (Option.some.inj (Option.mem_def.mp he)).symm
      exact hhi ⟨D, included⟩ rfl
    · simp

theorem univ : ValuativeUnion O Set.univ := by
  have h : (valuativeInterval none none : Set K) = Set.univ := by
    ext x
    simp [valuativeInterval, allowedAbove, allowedBelow]
  rw [← h]
  exact of_ends none none (by simp) (by simp)

/-- The finite-union description is closed under Boolean operations,
including complements of intervals with infinite ends. -/
theorem compl (hU : ValuativeUnion O U) : ValuativeUnion O Uᶜ := by
  induction hU with
  | empty => simpa only [Set.compl_empty] using (univ (O := O))
  | @insert D V hD _ ih =>
    obtain ⟨_, lo, hi, hlo, hhi, rfl⟩ := hD
    rw [Set.compl_union]
    have h : (valuativeInterval lo hi)ᶜ =
        {x | ¬ allowedAbove lo x} ∪ {x | ¬ allowedBelow hi x} := by
      ext x
      exact not_and_or
    rw [h]
    exact ((not_allowedAbove lo hlo).union (not_allowedBelow hi hhi)).inter ih

theorem exists_finset (hU : ValuativeUnion O U) :
    ∃ pieces : Finset (Set K), (∀ D ∈ pieces, IsValuativeInterval O D) ∧
      U = ⋃ D ∈ pieces, D := by
  classical
  induction hU with
  | empty =>
    exact ⟨∅, by simp, by simp⟩
  | @insert D V hD _ ih =>
    obtain ⟨pieces, hinterval, hcover⟩ := ih
    refine ⟨Insert.insert D pieces, ?_, ?_⟩
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hD
      · exact hinterval B hB
    · rw [hcover]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
      constructor
      · rintro (hx | ⟨B, hB, hx⟩)
        · exact ⟨D, Or.inl rfl, hx⟩
        · exact ⟨B, Or.inr hB, hx⟩
      · rintro ⟨B, rfl | hB, hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨B, hB, hx⟩

/-- A finite cover by valuative intervals has a Holly decomposition.
In a cover with the fewest pieces, no pair can merge into one interval. -/
theorem exists_hollyDecomposition (hU : ValuativeUnion O U) :
    ∃ pieces, IsHollyDecomposition O U pieces := by
  classical
  let cover (pieces : Finset (Set K)) :=
    (∀ D ∈ pieces, IsValuativeInterval O D) ∧ U = ⋃ D ∈ pieces, D
  have h : ∃ n, ∃ pieces : Finset (Set K), pieces.card = n ∧ cover pieces := by
    obtain ⟨pieces, hp, hU⟩ := hU.exists_finset
    exact ⟨pieces.card, pieces, rfl, hp, hU⟩
  obtain ⟨pieces, hcard, hpieces, hcover⟩ := Nat.find_spec h
  refine ⟨pieces, hpieces, hcover, ?_⟩
  intro D hD B hB hne hmerge
  let rest := (pieces.erase D).erase B
  let pieces' := Insert.insert (D ∪ B) rest
  have hrest : rest ⊆ pieces := Finset.erase_subset _ _ |>.trans (Finset.erase_subset _ _)
  have hcover' : cover pieces' := by
    constructor
    · intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hmerge
      · exact hpieces _ (hrest hC)
    · rw [hcover]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨C, hC, hx⟩
        by_cases hCD : C = D
        · exact ⟨D ∪ B, Finset.mem_insert_self .., Or.inl (hCD ▸ hx)⟩
        by_cases hCB : C = B
        · exact ⟨D ∪ B, Finset.mem_insert_self .., Or.inr (hCB ▸ hx)⟩
        exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨hCB, Finset.mem_erase.mpr ⟨hCD, hC⟩⟩), hx⟩
      · rintro ⟨C, hC, hx⟩
        rcases Finset.mem_insert.mp hC with rfl | hC
        · rcases hx with hx | hx
          · exact ⟨D, hD, hx⟩
          · exact ⟨B, hB, hx⟩
        · exact ⟨C, hrest hC, hx⟩
  have h₁ := Finset.card_erase_add_one hD
  have h₂ : rest.card + 1 = (pieces.erase D).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne.symm, hB⟩)
  have h₃ : pieces'.card ≤ rest.card + 1 := Finset.card_insert_le _ _
  have hmin : Nat.find h ≤ pieces'.card := Nat.find_min' h ⟨pieces', rfl, hcover'⟩
  omega

end ValuativeUnion

end GeneralizedEuler.Section2
