module

public import Section5.RelativeRVGluing

/-! Omitting coordinates on which the selected head tuple is zero
does not enlarge an index fiber inside the corresponding stratum. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h n k : ℕ}

/-- A head start counts its selected coordinates before zero entries
are dropped. This set represents one fixed zero pattern. -/
@[expose] def headStartStratum (sel : Fin n → Fin h) (keep : Fin k → Fin n)
    (zero : X .rv) (B : Set (Fin h → X .rv)) : Set (Fin h → X .rv) :=
  {x ∈ B | ∀ i, x (sel i) ≠ zero ↔ i ∈ Set.range keep}

theorem headStartStratum_definable (sel : Fin n → Fin h) (keep : Fin k → Fin n) (zero : S.carrier .rv)
    {B : Set (Fin h → X .rv)} (defB : isRVSet M S B) :
    isRVSet M S (headStartStratum sel keep zero.val B) := by
  classical
  let W := RVVariables (Fin h)
  let C (i : Fin n) : Set (SortedAssignment X W) := {a | a .rv (sel i) = zero.val}
  have dC (i : Fin n) : SortedDefinableOver M S.carrier (C i) :=
    SortedDefinableOver.coordinate_eq_parameter (M := M) (Var := W) .rv (sel i) zero
  let s (i : Fin n) := if i ∈ Set.range keep then (C i)ᶜ else C i
  have ds (i : Fin n) : SortedDefinableOver M S.carrier (s i) := by
    by_cases hi : i ∈ Set.range keep
    · simpa only [s,ite_eq_left hi] using (dC i).compl
    · simpa only [s,ite_eq_right hi] using dC i
  unfold isRVSet at defB ⊢
  convert defB.inter (SortedDefinableOver.iInter ds) using 1
  ext a
  simp only [Set.mem_inter_iff,Set.mem_iInter,headStartStratum,Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  by_cases hi : i ∈ Set.range keep
  · rw [show s i = (C i)ᶜ from ite_eq_left hi]
    change (a .rv (sel i) ≠ zero.val ↔ i ∈ Set.range keep) ↔ a .rv (sel i) ≠ zero.val
    exact ⟨fun h => h.2 hi,fun h => ⟨fun _ => hi,fun _ => h⟩⟩
  · rw [show s i = C i from ite_eq_right hi]
    change (a .rv (sel i) ≠ zero.val ↔ i ∈ Set.range keep) ↔ a .rv (sel i) = zero.val
    simp only [hi,iff_false,not_ne_iff]

theorem headStartStratum_nonzero (sel : Fin n → Fin h) (keep : Fin k → Fin n)
    {zero : X .rv} {B : Set (Fin h → X .rv)} {x : Fin h → X .rv}
    (hx : x ∈ headStartStratum sel keep zero B) (i : Fin k) :
    x (sel (keep i)) ≠ zero :=
  (hx.2 (keep i)).2 (Set.mem_range_self i)

theorem headStartStratum_finite_indices (sel : Fin n → Fin h) (keep : Fin k → Fin n)
    (zero : X .rv) (B : Set (Fin h → X .rv))
    (finite : ∀ y : Fin n → X .rv, {x ∈ B | x ∘ sel = y}.Finite) :
    ∀ y : Fin k → X .rv, {x ∈ headStartStratum sel keep zero B | x ∘ sel ∘ keep = y}.Finite := by
  intro y
  let T := {x ∈ headStartStratum sel keep zero B | x ∘ sel ∘ keep = y}
  by_cases ht : T.Nonempty
  · obtain ⟨x,hx⟩ := ht
    apply (finite (x ∘ sel)).subset
    rintro w ⟨hw,ew⟩
    refine ⟨hw.1,?_⟩
    funext i
    by_cases hi : i ∈ Set.range keep
    · obtain ⟨j,rfl⟩ := hi
      exact congrFun (ew.trans hx.2.symm) j
    · have hz : w (sel i) = zero := not_ne_iff.1 (fun hn => hi ((hw.2 i).1 hn))
      have hzx : x (sel i) = zero := not_ne_iff.1 (fun hn => hi ((hx.1.2 i).1 hn))
      exact hz.trans hzx.symm
  · change T.Finite
    rw [Set.not_nonempty_iff_eq_empty.1 ht]
    exact Set.finite_empty

end GeneralizedEuler.Section5
