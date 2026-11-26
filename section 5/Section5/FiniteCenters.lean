module

public import Section5.UnaryPreparation

/-! Preparation of a finite set of translated leading-term tests on the
full line, followed by restriction to a family with fixed RV labels. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

universe u h

variable {K : Type u} [Field K] {O : ValuationSubring K}

/-- The labels of a finite succession of regularizations. -/
@[expose] def PreparationLabels (O : ValuationSubring K) (H : Type h) : ℕ → Type (max u h)
  | 0 => ULift H
  | n + 1 => PreparationLabels O H n × RV0 O

namespace UnaryPreparation

variable {H : Type h} (P : UnaryPreparation O H) {C : Type*} (center : C → K)

/-- Prepare the centers in reverse list order. -/
@[expose] def prepare : (cs : List C) → UnaryPreparation O (PreparationLabels O H cs.length)
  | [] =>
    { label := fun x => ⟨P.label x⟩
      offset := fun h => P.offset h.down
      lead := fun h => P.lead h.down
      leading := P.leading
      constant_label := fun eq => congrArg ULift.up (P.constant_label eq) }
  | c :: cs => (prepare cs).step (center c)

/-- Preparing an additional center preserves all tests detected by the
previous labels, which are the first component of the new labels. -/
theorem prepare_decides (cs : List C) {x y : K} (he : (P.prepare center cs).label x = (P.prepare center cs).label y) :
    P.label x = P.label y ∧ ∀ c ∈ cs, rv O (x - center c) = rv O (y - center c) := by
  induction cs with
  | nil =>
    exact ⟨congrArg ULift.down he, by simp⟩
  | cons c cs ih =>
    have h := ih (congrArg Prod.fst he)
    refine ⟨h.1, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (P.prepare center cs).step_decides (center d) he
    · exact h.2 d hd

theorem prepare_offset_mem (B : Set K) (hP : ∀ t, P.offset t ∈ B)
    (cs : List C) (hcs : ∀ c ∈ cs, center c ∈ B) :
    ∀ t, (P.prepare center cs).offset t ∈ B := by
  classical
  induction cs with
  | nil => exact fun t => hP t.down
  | cons c cs ih =>
    intro t
    change (P.prepare center cs).nextOffset (center c) t.1 ∈ B
    unfold nextOffset
    split
    · exact hcs c List.mem_cons_self
    · exact ih (fun d hd => hcs d (List.mem_cons_of_mem c hd)) t.1

/-- The restriction of a prepared affine line to a family whose
membership is constant on labels is again a union of whole fibers. -/
theorem image_restriction {I : Type*} (A : Set (K × I))
    (hA : ∀ x y ξ, P.label x = P.label y → ((x, ξ) ∈ A ↔ (y, ξ) ∈ A)) :
    (fun p : K × I => (P.map p.1, p.2)) '' A =
      {p | rv O p.1.1 = P.lead p.1.2 ∧ ∃ x, (x, p.2) ∈ A ∧ P.label x = p.1.2} := by
  ext p
  constructor
  · rintro ⟨⟨x, ξ⟩, hx, rfl⟩
    exact ⟨P.leading x, x, hx, rfl⟩
  · rcases p with ⟨⟨y, t⟩, ξ⟩
    rintro ⟨hy, x, hx, rfl⟩
    let z := y + P.offset (P.label x)
    have hz : P.label z = P.label x := P.constant_label (by simpa [z] using hy)
    have hzA := (hA z x ξ hz).2 hx
    exact ⟨(z, ξ), hzA, by simp [map, hz, z]⟩

/-- Simultaneous unary preparation for any family already decided by the
same finite list of translates. The original RV tuple stays fixed. -/
theorem unary_pullback_of_finite_centers {I : Type*} (A : Set (K × I)) (cs : List C)
    (hA : ∀ x y ξ, (∀ c ∈ cs, rv O (x - center c) = rv O (y - center c)) →
      ((x, ξ) ∈ A ↔ (y, ξ) ∈ A)) :
    let P := (regularize (O := O)).prepare center cs
    (fun p : K × I => (P.map p.1, p.2)) '' A =
      {p | rv O p.1.1 = P.lead p.1.2 ∧ ∃ x, (x, p.2) ∈ A ∧ P.label x = p.1.2} := by
  intro P
  exact P.image_restriction A fun x y ξ e => hA x y ξ (((regularize (O := O)).prepare_decides center cs e).2)

end UnaryPreparation

/-- A disc with points both inside and outside a unary set contains one
of its preparing centers. This works fiberwise over the original RV tuple. -/
theorem cut_disc_contains_center {C I : Type*} (point : C → K) (cs : List C)
    (A : Set (K × I))
    (hA : ∀ x y ξ, (∀ c ∈ cs, rv O (x - point c) = rv O (y - point c)) →
      ((x, ξ) ∈ A ↔ (y, ξ) ∈ A))
    {a x y : K} {r : O.ValueGroup} {ξ : I}
    (hx : x ∈ openDisc O a r) (hy : y ∈ openDisc O a r)
    (hxin : (x, ξ) ∈ A) (hyout : (y, ξ) ∉ A) :
    ∃ c ∈ cs, point c ∈ openDisc O a r := by
  by_contra! h
  apply hyout
  exact (hA x y ξ fun c hc =>
    GeneralizedEuler.Section3.rv_translate_constant_off_disc O hx hy (h c hc)).1 hxin

end GeneralizedEuler.Section5
