module

public import Section5.HeadPreparation

/-! The result of preparing the first coordinate over a varying tail.
The graph can be expressed using the retained head label and the
unmodified tail variables. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation

variable {K : Type*} [Field K] {O : ValuationSubring K} {I X Q V : Type*}
  (center : X → Option I → K) (cs : List I)

@[expose] def verticalPreparation (p : X × K) :
    X × (K × PreparationLabels O (RV0 O) cs.length) :=
  (p.1, (centerPreparation (O := O) (center p.1) cs).map p.2)

theorem verticalPreparation_injective :
    Function.Injective (verticalPreparation (O := O) center cs) := by
  rintro ⟨b, x⟩ ⟨b', x'⟩ he
  have hb : b = b' := congrArg Prod.fst he
  subst b'
  have hx := (centerPreparation (O := O) (center b) cs).map_injective (congrArg Prod.snd he)
  exact Prod.ext rfl hx

/-- After the lower-dimensional preparation of the pairwise center
differences, the vertical image has whole RV fibers across all coordinates. -/
theorem verticalPreparation_range (tailLabel : X → Q)
    (hzero : ∀ x, center x none = 0)
    (stable : ∀ x y, tailLabel x = tailLabel y →
      ∀ i j, rv O (center x i - center x j) = rv O (center y i - center y j)) :
    Set.range (verticalPreparation (O := O) center cs) =
      {p | rv O p.2.1 = (centerPreparation (O := O) (center p.1) cs).lead p.2.2 ∧
        ∃ a : X, tailLabel a = tailLabel p.1 ∧
          p.2.2 ∈ Set.range (centerPreparation (O := O) (center a) cs).label} := by
  ext p
  rcases p with ⟨b, y, t⟩
  let P := centerPreparation (O := O) (center b) cs
  constructor
  · rintro ⟨⟨a, x⟩, he⟩
    have hab : a = b := congrArg Prod.fst he
    subst a
    have h : P.map x = (y, t) := congrArg Prod.snd he
    have hy := show (y, t) ∈ Set.range P.map from ⟨x, h⟩
    rw [P.image_univ] at hy
    exact ⟨hy.2, b, rfl, hy.1⟩
  · rintro ⟨h, a, hq, ht⟩
    have he := label_ranges_of_center_differences (O := O) (center a) (center b)
      (hzero a) (hzero b) (stable a b hq) cs
    have hy : (y, t) ∈ Set.range P.map := by
      rw [P.image_univ]
      exact ⟨he ▸ ht, h⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨(b, x), Prod.ext rfl hx⟩

/-- Uniform vertical centers prepare all membership and output tests at
once. The remaining test is a relation on the tail and the retained head
label. The same statement handles partial graphs and empty output fibers. -/
theorem verticalPreparation_graph (G : Set (X × K × V))
    (hG : ∀ b x y v, (∀ i ∈ cs, rv O (x - center b (some i)) = rv O (y - center b (some i))) →
      ((b, x, v) ∈ G ↔ (b, y, v) ∈ G)) :
    (fun p : X × K × V => (verticalPreparation (O := O) center cs (p.1, p.2.1), p.2.2)) '' G =
      {p | rv O p.1.2.1 = (centerPreparation (O := O) (center p.1.1) cs).lead p.1.2.2 ∧
        ∃ x, (p.1.1, x, p.2) ∈ G ∧
          (centerPreparation (O := O) (center p.1.1) cs).label x = p.1.2.2} := by
  ext p
  rcases p with ⟨⟨b, y, t⟩, v⟩
  let P := centerPreparation (O := O) (center b) cs
  let A : Set (K × V) := {p | (b, p.1, p.2) ∈ G}
  have hA : ∀ x y v, P.label x = P.label y → ((x, v) ∈ A ↔ (y, v) ∈ A) := by
    intro x y v he
    exact hG b x y v
      (((regularize (O := O)).prepare_decides (center b ∘ some) cs he).2)
  have he := P.image_restriction A hA
  constructor
  · rintro ⟨⟨a, x, v'⟩, hx, h⟩
    have ha : a = b := congrArg (fun p => p.1.1) h
    have hv : v' = v := congrArg Prod.snd h
    subst a
    subst v'
    have hy : ((y,t), v) ∈ (fun p : K × V => (P.map p.1, p.2)) '' A :=
      ⟨(x,v), hx, Prod.ext (congrArg (fun p => p.1.2) h) rfl⟩
    rw [he] at hy
    exact hy
  · intro h
    have hy : ((y,t), v) ∈ (fun p : K × V => (P.map p.1, p.2)) '' A := he.symm ▸ h
    obtain ⟨⟨x,v'⟩, hmem, hp⟩ := hy
    obtain ⟨hxy, hv⟩ := Prod.mk.inj hp
    exact ⟨(b,x,v'), hmem, Prod.ext (Prod.ext rfl hxy) hv⟩

end GeneralizedEuler.Section5
