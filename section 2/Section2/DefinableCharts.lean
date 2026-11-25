module

public import Section2.Dimension
public import Section2.SortedDefinability

/-! The definability of the padded, tagged chart injection in Lemma 2.26. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

/-- A tuple with `n` field coordinates and RV coordinates indexed by `R`. -/
abbrev MixedVariables (n : ℕ) (R : Type) : TCsort → Type
  | .vf => Fin n
  | .rv => R

abbrev MixedTuple (X : TCsort → Type z) (n : ℕ) (R : Type) :=
  (Fin n → X .vf) × (R → X .rv)

@[expose]
def mixedTuple {X : TCsort → Type z} {n : ℕ} {R : Type}
    (a : ∀ s, MixedVariables n R s → X s) : MixedTuple X n R :=
  ⟨a .vf, a .rv⟩

abbrev ChartGraphVariables (n : ℕ) (R : Type) (k : ℕ) (s : TCsort) :=
  MixedVariables n R s ⊕ MixedVariables k (R ⊕ Unit) s

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X} {A : ∀ s, Set (X s)} {R : Type} {n k : ℕ}

abbrev chartInput (a : ∀ s, ChartGraphVariables n R k s → X s) : MixedTuple X n R :=
  mixedTuple (fun s => a s ∘ Sum.inl)

abbrev chartOutput (a : ∀ s, ChartGraphVariables n R k s → X s) :
    (Fin k → X .vf) × ((R → X .rv) × X .rv) :=
  ⟨fun j => a .vf (.inr j), fun j => a .rv (.inr (.inl j)), a .rv (.inr (.inr ()))⟩

/-- Given a finite definable chart cover, the tagged coordinate injection
is definable over the same base. The original RV coordinates are retained.
The chart tag uses one additional RV coordinate. -/
theorem exists_definable_embedding_of_projection_cover [Finite R] {l : ℕ}
    (D : Set (MixedTuple X n R)) (pieces : Fin l → Set (MixedTuple X n R))
    (hD : SortedDefinableOver M A {a | mixedTuple a ∈ D})
    (hpieces : ∀ i, SortedDefinableOver M A {a | mixedTuple a ∈ pieces i})
    (hcover : ∀ x ∈ D, ∃ i, x ∈ pieces i) (m : Fin l → ℕ) (hm : ∀ i, m i ≤ k)
    (projection : ∀ i, Fin (m i) ↪ Fin n)
    (hinj : ∀ i, Set.InjOn (fun x : MixedTuple X n R =>
      (coordinateProjection (projection i) x.1, x.2)) (D ∩ pieces i))
    (padding : A .vf) (tag : Fin l ↪ X .rv) (htag : ∀ i, tag i ∈ A .rv) :
    ∃ f : D ↪ (Fin k → X .vf) × ((R → X .rv) × X .rv),
      SortedDefinableOver M A {a : ∀ s, ChartGraphVariables n R k s → X s |
        ∃ x : D, x.val = chartInput a ∧ f x = chartOutput a} := by
  classical
  let piece (i : Fin l) : Set D := Subtype.val ⁻¹' pieces i
  have hinj' (i : Fin l) : Set.InjOn (fun x : D =>
      (coordinateProjection (projection i) x.val.1, x.val.2)) (piece i) := by
    intro x hx y hy hxy
    exact Subtype.ext (hinj i ⟨x.property, hx⟩ ⟨y.property, hy⟩ hxy)
  obtain ⟨f, hf⟩ := exists_embedding_with_piecewise_projection_graph D piece
    (fun x => hcover x.val x.property) m hm projection hinj' padding.val tag
  refine ⟨f, ?_⟩
  let In : Set (∀ s, ChartGraphVariables n R k s → X s) := {a | chartInput a ∈ D}
  let P (i : Fin l) : Set (∀ s, ChartGraphVariables n R k s → X s) :=
    {a | chartInput a ∈ pieces i}
  let earlier (i : Fin l) := ⋂ j : {j : Fin l // j < i}, (P j.val)ᶜ
  let VF (i : Fin l) (j : Fin k) : Set (∀ s, ChartGraphVariables n R k s → X s) :=
    {a | (chartOutput a).1 j =
      if h : j.val < m i then (chartInput a).1 (projection i ⟨j.val, h⟩) else padding.val}
  let RV (j : R) : Set (∀ s, ChartGraphVariables n R k s → X s) :=
    {a | (chartOutput a).2.1 j = (chartInput a).2 j}
  let Label (i : Fin l) : Set (∀ s, ChartGraphVariables n R k s → X s) :=
    {a | (chartOutput a).2.2 = tag i}
  have hIn : SortedDefinableOver M A In := hD.pullback_relabel (fun _ => Sum.inl)
  have hP (i : Fin l) : SortedDefinableOver M A (P i) :=
    (hpieces i).pullback_relabel (fun _ => Sum.inl)
  have hEarlier (i : Fin l) : SortedDefinableOver M A (earlier i) :=
    SortedDefinableOver.iInter (fun j => (hP j.val).compl)
  have hVF (i : Fin l) (j : Fin k) : SortedDefinableOver M A (VF i j) := by
    by_cases h : j.val < m i
    · have he : VF i j = {a | a .vf (.inr j) = a .vf (.inl (projection i ⟨j.val, h⟩))} := by
        ext a
        simp only [VF, Set.mem_ofPred_eq, dite_eq_left h]
        rfl
      rw [he]
      exact SortedDefinableOver.coordinate_eq .vf _ _
    · have he : VF i j = {a | a .vf (.inr j) = padding.val} := by
        ext a
        simp only [VF, Set.mem_ofPred_eq, dite_eq_right h]
      rw [he]
      exact SortedDefinableOver.coordinate_eq_parameter .vf _ padding
  have hRV (j : R) : SortedDefinableOver M A (RV j) :=
    SortedDefinableOver.coordinate_eq (Var := ChartGraphVariables n R k) .rv
      (.inr (.inl j)) (.inl j)
  have hLabel (i : Fin l) : SortedDefinableOver M A (Label i) :=
    SortedDefinableOver.coordinate_eq_parameter (Var := ChartGraphVariables n R k) .rv
      (.inr (.inr ())) ⟨tag i, htag i⟩
  let Body (i : Fin l) := (P i ∩ earlier i) ∩ (⋂ j, VF i j) ∩ (⋂ j, RV j) ∩ Label i
  have hBody (i : Fin l) : SortedDefinableOver M A (Body i) :=
    (((hP i).inter (hEarlier i)).inter (SortedDefinableOver.iInter (hVF i))
      |>.inter (SortedDefinableOver.iInter hRV)).inter (hLabel i)
  have hGraph : SortedDefinableOver M A (In ∩ ⋃ i, Body i) :=
    hIn.inter (SortedDefinableOver.iUnion hBody)
  have body_iff (i : Fin l) (a : ∀ s, ChartGraphVariables n R k s → X s) :
      a ∈ Body i ↔ chartInput a ∈ pieces i ∧ (∀ j < i, chartInput a ∉ pieces j) ∧
        ((fun j : Fin k => if h : j.val < m i then (chartInput a).1 (projection i ⟨j.val, h⟩)
          else padding.val), (chartInput a).2, tag i) = chartOutput a := by
    simp only [Body, P, earlier, VF, RV, Label, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_ofPred_eq, Subtype.forall]
    constructor
    · rintro ⟨⟨⟨⟨hp, hbefore⟩, hvf⟩, hrv⟩, htag'⟩
      exact ⟨hp, hbefore, Prod.ext (funext fun j => (hvf j).symm)
        (Prod.ext (funext fun j => (hrv j).symm) htag'.symm)⟩
    · rintro ⟨hp, hbefore, he⟩
      exact ⟨⟨⟨⟨hp, hbefore⟩,
        fun j => (congrFun (congrArg Prod.fst he) j).symm⟩,
        fun j => (congrFun (congrArg (fun y => y.2.1) he) j).symm⟩,
        (congrArg (fun y => y.2.2) he).symm⟩
  convert hGraph using 1
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, In]
  constructor
  · rintro ⟨x, hx, hfx⟩
    obtain ⟨i, hi, hbefore, hcoords⟩ := (hf x _).mp hfx
    have hi' : x.val ∈ pieces i := hi
    have hb' : ∀ j < i, x.val ∉ pieces j := hbefore
    rw [hx] at hi' hb' hcoords
    exact ⟨hx ▸ x.property, i, (body_iff i a).mpr ⟨hi', hb', hcoords⟩⟩
  · rintro ⟨ha, i, hi⟩
    obtain ⟨hp, hbefore, hcoords⟩ := (body_iff i a).mp hi
    exact ⟨⟨chartInput a, ha⟩, rfl, (hf _ _).mpr ⟨i, hp, hbefore, hcoords⟩⟩

/-- Natural RV tags already belong to any base containing the field
numerals, so the chart injection needs no extra parameters. -/
theorem natRVEmbedding_mem_base {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (power : E → RV0 O → RV0 O)
    (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
    (hn : ∀ n : ℕ, (n : K) ∈ S.carrier .vf) (j : ℕ) :
    natRVEmbedding O hO j ∈ S.carrier .rv := by
  rw [natRVEmbedding_apply, ← canonicalStructure_rvMap O hO power (L := L)]
  exact S.rvMap_mem (hn j)

end GeneralizedEuler.Section2
