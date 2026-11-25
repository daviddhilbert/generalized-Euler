module

public import Section2.RVMonomials
public import Section2.RVReduct

/-! Definable normalization of finitely many value fibers for Theorem 2.31. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

abbrev ResidueChartVariables (n : ℕ) := RVVariables (Fin n ⊕ (Fin n ⊕ Unit))

/-- Normalizing by a representative in each coordinate value and tagging
the finitely many fibers gives a definable injection into residue tuples.
The graph uses only the specified representatives and tags from the base. -/
theorem exists_definable_residue_normalization
    {L : Language.{u, v}} {E : Type w} {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
    (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
    (A : ∀ s, Set (CanonicalSort O s)) {n l : ℕ} (D : Set (Fin n → RV0 O))
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO power) A
      {a : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | a .rv ∈ D})
    (reference : Fin l → Fin n → A .rv) (tag : Fin l ↪ Residue O)
    (htag : ∀ i, residueRV O (tag i) ∈ A .rv)
    (hcover : ∀ x ∈ D, ∃ i, ∀ j, unsignedValue O (x j) = unsignedValue O (reference i j).val)
    (hlabel : Function.Injective (fun i j => unsignedValue O (reference i j).val)) :
    ∃ f : D ↪ Residue O × (Fin n → Residue O),
      SortedDefinableOver (canonicalStructure (L := L) O hO power) A
        {a : ∀ s, ResidueChartVariables n s → CanonicalSort O s | ∃ x : D,
          x.val = (fun j => a .rv (.inl j)) ∧
          a .rv (.inr (.inr ())) = residueRV O (f x).1 ∧
          ∀ j, a .rv (.inr (.inl j)) = residueRV O ((f x).2 j)} := by
  classical
  let M := canonicalStructure (L := L) O hO power
  let label (x : D) := (hcover x.val x.property).choose
  have value_eq (x : D) (j : Fin n) :
      unsignedValue O (x.val j) = unsignedValue O (reference (label x) j).val :=
    (hcover x.val x.property).choose_spec j
  have label_eq (x : D) (i : Fin l)
      (hi : ∀ j, unsignedValue O (x.val j) = unsignedValue O (reference i j).val) : label x = i :=
    hlabel (funext fun j => (value_eq x j).symm.trans (hi j))
  let r (x : D) (j : Fin n) := rvResidue O (x.val j / (reference (label x) j).val)
  let f : D ↪ Residue O × (Fin n → Residue O) := ⟨fun x => (tag (label x), r x), by
    intro x y h
    have hxy : label x = label y := tag.injective (congrArg Prod.fst h)
    have hr : r x = r y := congrArg Prod.snd h
    apply Subtype.ext
    funext j
    have hy := value_eq y j
    rw [← hxy] at hy
    have he := congrFun hr j
    change rvResidue O (x.val j / (reference (label x) j).val) =
      rvResidue O (y.val j / (reference (label y) j).val) at he
    rw [← hxy] at he
    exact rv_eq_of_equal_normalized_residues O (value_eq x j) hy he⟩
  have normalize (x : D) (j : Fin n) :
      residueRV O ((f x).2 j) = x.val j / (reference (label x) j).val :=
    residueRV_rvResidue_of_mem_range O (div_mem_residueRV_of_equal_unsignedValue O (value_eq x j))
  refine ⟨f, ?_⟩
  let Domain := ∀ s, ResidueChartVariables n s → CanonicalSort O s
  let input (a : Domain) (j : Fin n) := a .rv (.inl j)
  let In : Set Domain := {a | input a ∈ D}
  let Value (i : Fin l) : Set Domain := {a | ∀ j,
    unsignedValue O (input a j) = unsignedValue O (reference i j).val}
  let Tag (i : Fin l) : Set Domain := {a | a .rv (.inr (.inr ())) = residueRV O (tag i)}
  let Divide (i : Fin l) (j : Fin n) : Set Domain :=
    {a | a .rv (.inr (.inl j)) = input a j / (reference i j).val}
  let Body (i : Fin l) := (Value i ∩ Tag i) ∩ ⋂ j, Divide i j
  have hIn : SortedDefinableOver M A In :=
    hD.pullback_relabel (W := ResidueChartVariables n) (fun s => match s with
      | .vf => id
      | .rv => Sum.inl)
  have hBody (i : Fin l) : SortedDefinableOver M A (Body i) := by
    have hV : SortedDefinableOver M A (Value i) :=
      definable_unsigned_value_fiber (L := L) (Var := ResidueChartVariables n)
        O hO power Sum.inl (reference i)
    have hT : SortedDefinableOver M A (Tag i) := by
      let c : A .rv := ⟨residueRV O (tag i), htag i⟩
      exact SortedDefinableOver.coordinate_eq_parameter (M := M) (A := A)
        (Var := ResidueChartVariables n) .rv (.inr (.inr ())) c
    have hQ (j : Fin n) : SortedDefinableOver M A (Divide i j) :=
      definable_rv_division_coordinate (L := L) (Var := ResidueChartVariables n) O hO power
        (reference i j) (.inl j) (.inr (.inl j))
    exact (hV.inter hT).inter (SortedDefinableOver.iInter hQ)
  have hGraph := hIn.inter (SortedDefinableOver.iUnion hBody)
  convert hGraph using 1
  ext a
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, In, Body, Value, Tag, Divide, Set.mem_iInter]
  constructor
  · rintro ⟨x, hx, htag', hnorm⟩
    have hxi : x.val = input a := hx
    have ha : input a ∈ D := hxi ▸ x.property
    refine ⟨ha, label x, ⟨?_, htag'⟩, ?_⟩
    · intro j
      rw [← show x.val = input a from hx]
      exact value_eq x j
    · intro j
      change a .rv (.inr (.inl j)) = input a j / (reference (label x) j).val
      rw [hnorm j, normalize, hxi]
  · rintro ⟨ha, i, ⟨hvalue, htag'⟩, hdiv⟩
    let x : D := ⟨input a, ha⟩
    have hi := label_eq x i hvalue
    refine ⟨x, rfl, ?_, ?_⟩
    · change a .rv (.inr (.inr ())) = residueRV O (tag (label x))
      rwa [hi]
    · intro j
      rw [normalize, hi]
      exact hdiv j

end GeneralizedEuler.Section2
