module

public import Section2.RVMonomials
public import Section2.RVDefinableEquivalence

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

section AllParameters

variable {L : Language.{u, v}} {E : Type w} {K : Type z} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

private noncomputable def embedResidueTuple {n : ℕ} (p : Residue O × (Fin n → Residue O)) :
    Fin n ⊕ Unit → RV0 O := Sum.elim (residueRV O ∘ p.2) (fun _ => residueRV O p.1)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem embedResidueTuple_injective {n : ℕ} :
    Function.Injective (embedResidueTuple O (n := n)) := by
  intro x y h
  exact Prod.ext (residueRV_injective O (congrFun h (.inr ())))
    (funext fun j => residueRV_injective O (congrFun h (.inl j)))

/-- With the parameters of Convention 2.1, finite value image suffices
for a definable bijection onto a definable set of embedded residue tuples. -/
theorem exists_definable_equiv_to_residue_tuples {n : ℕ} (D : Set (Fin n → RV0 O))
    [Finite (Set.range (fun x : D => unsignedValue O ∘ x.val))]
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {a : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | a .rv ∈ D}) :
    ∃ B : Set ((Fin n ⊕ Unit) → RV0 O), ∃ e : D ≃ B,
      SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
        (rvGraph (fun x => (e x).val)) ∧
      SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
        {a : ∀ s, RVVariables (Fin n ⊕ Unit) s → CanonicalSort O s | a .rv ∈ B} ∧
      ∀ y : B, ∀ j, y.val j ∈ Set.range (residueRV O) := by
  classical
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let Labels := Set.range (fun x : D => unsignedValue O ∘ x.val)
  let := Fintype.ofFinite Labels
  let l := Fintype.card Labels
  let idx : Labels ≃ Fin l := Fintype.equivFin Labels
  let rep (i : Fin l) : D := (idx.symm i).property.choose
  let reference (i : Fin l) (j : Fin n) : (Set.univ : Set (RV0 O)) := ⟨(rep i).val j, Set.mem_univ _⟩
  have href (i : Fin l) : (fun j => unsignedValue O (reference i j).val) = (idx.symm i).val :=
    (idx.symm i).property.choose_spec
  have hlabel : Function.Injective (fun i j => unsignedValue O (reference i j).val) := by
    intro i j h
    exact idx.symm.injective (Subtype.ext ((href i).symm.trans (h.trans (href j))))
  have hcover (x : Fin n → RV0 O) (hx : x ∈ D) :
      ∃ i, ∀ j, unsignedValue O (x j) = unsignedValue O (reference i j).val := by
    let q : Labels := ⟨unsignedValue O ∘ x, ⟨⟨x, hx⟩, rfl⟩⟩
    refine ⟨idx q, fun j => ?_⟩
    have h := congrFun (href (idx q)) j
    rw [idx.symm_apply_apply] at h
    exact h.symm
  let tag : Fin l ↪ Residue O := ⟨fun i => (i.val : Residue O), fun _ _ h => Fin.ext (Nat.cast_injective h)⟩
  obtain ⟨f, hf⟩ := exists_definable_residue_normalization (L := L) O hO power (fun _ => Set.univ)
    D hD reference tag (fun _ => Set.mem_univ _) hcover hlabel
  let enc (x : D) := embedResidueTuple O (f x)
  have henc : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      (rvGraph enc) := by
    convert hf using 1
    ext a
    change (∃ x : D, x.val = a .rv ∘ Sum.inl ∧ enc x = a .rv ∘ Sum.inr) ↔ _
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨x, hx, (congrFun h (.inr ())).symm, fun j => (congrFun h (.inl j)).symm⟩
    · rintro ⟨x, hx, htag, hnorm⟩
      refine ⟨x, hx, ?_⟩
      funext j
      rcases j with i | ⟨⟩
      · exact (hnorm i).symm
      · exact htag.symm
  let e := Equiv.ofInjective enc ((embedResidueTuple_injective O).comp f.injective)
  have hrange := definable_range_of_rvGraph (X := CanonicalSort O) (I := Fin n)
    (J := Fin n ⊕ Unit) enc henc
  refine ⟨Set.range enc, e, henc, hrange, ?_⟩
  intro y i
  obtain ⟨x, hx⟩ := y.property
  rw [← hx]
  cases i
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end AllParameters

end GeneralizedEuler.Section2
