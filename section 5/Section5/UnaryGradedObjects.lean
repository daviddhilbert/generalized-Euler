module

public import Section5.DefinableUnaryLabels

/-! The two degrees of a unary RV presentation, as actual Section 4
objects. The active coordinate is omitted on the zero stratum. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable {n : ℕ} (D : Set (Fin n → RV0 O)) (i : Fin n)
  (hD : isRVSet (canonicalStructure (L := L) O hO power) S D) (hfin : ∀ s, {t ∈ D | t i = s}.Finite)

theorem coordinate_zero_definable :
    isRVSet 𝓜 S {t : Fin n → RV0 O | t i = 0} := by
  have h := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier)
    (Var := RVVariables (Fin n)) .rv i rvZeroTerm
  unfold isRVSet
  convert h using 1
  ext t
  simp only [Set.mem_ofPred_eq, realize_rvZeroTerm O hO power]

/-- On the zero stratum the structure map has zero coordinates. -/
@[expose] def unaryDegreeZero : RVObject 𝓜 S 0 where
  arity := n
  carrier := {t ∈ D | t i = 0}
  definable := hD.inter (coordinate_zero_definable O hO power S i)
  label _ := Fin.elim0
  graph := by
    have hd : isRVSet 𝓜 S {w : Fin n ⊕ Fin 0 → RV0 O |
        w ∘ Sum.inl ∈ {t ∈ D | t i = 0}} :=
      isRVSet_precomp Sum.inl (hD.inter (coordinate_zero_definable O hO power S i))
    unfold isRVSet at hd
    convert hd using 1
    ext w
    change (∃ t : {t ∈ D | t i = 0}, t.val = w .rv ∘ Sum.inl ∧
      Fin.elim0 = w .rv ∘ Sum.inr) ↔ w .rv ∘ Sum.inl ∈ {t ∈ D | t i = 0}
    exact ⟨fun ⟨t, ht, _⟩ => ht ▸ t.property,
      fun hp => ⟨⟨_, hp⟩, rfl, Subsingleton.elim _ _⟩⟩
  nonzero := fun _ j => j.elim0
  finiteFibers y := by
    apply ((hfin 0).preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    exact fun t _ => t.property

/-- On the nonzero stratum the structure map retains the leading-term
coordinate. The other coordinates stay in the RV tag. -/
@[expose] def unaryDegreeOne : RVObject 𝓜 S 1 where
  arity := n
  carrier := {t ∈ D | t i ≠ 0}
  definable := hD.inter (coordinate_zero_definable O hO power S i).compl
  label t := fun _ => t.val i
  graph := by
    have hd : isRVSet 𝓜 S {w : Fin n ⊕ Fin 1 → RV0 O |
        w ∘ Sum.inl ∈ {t ∈ D | t i ≠ 0}} :=
      isRVSet_precomp Sum.inl (hD.inter (coordinate_zero_definable O hO power S i).compl)
    have he := SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier)
      (Var := RVVariables (Fin n ⊕ Fin 1)) .rv (.inl i) (.inr 0)
    convert hd.inter he using 1
    ext w
    change (∃ t : {t ∈ D | t i ≠ 0}, t.val = w .rv ∘ Sum.inl ∧
      (fun _ => t.val i) = w .rv ∘ Sum.inr) ↔
      w .rv ∘ Sum.inl ∈ {t ∈ D | t i ≠ 0} ∧ w .rv (.inl i) = w .rv (.inr 0)
    constructor
    · rintro ⟨t, ht, hout⟩
      exact ⟨ht ▸ t.property, (congrFun ht i).symm.trans (congrFun hout 0)⟩
    · rintro ⟨hp, hp'⟩
      refine ⟨⟨_, hp⟩, rfl, funext fun j => ?_⟩
      rw [Fin.fin_one_eq_zero j]
      exact hp'
  nonzero t _ := t.property.2
  finiteFibers y := by
    apply ((hfin (y 0)).preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro t ht
    exact ⟨t.property.1, congrFun (show (fun _ : Fin 1 => t.val i) = y from ht) 0⟩

end GeneralizedEuler.Section5
