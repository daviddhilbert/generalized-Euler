module

public import Section5.PaddedRVLabelGraph
public import Section5.IdentityContractionRuns
public import Section5.SingleSupportTerminalClass
public import Section5.FieldwiseContractionRelations

/-! An identity run on a padded lift recovers the original RV object
class in its original degree, with the padding omitted. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem padded_lift_identity_class
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    {d n : ℕ} (U : RVObject 𝓜 S d) (p : Fin d ↪ Fin n) :
    let A := paddedLiftFamily O hO power S U p
    ∃ (B : RetainedFieldFamily 𝓜 S 0 n) (a : ℕ) (idx : Fin a ≃ B.tags),
      HeadContractionRun A B ∧
      B.terminalGradedClass idx (baseRVZero S) rfl = objectClass 𝓜 S ⟨d,U⟩ := by
  classical
  intro A
  obtain ⟨l,B,e,order,run,member,selected⟩ :=
    identity_contraction_run O hO power S F minusOne hm hF zero hz A
      (paddedLiftFamily_pullback O hO power S U p)
  have count : l = n := run.selected_count.trans (Nat.zero_add n)
  subst l
  let : Finite B.tags := B.finiteTags
  let a := Nat.card B.tags
  let idx : Fin a ≃ B.tags := (Finite.equivFin _).symm
  let E' : (Fin n ⊕ Fin U.arity) ≃ B.tags := e
  let Z := paddedRVLabels O hO power S U p
  have carrier (t : B.tags → RV0 O) : (Fin.elim0,t) ∈ B.carrier ↔ t ∘ E' ∈ Z := by
    let x (i : Fin n) := (rv_surjective O (t (e (.inl i)))).choose
    have lead (i : Fin n) : rv O (x i) = t (e (.inl i)) := (rv_surjective O _).choose_spec
    rw [member t x lead]
    have lump : rv O ∘ x ∘ p = (t ∘ E') ∘ Sum.inl ∘ p := funext (fun j => lead (p j))
    have pad (i : Fin n) : x i = 0 ↔ (t ∘ E') (.inl i) = 0 := by
      rw [← (rv_eq_zero_iff O),lead]
      rfl
    constructor
    · rintro ⟨⟨u,ht,hl⟩,hz⟩
      exact ⟨u,ht,hl.trans lump,fun i hi => (pad i).1 (hz i hi)⟩
    · rintro ⟨u,ht,hl,hz⟩
      exact ⟨⟨u,ht,hl.trans lump.symm⟩,fun i hi => (pad i).2 (hz i hi)⟩
  have iso := paddedRVLabels_equivalent O hO power S U p
  have defZ : isRVSet 𝓜 S Z := isRVSet_of_rvEquiv iso
  let reindex := idx.trans E'.symm
  have re := rv_reindex_equivalent 𝓜 S reindex Z defZ
  have eq : {t | t ∘ reindex.symm ∈ Z} = B.terminalLabels idx := by
    ext t
    exact (carrier (t ∘ idx.symm)).symm
  have iso' : RVDefinablyEquivalent 𝓜 S.carrier U.carrier (B.terminalLabels idx) := iso.trans (eq ▸ re)
  let collapse : (Fin n ⊕ Fin 0) ≃ Fin n :=
    { toFun := Sum.elim id Fin.elim0
      invFun := Sum.inl
      left_inv := by rintro (j | j); rfl; exact Fin.elim0 j
      right_inv := fun _ => rfl }
  let read := order.trans collapse
  have sel (i : Fin n) : B.select i = E' (.inl (read i)) := by
    cases ho : order i with
    | inl j =>
      have hread : read i = j := congrArg collapse ho
      have hsel : B.select i = E' (.inl j) := (selected i).trans
        (congrArg e (congrArg (Sum.map id A.select) ho))
      exact hsel.trans (congrArg (fun a => E' (.inl a)) hread.symm)
    | inr j => exact Fin.elim0 j
  let emb := p.trans read.symm.toEmbedding
  let support := (Finset.univ : Finset (Fin d)).map emb
  have card : support.card = d := by rw [Finset.card_map,Finset.card_univ,Fintype.card_fin]
  refine ⟨B,a,idx,run,B.terminalGradedClass_of_single_support idx (baseRVZero S) rfl support card ?_ U iso'.symm⟩
  intro t ht i
  have tmem : (t ∘ idx.symm) ∘ E' ∈ Z := (carrier (t ∘ idx.symm)).1 ht
  obtain ⟨u,_,hl,hpad⟩ := tmem
  have st : i ∈ support ↔ read i ∈ Set.range p := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨j,_,rfl⟩
      exact ⟨j,(read.apply_symm_apply (p j)).symm⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,Finset.mem_univ _,read.injective ((read.apply_symm_apply (p j)).trans hj)⟩
  change (t ∘ idx.symm) (B.select i) ≠ 0 ↔ i ∈ support
  rw [sel,st]
  constructor
  · intro ne
    by_contra no
    exact ne (hpad (read i) no)
  · rintro ⟨j,e⟩
    rw [← e]
    exact fun hz => U.nonzero u j ((congrFun hl j).trans hz)

end GeneralizedEuler.Section5
