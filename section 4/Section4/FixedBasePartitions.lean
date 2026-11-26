module

public import Section4.CellProducts
public import Section4.Objects

public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder

variable {L JG JH : Language} {E : Type*} {Z : TCsort → Type*}
  {G K : Type*} [JG.Structure G] [JH.Structure K] {A : Set G} {B : Set K}
  {M : SortedStructure L E Z} {I : Type} [Finite I]

/-- Apply sorted QE and the Section 2 interpretation to an RV formula,
then partition its value space over the old values. Each surviving residue
condition is definable over the old residues. -/
theorem fixed_base_value_partition (P : RVCoordinatePresentation M JG JH A B)
    (S : SortedSubstructure M) (U : Set (I → Z .rv)) (hU : isRVSet M S U)
    (qe : ∀ φ : SortedFormula L E (FullRVVariables S I),
      ∃ q : SortedFormula L E (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    (base : ∀ p : S.carrier .rv, (P.encode p.val).1 ∈ A ∧ (P.encode p.val).2 ∈ B)
    (input : ∀ i : I, SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment G K I => P.encode (P.decode (x.1 i,x.2 i))))) :
    ∃ (n : ℕ) (D : Fin n → Set (I → G)) (R : Fin n → Set (I → K)),
      (∀ i, A.Definable JG (D i) ∧ B.Definable JH (R i)) ∧ (∀ γ, ∃! i, γ ∈ D i) ∧
      ∀ γ r i, γ ∈ D i → ((fun k => P.decode (γ k,r k)) ∈ U ↔ r ∈ R i) := by
  exact separated_partition Set.definable_univ (fun h h' => h.inter h') (fun h => h.compl)
    Set.definable_empty (fun h h' => h.union h') (P.separated_rv_pullback S hU qe base input)

omit [Finite I] in
/-- Every cell in a finite ordering of distinct representatives has a
fixed-base rank formula: quantify the tuple of representatives in RV.
This lemma applies to any uniformly definable predecessor relation. -/
theorem definable_many_witnesses (S : SortedSubstructure M) {J : Type} [Finite J]
    (pred : (I → Z .rv) → (J → Z .rv) → Prop)
    (hp : isRVSet M S {x : I ⊕ J → Z .rv | pred (x ∘ Sum.inl) (x ∘ Sum.inr)})
    (n : ℕ) : isRVSet M S {x | ∃ f : Fin n → J → Z .rv, Function.Injective f ∧ ∀ i, pred x (f i)} := by
  let V := RVVariables I
  let W := AddRVCoordinates V (Fin n × J)
  let rename (i : Fin n) : ∀ s, RVVariables (I ⊕ J) s → W s
    | .vf => PEmpty.elim
    | .rv => Sum.map id (Prod.mk i)
  let test (i : Fin n) : Set (∀ s, W s → Z s) :=
    {x | pred (x .rv ∘ Sum.inl) (fun j => x .rv (.inr (i,j)))}
  have dt (i) : SortedDefinableOver M S.carrier (test i) := hp.pullback_relabel (rename i)
  let pairs := {p : Fin n × Fin n // p.1 ≠ p.2}
  let unequal (p : pairs) (j : J) : Set (∀ s, W s → Z s) :=
    {x | x .rv (.inr (p.val.1,j)) ≠ x .rv (.inr (p.val.2,j))}
  have du (p : pairs) (j : J) : SortedDefinableOver M S.carrier (unequal p j) :=
    (SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .rv _ _).compl
  have proj := SortedDefinableOver.project_rv_coordinates
    ((SortedDefinableOver.iInter dt).inter (SortedDefinableOver.iInter fun p => SortedDefinableOver.iUnion (du p)))
  unfold isRVSet
  convert proj using 1
  ext x
  simp only [Set.mem_ofPred,Set.mem_inter_iff,Set.mem_iInter,Set.mem_iUnion,test,unequal]
  constructor
  · rintro ⟨f,hf,hp⟩
    refine ⟨Function.uncurry f,hp,fun p => ?_⟩
    exact Function.ne_iff.mp (hf.ne p.property)
  · rintro ⟨w,hw,hsep⟩
    refine ⟨Function.curry w,?_,hw⟩
    intro j k he
    by_contra hjk
    obtain ⟨i,hi⟩ := hsep ⟨(j,k),hjk⟩
    exact hi (congrFun he i)

end GeneralizedEuler.Section4
