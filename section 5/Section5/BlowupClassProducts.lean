module

public import Section5.PositiveBlowupObject
public import Section4.DistinguishedResiduePoint
public import Section4.RVProducts
public import Section4.ValueFactorMap
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import all Section4.DistinguishedResiduePoint
import all Section4.PositivePresentations
import all Section4.Scissors

/-! Compute the two elementary blowup classes using the deleted-label
object as a common factor. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

private theorem rv_product_right_singleton
    {L : Language} {E : Type*} {X : TCsort → Type z}
    {M : SortedStructure L E X} {S : SortedSubstructure M}
    {I J : Type} [Finite I] {D : Set (I → X .rv)} (hd : isRVSet M S D)
    (u : J → X .rv) (hu : isRVSet M S ({u} : Set (J → X .rv))) :
    RVDefinablyEquivalent M S.carrier D (productSet D ({u} : Set (J → X .rv))) := by
  let B := productSet D ({u} : Set (J → X .rv))
  let e : D ≃ B :=
    { toFun := fun x => ⟨Sum.elim x.val u,x.property,rfl⟩
      invFun := fun y => ⟨y.val ∘ Sum.inl,y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro y
        apply Subtype.ext
        funext i
        cases i with
        | inl i => rfl
        | inr i => exact (congrFun (Set.mem_singleton_iff.1 y.property.2) i).symm }
  let W := RVVariables (I ⊕ (I ⊕ J))
  have hD := isRVSet_precomp (Sum.inl : I → I ⊕ (I ⊕ J)) hd
  have hPoint := isRVSet_precomp (Sum.inr ∘ Sum.inr : J → I ⊕ (I ⊕ J)) hu
  have same := SortedDefinableOver.iInter (fun i : I =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W)
      .rv (.inl i) (.inr (.inl i)))
  refine ⟨e,?_⟩
  convert hD.inter (hPoint.inter same) using 1
  ext w
  change (∃ x : D, x.val = w .rv ∘ Sum.inl ∧ Sum.elim x.val u = w .rv ∘ Sum.inr) ↔
    (w .rv ∘ Sum.inl) ∈ D ∧ ((w .rv ∘ Sum.inr ∘ Sum.inr) ∈ ({u} : Set (J → X .rv)) ∧
      w ∈ ⋂ i : I, {v | v .rv (.inl i) = v .rv (.inr (.inl i))})
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_singleton_iff]
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨hx ▸ x.property,funext fun j => (congrFun he (.inr j)).symm,
      fun i => (congrFun hx i).symm.trans (congrFun he (.inl i))⟩
  · rintro ⟨hD',hU,hSame⟩
    refine ⟨⟨_,hD'⟩,rfl,?_⟩
    funext i
    cases i with
    | inl i => exact hSame i
    | inr i => exact (congrFun hU i).symm

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k m : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- The infinitesimal nonzero multipliers with their identity structure
map in degree one. -/
def multiplierObject (hneg : rv O (-1) ∈ S.carrier .rv) : RVObject 𝓜 S 1 :=
  identityRVObject {x : Fin 1 → RV0 O | unsignedValue O (x 0) < 1 ∧ x 0 ≠ 0}
    (nonzero_multipliers_definable O hO power S hneg)
    (by
      intro x hx i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hx.2)

theorem positiveBlowup_class_factor (U : RVObject 𝓜 S (k+1))
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    objectClass 𝓜 S ⟨_,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ =
      objectClass 𝓜 S ⟨_,zeroBlowupObject U j finiteDelete⟩ *
      objectClass 𝓜 S ⟨_,multiplierObject O hO power S hneg⟩ := by
  let V := zeroBlowupObject U j finiteDelete
  let R := multiplierObject O hO power S hneg
  let W := positiveBlowupObject O hO power S U idx hneg j finiteDelete
  change objectClass 𝓜 S ⟨_,W⟩ = objectClass 𝓜 S ⟨_,V⟩ * objectClass 𝓜 S ⟨_,R⟩
  unfold objectClass
  rw [← map_mul]
  apply scissors_sound 𝓜 S
  apply RVRelation.prod V R W
  have h := rv_reindex_equivalent 𝓜 S idx
    (productSet U.carrier {x : Fin 1 → RV0 O | unsignedValue O (x 0) < 1 ∧ x 0 ≠ 0})
    (isRVSet_inter (isRVSet_precomp Sum.inl U.definable)
      (isRVSet_precomp Sum.inr (nonzero_multipliers_definable O hO power S hneg)))
  exact h

theorem blowup_original_class_factor (U : RVObject 𝓜 S (k+1)) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    objectClass 𝓜 S ⟨_,U⟩ =
      objectClass 𝓜 S ⟨_,zeroBlowupObject U j finiteDelete⟩ *
      objectClass 𝓜 S ⟨_,residuePointObject O hO power S⟩ := by
  let V := zeroBlowupObject U j finiteDelete
  let R := residuePointObject O hO power S
  change objectClass 𝓜 S ⟨_,U⟩ = objectClass 𝓜 S ⟨_,V⟩ * objectClass 𝓜 S ⟨_,R⟩
  unfold objectClass
  rw [← map_mul]
  apply scissors_sound 𝓜 S
  apply RVRelation.prod V R U
  exact (rv_product_right_singleton U.definable 1 R.definable).symm

/-- The basic relation is the class difference for the blowup of a
single degree-one point. -/
@[expose] def basicBlowupDifference {T : Type*} [CommRing T]
    (rho : RVSemiring 𝓜 S →+* T) (hneg : rv O (-1) ∈ S.carrier .rv) : T :=
  1 + rho (objectClass 𝓜 S ⟨_,multiplierObject O hO power S hneg⟩) -
    rho (objectClass 𝓜 S ⟨_,residuePointObject O hO power S⟩)

theorem elementaryBlowup_difference {T : Type*} [CommRing T]
    (rho : RVSemiring 𝓜 S →+* T) (U : RVObject 𝓜 S (k+1))
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    rho (objectClass 𝓜 S ⟨_,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ +
      objectClass 𝓜 S ⟨_,zeroBlowupObject U j finiteDelete⟩) -
      rho (objectClass 𝓜 S ⟨_,U⟩) =
    rho (objectClass 𝓜 S ⟨_,zeroBlowupObject U j finiteDelete⟩) *
      basicBlowupDifference O hO power S rho hneg := by
  rw [map_add,positiveBlowup_class_factor O hO power S U idx hneg j finiteDelete,
    blowup_original_class_factor O hO power S U j finiteDelete,map_mul,map_mul,basicBlowupDifference]
  ring

theorem elementaryBlowup_difference_mem_span {T : Type*} [CommRing T]
    (rho : RVSemiring 𝓜 S →+* T) (U : RVObject 𝓜 S (k+1))
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    rho (objectClass 𝓜 S ⟨_,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ +
      objectClass 𝓜 S ⟨_,zeroBlowupObject U j finiteDelete⟩) -
      rho (objectClass 𝓜 S ⟨_,U⟩) ∈ Ideal.span {basicBlowupDifference O hO power S rho hneg} := by
  rw [elementaryBlowup_difference O hO power S rho U idx hneg j finiteDelete]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

theorem degree_one_point_realizes_basic_difference {T : Type*} [CommRing T]
    (rho : RVSemiring 𝓜 S →+* T) (hneg : rv O (-1) ∈ S.carrier .rv)
    (idx : Fin m ≃ Fin (residuePointObject O hO power S).arity ⊕ Fin 1) :
    ∃ (U₀ : RVObject 𝓜 S 0) (U₁ : RVObject 𝓜 S 1),
      (∃ finiteDelete : ∀ t : Fin 0 → RV0 O,
        {u ∈ Set.range (residuePointObject O hO power S).label | u ∘ (0 : Fin 1).succAbove = t}.Finite,
        U₀ = zeroBlowupObject (residuePointObject O hO power S) 0 finiteDelete ∧
        U₁ = positiveBlowupObject O hO power S (residuePointObject O hO power S) idx hneg 0 finiteDelete) ∧
      rho (objectClass 𝓜 S ⟨_,U₁⟩ + objectClass 𝓜 S ⟨_,U₀⟩) -
        rho (objectClass 𝓜 S ⟨_,residuePointObject O hO power S⟩) =
          basicBlowupDifference O hO power S rho hneg := by
  let R := residuePointObject O hO power S
  have finiteDelete (t : Fin 0 → RV0 O) :
      {u ∈ Set.range R.label | u ∘ (0 : Fin 1).succAbove = t}.Finite := by
    apply (Set.finite_singleton (1 : Fin 1 → RV0 O)).subset
    rintro u ⟨⟨x,rfl⟩,_⟩
    exact x.property
  let P := positiveBlowupObject O hO power S R idx hneg 0 finiteDelete
  let Z := zeroBlowupObject R 0 finiteDelete
  refine ⟨Z,P,⟨finiteDelete,rfl,rfl⟩,?_⟩
  have one : objectClass 𝓜 S ⟨0,Z⟩ = 1 := by
    unfold objectClass
    rw [← map_one (ringConGen (RVRelation 𝓜 S)).mk']
    exact scissors_sound 𝓜 S (RVRelation.one Z ⟨1,rfl⟩)
  have he := elementaryBlowup_difference O hO power S rho R idx hneg 0 finiteDelete
  change rho (objectClass 𝓜 S ⟨_,P⟩ + objectClass 𝓜 S ⟨_,Z⟩) -
    rho (objectClass 𝓜 S ⟨_,R⟩) = _
  change rho (objectClass 𝓜 S ⟨_,P⟩ + objectClass 𝓜 S ⟨_,Z⟩) -
    rho (objectClass 𝓜 S ⟨_,R⟩) = rho (objectClass 𝓜 S ⟨_,Z⟩) *
      basicBlowupDifference O hO power S rho hneg at he
  simpa only [one,map_one,one_mul] using he

end GeneralizedEuler.Section5
