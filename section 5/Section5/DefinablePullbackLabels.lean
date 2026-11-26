module

public import Section5.PullbackLabels
public import Section4.FiniteScissors

/-! Fixed-base definability of the labels of a mixed pullback. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*} {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type}

theorem testDomain_definable [Finite J] {G : PointTests O n I J}
    (hG : PointTestsDefinable M S G) :
    SortedDefinableOver M S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables n I) | mixedTuple a ∈ testDomain G} := by
  unfold PointTestsDefinable DefinableRelation at hG
  have h := definable_project_mixed hG
  convert h using 1
  ext x
  change (∃ t, (mixedTuple x,t) ∈ G) ↔
    ∃ y : SortedAssignment (CanonicalSort O) (RVVariables J), (mixedTuple x,y .rv) ∈ G
  constructor
  · rintro ⟨t,ht⟩
    let a : SortedAssignment (CanonicalSort O) (RVVariables J)
      | .vf => PEmpty.elim
      | .rv => t
    exact ⟨a,ht⟩
  · rintro ⟨a,ha⟩
    exact ⟨a .rv,ha⟩

theorem PreparedMap.domain_image_definable [Finite I] [Finite J] {G : PointTests O n I J}
    (P : PreparedMap M S G) (hG : PointTestsDefinable M S G) :
    SortedDefinableOver M S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables n P.tags) |
        mixedTuple a ∈ P.map '' testDomain G} := by
  have hmap := P.definable
  unfold PointMapDefinable at hmap
  have h := hmap.image (testDomain_definable hG)
  convert h using 1
  ext a
  constructor
  · rintro ⟨p,hp,he⟩
    obtain ⟨x,rfl⟩ := mixedTuple_surjective p
    exact ⟨x,hp,he⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨mixedTuple x,hx,he⟩

/-- Pack the field leading terms and retained auxiliary tuple into a
single RV tuple for use as a graded RV object. -/
@[expose] def packPullbackLabel (p : PreparationPoint O (Fin n) I) : Fin n ⊕ I → RV0 O :=
  Sum.elim (rv O ∘ p.1) p.2

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (B : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem packPullbackLabel_definable [Finite I] :
    DefinableRelation 𝓜 B.carrier
      (fun a : SortedAssignment (CanonicalSort O) (MixedVariables n I) =>
        fun b : SortedAssignment (CanonicalSort O) (RVVariables (Fin n ⊕ I)) =>
          packPullbackLabel (mixedTuple a) = b .rv) := by
  let V := SumVariables (MixedVariables n I) (RVVariables (Fin n ⊕ I))
  let lead (i : Fin n) : SortedTerm L E (WithBase B.carrier V) .rv :=
    rvOfVF (.var (.inr (.inl i)))
  have hVF := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := B.carrier) (Var := V)
      .rv (.inr (.inl i)) (lead i))
  have hRV := SortedDefinableOver.iInter (fun i : I =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := B.carrier) (Var := V)
      .rv (.inr (.inr i)) (.inl i))
  unfold DefinableRelation
  convert hVF.inter hRV using 1
  ext a
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq, lead,
    eval_rvOfVF O hO power, SortedTerm.realize]
  change Sum.elim (rv O ∘ a .vf ∘ Sum.inl) (a .rv ∘ Sum.inl) = a .rv ∘ Sum.inr ↔ _
  constructor
  · intro h
    exact ⟨fun i => (congrFun h (.inl i)).symm, fun i => (congrFun h (.inr i)).symm⟩
  · rintro ⟨h,k⟩
    funext i
    cases i with
    | inl i => exact (h i).symm
    | inr i => exact (k i).symm

theorem prepared_labels_definable [Finite I] [Finite J] {G : PointTests O n I J}
    (P : PreparedMap 𝓜 B G) (hG : PointTestsDefinable 𝓜 B G) :
    isRVSet 𝓜 B (packPullbackLabel '' (P.map '' testDomain G)) := by
  let := P.finiteTags
  have h := (packPullbackLabel_definable hO power B (n := n) (I := P.tags)).image
    (P.domain_image_definable hG)
  unfold isRVSet
  convert h using 1
  ext a
  constructor
  · rintro ⟨p,hp,he⟩
    obtain ⟨x,rfl⟩ := mixedTuple_surjective p
    exact ⟨x,hp,he⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨mixedTuple x,hx,he⟩

end Canonical

end GeneralizedEuler.Section5
