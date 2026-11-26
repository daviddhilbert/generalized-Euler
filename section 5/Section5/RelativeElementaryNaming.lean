module

public import Section5.RelativeRVObjectSchemes
public import Section5.ElementaryClassSteps
import all Section4.Objects

/-! Name an actual elementary center over a generated base and identify
the realized classes of its source and both output strata. -/

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
  (neg : rv O (-1) ∈ S.carrier .rv) {P : TCsort → Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem RelativeRVObjectScheme.realize_class_of_carrier_eq
    (p : SortedAssignment Z P)
    (zero : S.carrier .rv) (hz : zero.val = 0)
    {d : ℕ} (A : RVObject 𝓜 ((𝓜).termGenerated (namedTuple S p)) d)
    (W : RelativeRVObjectScheme 𝓜 S P) (degree : W.data.degree = d) (arity : W.data.arity = A.arity)
    (v : W.valid zero p)
    (carrier : ∀ a : Fin W.data.arity → RV0 O, a ∘ Fin.cast arity.symm ∈ A.carrier ↔
      appendAssignments p (rvTupleAssignment a) ∈ W.data.tags) :
    objectClass 𝓜 _ ⟨W.data.degree,W.realize zero hz p v⟩ = objectClass 𝓜 _ ⟨d,A⟩ := by
  let B := W.realize zero hz p v
  let T := (𝓜).termGenerated (namedTuple S p)
  have iso : RVDefinablyEquivalent 𝓜 T.carrier A.carrier B.carrier :=
    rv_cast_carrier_equiv A arity.symm B.carrier carrier
  have eqOfIso {j j' : ℕ} (U : RVObject 𝓜 T j) (V : RVObject 𝓜 T j') (eq : j = j')
      (h : RVDefinablyEquivalent 𝓜 T.carrier U.carrier V.carrier) :
      objectClass 𝓜 T ⟨j,U⟩ = objectClass 𝓜 T ⟨j',V⟩ := by
    subst j'
    exact scissors_sound 𝓜 _ (.iso _ _ h)
  exact eqOfIso B A degree iso.symm

theorem relative_elementary_scheme_of_center
    (p : SortedAssignment Z P) (zero : S.carrier .rv) (hz : zero.val = 0)
    (W : GradedObject 𝓜 ((𝓜).termGenerated (namedTuple S p)))
    (sat : ∀ d, let T := (𝓜).termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d)))) :
    let T := (𝓜).termGenerated (namedTuple S p)
    let cls := objectClass 𝓜 T
    let n := show rv O (-1) ∈ T.carrier .rv from
      ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
    ∃ (A : RelativeElementaryScheme 𝓜 S P W.1) (v : A.valid zero p),
      cls ⟨_,(RelativeRVObjectScheme.ofElementary A).realize zero hz p v.1⟩ =
        cls W * residuePointClass O hO power T ∧
      cls ⟨_,(RelativeRVObjectScheme.ofElementaryLower A).realize zero hz p v.2⟩ +
        cls ⟨_,(RelativeRVObjectScheme.ofElementaryUpper O hO power S neg A).realize zero hz p
          (RelativeRVObjectScheme.ofElementaryUpper_valid O hO power S neg A zero hz p v)⟩ =
        cls W * (1 + multiplierClass O hO power T n) := by
  intro T cls n
  let U := appendUnitLabel W.2 (canonical_rvUnit_nonzero (L := L) O hO power)
  let j := Fin.last W.1
  let finiteDelete := appendUnitLabel_finite_deletion W.2 (canonical_rvUnit_nonzero (L := L) O hO power)
  let Low := zeroBlowupObject U j finiteDelete
  let High := positiveBlowupObject O hO power T U finSumFinEquiv.symm n j finiteDelete
  obtain ⟨D,G,defD,defG,matchD,matchG⟩ := relative_rv_labels_of_object p U
  obtain ⟨b,c,hb,hc⟩ := relative_elementary_bounds_of_named_object p zero hz U j finiteDelete matchD matchG sat
  let A : RelativeElementaryScheme 𝓜 S P W.1 := ⟨U.arity,b,c,j,D,G,defD,defG⟩
  have v : A.valid zero p := ⟨hb,hc⟩
  have old : cls ⟨_,(RelativeRVObjectScheme.ofElementary A).realize zero hz p v.1⟩ = cls ⟨_,U⟩ :=
    RelativeRVObjectScheme.realize_class_of_carrier_eq O hO power S p zero hz U
      (RelativeRVObjectScheme.ofElementary A) rfl rfl v.1
      (fun a => (matchD (rvTupleAssignment a)).symm)
  have low : cls ⟨_,(RelativeRVObjectScheme.ofElementaryLower A).realize zero hz p v.2⟩ = cls ⟨_,Low⟩ :=
    RelativeRVObjectScheme.realize_class_of_carrier_eq O hO power S p zero hz Low
      (RelativeRVObjectScheme.ofElementaryLower A) rfl rfl v.2
      (fun a => (matchD (rvTupleAssignment a)).symm)
  let N := RelativeRVObjectScheme.ofElementaryUpper O hO power S neg A
  have vN : N.valid zero p := RelativeRVObjectScheme.ofElementaryUpper_valid O hO power S neg A zero hz p v
  have high : cls ⟨_,N.realize zero hz p vN⟩ = cls ⟨_,High⟩ := by
    refine RelativeRVObjectScheme.realize_class_of_carrier_eq O hO power S p zero hz High N rfl rfl vN ?_
    intro a
    change (Fin (U.arity+1) → RV0 O) at a
    have strip : retainOldRVTags O (rvTupleAssignment a) = rvTupleAssignment (a ∘ Fin.castSucc) := by
      funext s u
      cases s
      · exact u.elim
      · rfl
    have oldIndex : finSumFinEquiv (m := U.arity) (n := 1) ∘ Sum.inl = Fin.castSucc := by
      funext i
      exact Fin.ext rfl
    have lastIndex : finSumFinEquiv (m := U.arity) (n := 1) (Sum.inr 0) = Fin.last U.arity := by
      apply Fin.ext
      simp
    have keep : a ∘ finSumFinEquiv ∘ Sum.inl = a ∘ Fin.castSucc :=
      congrArg (fun f : Fin U.arity → Fin (U.arity+1) => a ∘ f) oldIndex
    change (a ∘ finSumFinEquiv ∘ Sum.inl ∈ U.carrier ∧
        unsignedValue O (a (finSumFinEquiv (Sum.inr 0))) < 1 ∧ a (finSumFinEquiv (Sum.inr 0)) ≠ 0) ↔
      (appendAssignments p (retainOldRVTags O (rvTupleAssignment a)) ∈ D ∧
        unsignedValue O (a (Fin.last U.arity)) < 1 ∧ a (Fin.last U.arity) ≠ 0)
    rw [keep,lastIndex,strip,matchD]
    rfl
  obtain ⟨source,target⟩ := elementaryClassStep_center_realization O hO power T n W
  refine ⟨A,v,old.trans source,?_⟩
  change cls ⟨_,(RelativeRVObjectScheme.ofElementaryLower A).realize zero hz p v.2⟩ +
      cls ⟨_,N.realize zero hz p vN⟩ = _
  rw [low,high]
  exact target

end GeneralizedEuler.Section5
