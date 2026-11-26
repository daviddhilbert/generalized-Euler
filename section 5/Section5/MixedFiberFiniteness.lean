module

public import Section5.TaggedCenterFiniteness
public import Section5.PartialFieldFunctions
public import Section5.MixedGraphIsomorphisms
public import Section5.MixedRelabeling
public import Section5.UnaryChainRules

/-! A definable mixed bijection preserves finite RV fibers over the
field tuple. Over a fixed target tuple, each inverse field coordinate
has finite image, even when the RV tags vary. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n m : ℕ} {I J : Type} [Finite I] [Finite J]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables n I
local notation "V" => MixedVariables m J

theorem MixedGraphIso.target_finiteFieldFibers_over
    (hyp : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (default : S.carrier .vf)
    {A : MixedCarrier Z n I} {B : MixedCarrier Z m J}
    (f : MixedGraphIso 𝓜 S A B)
    {T : Type*} (r : A → T) (s : B → T) (keep : ∀ a, s (f.equiv a) = r a)
    (finite : ∀ (x : Fin n → K) v, {a : A | a.val .vf = x ∧ r a = v}.Finite) :
    ∀ (y : Fin m → K) v, {b : B | b.val .vf = y ∧ s b = v}.Finite := by
  classical
  let R (i : Fin n) (b : SortedAssignment Z V) (v : fieldAssignment 1 Z) : Prop :=
    ∃ h : b ∈ B, (f.equiv.symm ⟨b,h⟩).val .vf i = v .vf 0
  have graphs (i : Fin n) : DefinableRelation 𝓜 S.carrier (R i) := by
    let take : (s : TCsort) → MixedVariables 1 Empty s → U s
      | .vf => fun _ => i
      | .rv => Empty.elim
    apply (f.symm.definable.comp (mixed_projection_graph (M := 𝓜) (S := S) take)).congr
    intro b v
    constructor
    · rintro ⟨a,⟨h,eq⟩,hv⟩
      exact ⟨h,(congrFun (congrFun eq .vf) i).trans (congrFun (congrFun hv .vf) 0)⟩
    · rintro ⟨h,e⟩
      refine ⟨(f.equiv.symm ⟨b,h⟩).val,⟨h,rfl⟩,?_⟩
      exact fieldAssignment_ext (fun j => by
        have eq : j = 0 := Subsingleton.elim _ _
        subst j
        exact e)
  have unique (i : Fin n) (a : SortedAssignment Z V) (b c : fieldAssignment 1 Z)
      (hb : R i a b) (hc : R i a c) : b = c := by
    obtain ⟨h,hb⟩ := hb
    obtain ⟨j,hc⟩ := hc
    exact fieldAssignment_ext (fun k => by
      have eq : k = 0 := Subsingleton.elim _ _
      subst k
      exact hb.symm.trans hc)
  choose value eval definable using fun i =>
    definable_partial_field_function (R i) (graphs i) (unique i) default
  let inputs (y : Fin m → K) (t : J → RV0 O) : SortedAssignment Z V
    | .vf => y
    | .rv => t
  have sameInput (b : SortedAssignment Z V) : inputs (b .vf) (b .rv) = b := by
    funext s i
    cases s <;> rfl
  let centers (i : Fin n) (y : Fin m → K) (r : J → RV0 O) := value i (inputs y r)
  have defCenter (i : Fin n) :
      DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment Z V) (v : fieldAssignment 1 Z) =>
        centers i (a .vf) (a .rv) = v .vf 0) :=
    (definable i).congr (fun a v => by change _ ↔ value i (inputs (a .vf) (a .rv)) = v .vf 0; rw [sameInput])
  intro y v
  let possible : Set (Fin n → K) := Set.pi Set.univ (fun i => Set.range (centers i y))
  have fin : possible.Finite :=
    Set.Finite.pi (fun i =>
      finite_tagged_center_range O hO power S hyp he small (centers i) (defCenter i) y)
  have invSpace : ∀ b : B, b.val .vf = y → (f.equiv.symm b).val .vf ∈ possible := by
    intro b eq i _
    let a := f.equiv.symm b
    let v : fieldAssignment 1 Z := fieldTupleAssignment (fun _ => a.val .vf i)
    have ev := eval i b.val v (show R i b.val v from ⟨b.property,rfl⟩)
    refine ⟨b.val .rv,?_⟩
    change value i (inputs y (b.val .rv)) = a.val .vf i
    rw [← eq,sameInput]
    exact ev
  have global : (⋃ x ∈ possible, {a : A | a.val .vf = x ∧ r a = v}).Finite :=
    fin.biUnion (fun x _ => finite x v)
  apply (global.image f.equiv).subset
  rintro b ⟨hb,hv⟩
  have fiber : r (f.equiv.symm b) = v :=
    (keep (f.equiv.symm b)).symm.trans ((congrArg s (f.equiv.apply_symm_apply b)).trans hv)
  exact ⟨f.equiv.symm b,Set.mem_iUnion₂.2 ⟨_,invSpace b hb,rfl,fiber⟩,f.equiv.apply_symm_apply b⟩

theorem MixedGraphIso.target_finiteFieldFibers
    (hyp : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (default : S.carrier .vf)
    {A : MixedCarrier Z n I} {B : MixedCarrier Z m J}
    (f : MixedGraphIso 𝓜 S A B)
    (finite : ∀ x : Fin n → K, {a : A | a.val .vf = x}.Finite) :
    ∀ y : Fin m → K, {b : B | b.val .vf = y}.Finite := by
  intro y
  exact (f.target_finiteFieldFibers_over O hO power S hyp he small default (fun _ => ()) (fun _ => ())
    (fun _ => rfl) (fun x v => (finite x).subset (fun _ ha => ha.1)) y ()).subset (fun _ h => ⟨h,rfl⟩)

end GeneralizedEuler.Section5
