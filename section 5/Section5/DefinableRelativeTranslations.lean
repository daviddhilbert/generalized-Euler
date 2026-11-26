module

public import Section5.RelativeBlowupGraph
public import Section5.MixedRelabeling
public import Section5.UnaryChainRules

/-! A definable positioning function of retained coordinates gives a
relatively unary translation. The original RV tuple stays fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n b : ℕ} {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O
local notation "W" => MixedVariables n I

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[expose] def translateFieldCoordinate (j : Fin n)
    (x : SortedAssignment X W) (c : K) : SortedAssignment X W
  | .vf => Function.update (x .vf) j (x .vf j - c)
  | .rv => x .rv

theorem relative_translation_graph_definable (p : Fin b → Fin n) (j : Fin n)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (A : MixedCarrier X n I) (defA : SortedDefinableOver 𝓜 S.carrier A)
    (D : Set (fieldAssignment b X)) (c : D → K)
    (inD : ∀ a ∈ A, projectFields p (fieldTupleAssignment (a .vf)) ∈ D)
    (defC : DefinableRelation 𝓜 S.carrier (fun a (b : fieldAssignment 1 X) =>
      ∃ h : a ∈ D, c ⟨a,h⟩ = b .vf 0)) :
    DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ A,
      translateFieldCoordinate O j a (c ⟨projectFields p (fieldTupleAssignment (a .vf)),inD a ha⟩) = b) := by
  let drop : (s : TCsort) → W s → MixedVariables n (I ⊕ Unit) s
    | .vf => id
    | .rv => Sum.inl
  have full := relative_blowup_graph_definable O hO power S p j F minusOne hm hF A defA D c inD defC
  have erase (a : SortedAssignment X W) (d : K) :
      (fun s => updateBlowupPoint O j a d s ∘ drop s) = translateFieldCoordinate O j a d := by
    funext s i
    cases s <;> rfl
  apply (full.comp (mixed_projection_graph (M := 𝓜) (S := S) drop)).congr
  intro a b
  constructor
  · rintro ⟨_,⟨ha,rfl⟩,eq⟩
    exact ⟨ha,(erase a _).symm.trans eq⟩
  · rintro ⟨ha,eq⟩
    exact ⟨_,⟨ha,rfl⟩,(erase a _).trans eq⟩

theorem relative_translation_iso (p : Fin b → Fin n) (j : Fin n)
    (retains : ∀ i, p i ≠ j)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (A : MixedCarrier X n I) (defA : SortedDefinableOver 𝓜 S.carrier A)
    (D : Set (fieldAssignment b X)) (c : D → K)
    (inD : ∀ a ∈ A, projectFields p (fieldTupleAssignment (a .vf)) ∈ D)
    (defC : DefinableRelation 𝓜 S.carrier (fun a (b : fieldAssignment 1 X) =>
      ∃ h : a ∈ D, c ⟨a,h⟩ = b .vf 0)) :
    let T (a : A) := translateFieldCoordinate O j a.val
      (c ⟨projectFields p (fieldTupleAssignment (a.val .vf)),inD a.val a.property⟩)
    ∃ e : MixedGraphIso 𝓜 S A (Set.range T),
      FixesOutside e {j} ∧ ∀ a : A, (e.equiv a).val = T a := by
  intro T
  let kept (a : A) : D := ⟨projectFields p (fieldTupleAssignment (a.val .vf)),inD a.val a.property⟩
  have inj : Function.Injective T := by
    intro a b eq
    have h (i : Fin n) (hi : i ≠ j) : a.val .vf i = b.val .vf i := by
      have e := congrFun (congrFun eq .vf) i
      simpa only [T,translateFieldCoordinate,Function.update_of_ne hi,kept] using e
    have ek : kept a = kept b := Subtype.ext (fieldAssignment_ext (fun i => h (p i) (retains i)))
    have head := congrFun (congrFun eq .vf) j
    change Function.update (a.val .vf) j (a.val .vf j - c (kept a)) j =
      Function.update (b.val .vf) j (b.val .vf j - c (kept b)) j at head
    rw [Function.update_self,Function.update_self,ek,sub_left_inj] at head
    apply Subtype.ext
    funext s i
    cases s
    · by_cases e : i = j
      · exact e ▸ head
      · exact h i e
    · exact congrFun (congrFun eq .rv) i
  let e := MixedGraphIso.toRange T inj
    (relative_translation_graph_definable O hO power S p j F minusOne hm hF A defA D c inD defC)
  refine ⟨e,?_,fun _ => rfl⟩
  intro a i hi
  exact Function.update_of_ne (fun h => hi (Finset.mem_singleton.2 h)) _ _

end GeneralizedEuler.Section5
