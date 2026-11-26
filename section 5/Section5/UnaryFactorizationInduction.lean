module

public import Section5.UnarySwapChains
public import Section5.DefinableUnaryRecording
public import Section5.UnaryRecoveryExchange

/-! Factor a fixed-base mixed bijection using exchange. The induction
only moves the coordinates that remain after the recorded output. -/

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
  {n : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O

theorem unary_piecewise_from_recovered_coordinate
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {I J : Type} [Finite I] [Finite J] {A : MixedCarrier X n I} {B : MixedCarrier X n J}
    (f : MixedGraphIso 𝓜 S A B) (defA : SortedDefinableOver 𝓜 S.carrier A)
    (moving : Finset (Fin n)) (i j : Fin n) (hi : i ∈ moving) (hj : j ∈ moving)
    (fixes : FixesOutside f moving)
    (determines : ∀ x y : A, (∀ k, k ≠ i → x.val .vf k = y.val .vf k) →
      (f.equiv x).val .vf j = (f.equiv y).val .vf j → (f.equiv x).val .vf = (f.equiv y).val .vf)
    (smaller : ∀ {C D : MixedCarrier X n J} (g : MixedGraphIso 𝓜 S C D),
      SortedDefinableOver 𝓜 S.carrier C → FixesOutside g (moving.erase i) →
      UnaryPiecewise 𝓜 S n (moving.erase i) g) :
    UnaryPiecewise 𝓜 S n moving f := by
  obtain ⟨C,first,firstFix,firstValue⟩ := definable_record_output_coordinate f i j determines
  obtain ⟨D,swap,swaps,swapValue⟩ := unary_piecewise_swap O hO power S F minusOne hm hF
    B (f.target_definable defA) moving i j hi hj
  let tail := first.symm.trans (f.trans swap)
  have tailFix : FixesOutside tail (moving.erase i) := by
    intro a l hl
    obtain ⟨x,rfl⟩ := first.equiv.surjective a
    change (swap.equiv (f.equiv (first.equiv.symm (first.equiv x)))).val .vf l = (first.equiv x).val .vf l
    rw [first.equiv.symm_apply_apply, (swapValue (f.equiv x)).1]
    by_cases eq : l = i
    · subst l
      rw [Function.comp_apply,Equiv.swap_apply_left,firstValue]
    · have outside : l ∉ moving := fun h => hl (Finset.mem_erase.2 ⟨eq,h⟩)
      have nj : l ≠ j := fun e => outside (e ▸ hj)
      rw [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne eq nj,fixes x l outside]
      exact (firstFix x l (fun mem => eq (Finset.mem_singleton.1 mem))).symm
  have hf : UnaryPiecewise 𝓜 S n moving first := .unary first i hi firstFix
  have ht : UnaryPiecewise 𝓜 S n moving tail :=
    .widen (Finset.erase_subset i moving) (smaller tail (first.target_definable defA) tailFix)
  have e : (first.trans tail).trans swap.symm = f := MixedGraphIso.ext (fun a => by
    simp only [tail,MixedGraphIso.trans_apply,MixedGraphIso.symm_apply,Equiv.symm_apply_apply])
  rw [← e]
  exact .trans (.trans hf ht) (.symm swaps)

set_option linter.style.haveILetI false in
theorem unary_piecewise_factorization
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ (I : Type), Finite I → RealizesFinitelySatisfiableTypes 𝓜
      (WithBase S.carrier (MixedVariables n I)) (BaseAssignments S.carrier (MixedVariables n I)))
    (exchange : letI := valuedStructureOfSorted 𝓜 ∅
      ∀ (D : Set K) (x y : K),
        y ∈ Substructure.closure (convexLanguage L) (insert x D) →
        y ∉ Substructure.closure (convexLanguage L) D →
        x ∈ Substructure.closure (convexLanguage L) (insert y D))
    (move : letI := valuedStructureOfSorted 𝓜 ∅
      ∀ (a : Fin n → K) (y : K),
        y ∉ Substructure.closure (convexLanguage L) (S.carrier .vf ∪ Set.range a) →
        ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf y ≠ y ∧
          (∀ x ∈ S.carrier .vf ∪ Set.range a, e.toEmbedding .vf x = x) ∧
          ∀ t : RV0 O, e.toEmbedding .rv t = t)
    (moving : Finset (Fin n)) {I J : Type} [Finite I] [Finite J]
    {A : MixedCarrier X n I} {B : MixedCarrier X n J}
    (f : MixedGraphIso 𝓜 S A B) (defA : SortedDefinableOver 𝓜 S.carrier A)
    (fixes : FixesOutside f moving) :
    UnaryPiecewise 𝓜 S n moving f := by
  classical
  induction moving using Finset.strongInductionOn generalizing I J with
  | _ moving ih =>
    by_cases E₀ : moving = ∅
    · subst moving
      exact .fixed f fixes
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.2 E₀
    let C₀ := {j // j ∈ moving}
    let pos (j : C₀) : Fin n := j.val
    have out := output_field_closure_of_immediate_movers A B f.equiv f.definable
      (fun a y => move (a.val .vf) y)
    have recovers (a : A) :
        ∃ (j : C₀) (T : FieldTermTuple 𝓜 S (MixedVariables n Empty) n),
          (realizeFieldTuple T (recoveryInput i (pos j) a.val (f.equiv a).val)) .vf = (f.equiv a).val .vf := by
      obtain ⟨j,T,hj,h⟩ := output_recovery_terms_among_moving_coordinates moving i hi
        a.val (f.equiv a).val exchange (out a) (fixes a)
      exact ⟨⟨j,hj⟩,T,h⟩
    obtain ⟨C,D,defD,sub,disj,cover,determines⟩ := finite_recovered_output_partition_among
      pos i A B f.equiv (sat I inferInstance) defA f.definable recovers
    let e := (Fintype.equivFin {q // q ∈ C}).symm
    refine .partition (fun s => D (e s)) (fun s => defD (e s)) (fun s => sub (e s))
      (fun _ _ ne => disj (fun z => ne (e.injective z))) ?_ ?_
    · simpa only [e.surjective.iUnion_comp] using cover
    · intro s
      let q := e s
      let fD := f.restrict (sub q) (defD q)
      have fixesD : FixesOutside fD moving := fun x => fixes ⟨x.val,sub q x.property⟩
      have detD (x y : D q) :
          (∀ k, k ≠ i → x.val .vf k = y.val .vf k) →
          (fD.equiv x).val .vf (pos q.val.1) = (fD.equiv y).val .vf (pos q.val.1) →
          (fD.equiv x).val .vf = (fD.equiv y).val .vf :=
        determines q ⟨x.val,sub q x.property⟩ ⟨y.val,sub q y.property⟩ x.property y.property
      apply unary_piecewise_from_recovered_coordinate O hO power S F minusOne hm hF fD (defD q)
        moving i (pos q.val.1) hi q.val.1.property fixesD detD
      intro C₁ D₁ g d h
      exact ih (moving.erase i) (Finset.erase_ssubset hi) g d h

end GeneralizedEuler.Section5
