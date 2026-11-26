module

public import Section5.PureFieldFamilies
public import Section5.NamedFieldFunctions
public import Section5.HeadContractionEndpoints

/-! If a field pair has full translated leading-term fibers, use the
positioning function for the first head and a named center for the
second. The two recorded tags are exactly the fiber label and the
leading term relative to the center. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

namespace HeadContractionData

variable {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
  (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
  (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 2 0)
  (B : Set K) (c : K → K) (t : RV0 O)
  (defC : DefinableRelation (canonicalStructure (L := L) O hO power) S.carrier
    (fun (a b : fieldAssignment 1 (CanonicalSort O)) => c (a .vf 0) = b .vf 0))
  (shape : ∀ x b (q : A.tags → RV0 O),
    (x,b,q) ∈ A.verticalCarrier ↔ b 0 ∈ B ∧ rv O (x-c (b 0)) = t)

@[expose] def positionHead : HeadContractionData (n := 1) A :=
  .ofTranslation O hO power S A F minusOne hm hF (fun b => c (b 0)) defC (by
    intro b x y q h
    rw [shape,shape,h])

local notation "H" => positionHead F minusOne hm hF A B c t defC shape

theorem positionHead_target_mem (b : Fin 1 → K) (q : (H).target.tags → RV0 O) :
    (b,q) ∈ (H).target.carrier ↔ b 0 ∈ B ∧ q (.inl ()) = t := by
  change (∃ x, (x,b,q ∘ Sum.inr) ∈ A.verticalCarrier ∧
    ULift.up (rv O (x-c (b 0))) = ULift.up (q (.inl ()))) ↔ _
  constructor
  · rintro ⟨x,h,e⟩
    obtain ⟨hb,ht⟩ := (shape _ _ _).1 h
    exact ⟨hb,(congrArg ULift.down e).symm.trans ht⟩
  · rintro ⟨hb,e⟩
    obtain ⟨x,hx⟩ := rv_surjective O t
    have hx' : rv O (x + c (b 0) - c (b 0)) = t := by rw [add_sub_cancel_right,hx]
    exact ⟨x+c (b 0),(shape _ _ _).2 ⟨hb,hx'⟩,congrArg ULift.up (hx'.trans e.symm)⟩

variable (d : S.carrier .vf)
  (stable : ∀ x y : K, rv O (x-d.val) = rv O (y-d.val) → (x ∈ B ↔ y ∈ B))

@[expose] def centeredTail : HeadContractionData (n := 0) (H).target :=
  .ofTranslation O hO power S (H).target F minusOne hm hF (fun _ => d.val)
    (named_field_value_graph d) (by
      intro b x y q e
      change (Fin.cons x b,q) ∈ (H).target.carrier ↔ (Fin.cons y b,q) ∈ (H).target.carrier
      rw [positionHead_target_mem,positionHead_target_mem]
      exact and_congr_left' (stable x y e))

local notation "J" => centeredTail F minusOne hm hF A B c t defC shape d stable

theorem centeredTail_target_mem (q : (J).target.tags → RV0 O) :
    (Fin.elim0,q) ∈ (J).target.carrier ↔
      q (.inr (.inl ())) = t ∧ ∃ y ∈ B, rv O (y-d.val) = q (.inl ()) := by
  change (∃ y, (Fin.cons y Fin.elim0,q ∘ Sum.inr) ∈ (H).target.carrier ∧
    ULift.up (rv O (y-d.val)) = ULift.up (q (.inl ()))) ↔ _
  constructor
  · rintro ⟨y,h,e⟩
    obtain ⟨hy,ht⟩ := (positionHead_target_mem F minusOne hm hF A B c t defC shape _ _).1 h
    exact ⟨ht,y,hy,congrArg ULift.down e⟩
  · rintro ⟨ht,y,hy,e⟩
    exact ⟨y,(positionHead_target_mem F minusOne hm hF A B c t defC shape _ _).2 ⟨hy,ht⟩,congrArg ULift.up e⟩

theorem position_translation_run : HeadContractionRun A (J).target := .next H (.next J (.done _))

@[expose] def positionTerminalTags (empty : IsEmpty A.tags) : Fin 2 ≃ (J).target.tags :=
  Equiv.ofBijective (J).target.select (by
    constructor
    · intro i j eq
      have index (v : Fin 2) : v = 0 ∨ v = 1 := by
        refine Fin.cases (.inl rfl) (fun u => ?_) v
        exact .inr (congrArg Fin.succ (Subsingleton.elim u (0 : Fin 1)))
      rcases index i with rfl | rfl <;> rcases index j with rfl | rfl
      · rfl
      · change Sum.inr (Sum.inl ()) = Sum.inl () at eq
        cases eq
      · change Sum.inl () = Sum.inr (Sum.inl ()) at eq
        cases eq
      · rfl
    · rintro (_ | (_ | q))
      · exact ⟨1,rfl⟩
      · exact ⟨0,rfl⟩
      · exact (empty.false q).elim)

local notation "idx" => positionTerminalTags F minusOne hm hF A B c t defC shape d stable

theorem position_terminal_select (empty : IsEmpty A.tags) (i : Fin 2) :
    (J).target.terminalSelect (idx empty) i = i := (idx empty).symm_apply_apply i

theorem position_terminal_labels (empty : IsEmpty A.tags) (q : Fin 2 → RV0 O) :
    q ∈ (J).target.terminalLabels (idx empty) ↔ q 0 = t ∧ ∃ y ∈ B, rv O (y-d.val) = q 1 := by
  change (Fin.elim0,q ∘ (idx empty).symm) ∈ (J).target.carrier ↔ _
  rw [centeredTail_target_mem]
  change q ((idx empty).symm ((idx empty) 0)) = t ∧
    (∃ y ∈ B, rv O (y-d.val) = q ((idx empty).symm ((idx empty) 1))) ↔ _
  simp only [Equiv.symm_apply_apply]

end HeadContractionData

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A named center of a disc makes membership constant on its
translated leading-term fibers. -/
theorem centered_disc_stable (d : K) (r : O.ValueGroup) :
    ∀ x y : K, rv O (x-d) = rv O (y-d) → (x ∈ openDisc O d r ↔ y ∈ openDisc O d r) := by
  intro x y e
  change O.valuation (x-d) < r ↔ O.valuation (y-d) < r
  rw [← unsignedValue_rv,← unsignedValue_rv,e]

end GeneralizedEuler.Section5
