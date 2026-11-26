module

public import Section5.RelativeRVCuts

/-! Fixed relative schemes glue along a chain of cuts, blowups, and
isomorphisms. Both chains retain one common head-start selection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

section Classes
variable {L : Language} {E : Type*} {X : TCsort → Type z} {M : SortedStructure L E X}
  {S : SortedSubstructure M} {h t : ℕ}

abbrev RelativeRVRows (I : RelativeRVIndex M S h t) := List (Σ k, RelativeRVRow I k)

variable {I : RelativeRVIndex M S h t}

@[expose] def gluedRowsClass (F : RelativeRVRows I) : RVSemiring M S :=
  (F.map (fun row => row.2.gluedClass)).sum

@[simp] theorem gluedRowsClass_singleton {k : ℕ} (A : RelativeRVRow I k) :
    gluedRowsClass [⟨k,A⟩] = A.gluedClass := by simp [gluedRowsClass]

@[simp] theorem gluedRowsClass_append (A B : RelativeRVRows I) :
    gluedRowsClass (A ++ B) = gluedRowsClass A + gluedRowsClass B := by
  simp only [gluedRowsClass,List.map_append,List.sum_append]

end Classes

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)
  {h t : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable {I : RelativeRVIndex (X := CanonicalSort O) (canonicalStructure (L := L) O hO power) S h t}

local notation "rows" => RelativeRVRows I
local notation "cls" => gluedRowsClass (I := I)

inductive RelativeRVRowStep : rows → rows → Prop
  | cut {k : ℕ} (A : RelativeRVRow I k)
      (C : Set (SortedAssignment (CanonicalSort O) A.LocusVars))
      (defC : SortedDefinableOver 𝓜 S.carrier C) :
      RelativeRVRowStep [⟨k,A⟩] [⟨k,A.restrictRow C defC⟩,⟨k,A.restrictRow Cᶜ defC.compl⟩]
  | merge {k : ℕ} (A : RelativeRVRow I k)
      (C : Set (SortedAssignment (CanonicalSort O) A.LocusVars))
      (defC : SortedDefinableOver 𝓜 S.carrier C) :
      RelativeRVRowStep [⟨k,A.restrictRow C defC⟩,⟨k,A.restrictRow Cᶜ defC.compl⟩] [⟨k,A⟩]
  | iso {k : ℕ} (A B : RelativeRVRow I k)
      (G : Set (SortedAssignment (CanonicalSort O) (SumVariables A.LocusVars (RVVariables (Fin B.arity)))))
      (defG : SortedDefinableOver 𝓜 S.carrier G)
      (valid : ∀ p : SortedAssignment (CanonicalSort O) (RVVariables (Fin h)), p .rv ∈ I.labels →
        FiberBijectionScheme A.tags B.tags G p) :
      RelativeRVRowStep [⟨k,A⟩] [⟨k,B⟩]
  | elementary {k : ℕ} (A C : RelativeRVRow I (k+1)) (j : Fin (k+1)) (f : A.DeletedBound j)
      (posIso : RVDefinablyEquivalent 𝓜 S.carrier
        (gluedRVTags I.labels (relativePositiveTags O (P := RVVariables (Fin h)) (m := A.arity) A.tags))
        (gluedRVTags I.labels C.tags)) :
      RelativeRVRowStep [⟨k+1,A⟩] [⟨k,A.lowerRow j f⟩,⟨k+1,C⟩]
  | append {A B : rows} (pre post : rows) (step : RelativeRVRowStep A B) :
      RelativeRVRowStep (pre ++ A ++ post) (pre ++ B ++ post)

local notation "lstep" => RelativeRVRowStep O hO power S (I := I)
local notation "step" => ElementaryClassStep O hO power S neg

theorem gluedRows_step {A B : rows} (s : lstep A B) : step (cls A) (cls B) := by
  induction s with
  | cut A C defC =>
    apply Or.inl
    simpa [gluedRowsClass] using A.gluedClass_cut C defC
  | merge A C defC =>
    apply Or.inl
    simpa [gluedRowsClass] using (A.gluedClass_cut C defC).symm
  | iso A B G defG valid =>
    apply Or.inl
    simpa only [gluedRowsClass_singleton] using A.gluedClass_eq_of_fiber_isomorphism B defG valid
  | elementary A C j f posIso =>
    simpa [gluedRowsClass] using A.glued_row_blowup O hO power S neg j f C posIso
  | append pre post s ih =>
    simp only [gluedRowsClass_append]
    have add := elementaryClassStep_add O hO power S neg ih (cls pre)
    have add' := elementaryClassStep_add O hO power S neg add (cls post)
    simpa only [add_comm (cls pre)] using add'

theorem gluedRows_steps {A B : rows} {n : ℕ} (s : BlowupSteps lstep n A B) :
    BlowupSteps step n (cls A) (cls B) := by
  induction n generalizing A with
  | zero =>
    have e : A = B := s
    exact congrArg cls e
  | succ n ih =>
    obtain ⟨C,head,tail⟩ := s
    exact ⟨cls C,gluedRows_step O hO power S neg head,ih tail⟩

theorem gluedRows_common_blowup {A B : rows} (s : CommonBlowup lstep A B) :
    CommonBlowup step (cls A) (cls B) := by
  obtain ⟨C,a,b,l,r⟩ := s
  exact ⟨cls C,a,b,gluedRows_steps O hO power S neg l,gluedRows_steps O hO power S neg r⟩

end GeneralizedEuler.Section5
