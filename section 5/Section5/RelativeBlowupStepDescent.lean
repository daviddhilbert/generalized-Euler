module

public import Section5.RelativeBlowupStepSchemes
public import Section5.RelativeObjectDescent
public import Section5.RelativeElementaryDescent

/-! Descend the names from a local class step to a prepared RV index.
The two strata of the elementary center retain the same tags. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder RelativeObjectFamily RelativeRVTest

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  {P Q : TCsort → Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem relativePositiveTags_descend
    {m : ℕ} (H : SortedAssignment Z P → SortedAssignment Z Q → Prop)
    (D : Set (SortedAssignment Z (SumVariables P (RVVariables (Fin m))))) :
    descendFiberScheme H (relativePositiveTags O D) = relativePositiveTags O (descendFiberScheme H D) := by
  ext a
  let q : SortedAssignment Z Q := fun s => a s ∘ Sum.inl
  let u : SortedAssignment Z (RVVariables (Fin (m+1))) := fun s => a s ∘ Sum.inr
  let t := u .rv (Fin.last m)
  change (∃ p, H p q ∧ appendAssignments p (retainOldRVTags O u) ∈ D ∧ unsignedValue O t < 1 ∧ t ≠ 0) ↔
    ((∃ p, H p q ∧ appendAssignments p (retainOldRVTags O u) ∈ D) ∧ unsignedValue O t < 1 ∧ t ≠ 0)
  exact ⟨fun ⟨p,hp,hd,ht,nz⟩ => ⟨⟨p,hp,hd⟩,ht,nz⟩,fun ⟨⟨p,hp,hd⟩,ht,nz⟩ => ⟨p,hp,hd,ht,nz⟩⟩

variable [Finite (P .vf)] [Finite (P .rv)]

namespace RelativeBlowupRecipe

variable (R : RelativeBlowupRecipe (L := L) (O := O) (hO := hO) (power := power) S P)
  {H : SortedAssignment (CanonicalSort O) P → SortedAssignment (CanonicalSort O) Q → Prop}
  (defH : DefinableRelation (canonicalStructure (L := L) O hO power) S.carrier H)

@[expose] def descend : RelativeBlowupRecipe (L := L) (O := O) (hO := hO) (power := power) S Q :=
  ⟨R.degree,R.center.descend defH,R.restCount,fun i => (R.rest i).descend defH⟩

@[expose] def tests : List (RelativeRVTest 𝓜 S P) :=
  (RelativeRVObjectScheme.ofElementary R.center).tests ++ RelativeObjectFamily.tests R.rest

theorem descend_valid_of_tests {p : SortedAssignment Z P} {q : SortedAssignment Z Q} (hp : H p q)
    (agree : ∀ p', H p' q → Agree R.tests p p') (zero : S.carrier .rv)
    (v : R.valid zero p) : (R.descend defH).valid zero q := by
  constructor
  · have const p' h' := (agree_append.1 (agree p' h')).1
    apply R.center.descend_valid defH hp zero _ _ v.1
    · exact fun p' h' => const p' h' (ofSet R.center.tagsDefinable)
        (by simp [RelativeRVObjectScheme.tests,RelativeRVObjectScheme.ofElementary])
    · exact fun p' h' => same_ofGraph R.center.graphDefinable
        (const p' h' (ofGraph R.center.graphDefinable)
          (by simp [RelativeRVObjectScheme.tests,RelativeRVObjectScheme.ofElementary]))
  · exact RelativeObjectFamily.descend_valid_of_tests R.rest defH hp (fun p' h' => (agree_append.1 (agree p' h')).2) zero v.2

theorem descend_before_tags :
    (fun i => (R.before i).data.descend defH) = fun i => ((R.descend defH).before i).data := by
  funext i
  rcases i with (_ | i) <;> rfl

theorem descend_after_tags (neg : rv O (-1) ∈ S.carrier .rv) :
    (fun i => ((R.after neg) i).data.descend defH) = fun i => (((R.descend defH).after neg) i).data := by
  let V := R.descend defH
  funext i
  rcases i with (b | i)
  · cases b
    · rfl
    · change (RelativeRVObjectScheme.ofElementaryUpper O hO power S neg R.center).data.descend defH =
        (RelativeRVObjectScheme.ofElementaryUpper O hO power S neg V.center).data
      let pack (D : Set (SortedAssignment Z (SumVariables Q (RVVariables (Fin (R.center.arity+1))))))
          (defD : SortedDefinableOver 𝓜 S.carrier D) : RelativeRVTags 𝓜 S Q :=
        ⟨R.degree+1,R.center.arity+1,D,defD⟩
      let a := descendFiberScheme H (relativePositiveTags O R.center.tags)
      let b := relativePositiveTags O (descendFiberScheme H R.center.tags)
      have eq : a = b := relativePositiveTags_descend H R.center.tags
      have da : SortedDefinableOver 𝓜 S.carrier a :=
        descendFiberScheme_definable defH (relativePositiveTags_definable O neg R.center.tagsDefinable)
      have db : SortedDefinableOver 𝓜 S.carrier b :=
        relativePositiveTags_definable O neg (descendFiberScheme_definable defH R.center.tagsDefinable)
      change pack a da = pack b db
      have same {C D : Set (SortedAssignment Z (SumVariables Q (RVVariables (Fin (R.center.arity+1)))))}
          (e : C = D) (c : SortedDefinableOver 𝓜 S.carrier C) (d : SortedDefinableOver 𝓜 S.carrier D) :
          pack C c = pack D d := by
        cases e
        rfl
      exact same eq da db
  · rfl

end RelativeBlowupRecipe

namespace RelativeTaggedIsoScheme

variable {I J : Type}
  {A A' : I → RelativeRVTags (canonicalStructure (L := L) O hO power) S Q}
  {B B' : J → RelativeRVTags (canonicalStructure (L := L) O hO power) S Q}

@[expose] def transport (eqA : A = A') (eqB : B = B')
    (W : RelativeTaggedIsoScheme A B) : RelativeTaggedIsoScheme A' B' :=
  eqB ▸ eqA ▸ W

theorem valid_transport (eqA : A = A') (eqB : B = B')
    (W : RelativeTaggedIsoScheme A B) {q : SortedAssignment Z Q} (v : W.valid q) :
    (transport eqA eqB W).valid q := by
  subst A' B'
  exact v

end RelativeTaggedIsoScheme

namespace RelativeBlowupStepScheme

variable {I J : Type} {neg : rv O (-1) ∈ S.carrier .rv}
  {A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P I}
  {B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P J}
  {H : SortedAssignment (CanonicalSort O) P → SortedAssignment (CanonicalSort O) Q → Prop}
  (defH : DefinableRelation (canonicalStructure (L := L) O hO power) S.carrier H)

@[expose] def descend (W : RelativeBlowupStepScheme neg A B) :
    RelativeBlowupStepScheme neg (fun i => (A i).descend defH) (fun j => (B j).descend defH) :=
  match W with
  | .iso w => .iso (w.descend defH)
  | .elementary R left right => .elementary (R.descend defH)
      (RelativeTaggedIsoScheme.transport rfl (R.descend_before_tags defH) (left.descend defH))
      (RelativeTaggedIsoScheme.transport (R.descend_after_tags defH neg) rfl (right.descend defH))

@[expose] def tests [Fintype I] [Fintype J] (W : RelativeBlowupStepScheme neg A B) : List (RelativeRVTest 𝓜 S P) :=
  match W with
  | .iso w => w.tests
  | .elementary R left right => R.tests ++ left.tests ++ right.tests

theorem descend_valid_of_tests [Fintype I] [Fintype J] (W : RelativeBlowupStepScheme neg A B)
    {p : SortedAssignment Z P} {q : SortedAssignment Z Q} (hp : H p q)
    (agree : ∀ p', H p' q → Agree W.tests p p') (zero : S.carrier .rv)
    (v : W.valid zero p) : (W.descend defH).valid zero q := by
  cases W with
  | iso w => exact w.descend_valid_of_tests defH hp agree v
  | elementary R left right =>
    have testsR p' h' := (agree_append.1 (agree_append.1 (agree p' h')).1).1
    have testsL p' h' := (agree_append.1 (agree_append.1 (agree p' h')).1).2
    have testsR' p' h' := (agree_append.1 (agree p' h')).2
    exact ⟨R.descend_valid_of_tests defH hp testsR zero v.1,
      RelativeTaggedIsoScheme.valid_transport rfl (R.descend_before_tags defH) (left.descend defH)
        (left.descend_valid_of_tests defH hp testsL v.2.1),
      RelativeTaggedIsoScheme.valid_transport (R.descend_after_tags defH neg) rfl (right.descend defH)
        (right.descend_valid_of_tests defH hp testsR' v.2.2)⟩

end RelativeBlowupStepScheme

end GeneralizedEuler.Section5
