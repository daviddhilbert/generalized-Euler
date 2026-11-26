module

public import Section5.GluedBlowupStepSchemes

/-! A finite pair of local class paths has a fixed-base definable
validity test. Saturation chooses finitely many such pairs on a
disjoint definable partition of the parameter set. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  (neg : rv O (-1) ∈ S.carrier .rv)
  {P : TCsort → Type} {a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Fam" => RelativeObjectFamily 𝓜 S P

inductive RelativeBlowupPath (neg : rv O (-1) ∈ S.carrier .rv) :
    {a b : ℕ} → Fam (Fin a) → Fam (Fin b) → Type z
  | refl {a : ℕ} (A : Fam (Fin a)) : RelativeBlowupPath neg A A
  | cons {a m b : ℕ} {A : Fam (Fin a)} (C : Fam (Fin m)) {B : Fam (Fin b)}
    (head : RelativeBlowupStepScheme neg A C) (tail : RelativeBlowupPath neg C B) : RelativeBlowupPath neg A B

namespace RelativeBlowupPath

variable {neg} {A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P (Fin a)}
  {B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P (Fin b)}

@[expose] def valid (W : RelativeBlowupPath neg A B) (zero : S.carrier .rv) (p : SortedAssignment Z P) : Prop := by
  induction W with
  | refl A => exact Valid A zero p
  | @cons a m b A C B head tail ih => exact Valid A zero p ∧ head.valid zero p ∧ ih

theorem valid_definable (W : RelativeBlowupPath neg A B) (zero : S.carrier .rv) :
    SortedDefinableOver 𝓜 S.carrier {p | W.valid zero p} := by
  induction W with
  | refl A => exact RelativeObjectFamily.valid_definable A zero
  | @cons a m b A C B head tail ih =>
    exact (RelativeObjectFamily.valid_definable A zero).inter ((head.valid_definable zero).inter ih)

theorem valid_source (W : RelativeBlowupPath neg A B) {zero : S.carrier .rv} {p : SortedAssignment Z P}
    (v : W.valid zero p) : Valid A zero p := by
  cases W with
  | refl => exact v
  | cons => exact v.1

theorem valid_target (W : RelativeBlowupPath neg A B) {zero : S.carrier .rv} {p : SortedAssignment Z P}
    (v : W.valid zero p) : Valid B zero p := by
  induction W with
  | refl => exact v
  | cons _ _ _ ih => exact ih v.2.2

@[expose] def length (W : RelativeBlowupPath neg A B) : ℕ := by
  induction W with
  | refl => exact 0
  | cons _ _ _ ih => exact ih+1

theorem glued_steps {h t : ℕ} {A : RelativeObjectFamily 𝓜 S (RVVariables (Fin h)) (Fin a)}
    {B : RelativeObjectFamily 𝓜 S (RVVariables (Fin h)) (Fin b)}
    (W : RelativeBlowupPath neg A B)
    (D : RelativeRVIndex (X := CanonicalSort O) (canonicalStructure (L := L) O hO power) S h t)
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (v : ∀ p ∈ D.labels, W.valid zero (rvTupleAssignment p)) :
    BlowupSteps (ElementaryClassStep O hO power S neg) W.length
      (gluedClass zero hz D A (fun p hp => W.valid_source (v p hp)))
      (gluedClass zero hz D B (fun p hp => W.valid_target (v p hp))) := by
  induction W with
  | refl => rfl
  | cons C head tail ih =>
    let vt p hp := (v p hp).2.2
    let vC p hp := tail.valid_source (vt p hp)
    exact ⟨gluedClass zero hz D C vC,
      head.glued_step neg D zero hz (fun p hp => (v p hp).1) vC (fun p hp => (v p hp).2.1),
      ih vt⟩

end RelativeBlowupPath

variable {neg}

theorem relative_blowup_path_scheme_of_steps
    {A : Fam (Fin a)} {B : Fam (Fin b)}
    (p : SortedAssignment Z P) (zero : S.carrier .rv) (hz : zero.val = 0)
    (sat : ∀ d, let T := (𝓜).termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d))))
    {n : ℕ} (vA : Valid A zero p) (vB : Valid B zero p)
    (steps : let T := (𝓜).termGenerated (namedTuple S p)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      BlowupSteps (ElementaryClassStep O hO power T nT) n (fiberClass A zero hz p vA) (fiberClass B zero hz p vB)) :
    ∃ W : RelativeBlowupPath neg A B, W.valid zero p := by
  let T := (𝓜).termGenerated (namedTuple S p)
  let nT : rv O (-1) ∈ T.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
  change BlowupSteps (ElementaryClassStep O hO power T nT) n (fiberClass A zero hz p vA) (fiberClass B zero hz p vB) at steps
  induction n generalizing a with
  | zero =>
    have eq : fiberClass A zero hz p vA = fiberClass B zero hz p vB := steps
    obtain ⟨w,vw⟩ := isoScheme_of_fiberClass_eq A B zero hz p vA vB eq
    exact ⟨.cons B (.iso w) (.refl B),vA,vw,vB⟩
  | succ n ih =>
    obtain ⟨c,head,tail⟩ := steps
    obtain ⟨m,C,vC,eq⟩ := positive_class_has_named_family zero hz p sat c
    rw [← eq] at head tail
    obtain ⟨H,vH⟩ := relative_blowup_step_scheme_of_class_step neg A C zero hz p vA vC sat head
    obtain ⟨R,vR⟩ := ih vC tail
    exact ⟨.cons C H R,vA,vH,vR⟩

structure RelativeCommonBlowupScheme
    (neg : rv O (-1) ∈ S.carrier .rv) (A : Fam (Fin a)) (B : Fam (Fin b)) where
  count : ℕ
  target : Fam (Fin count)
  left : RelativeBlowupPath neg A target
  right : RelativeBlowupPath neg B target

namespace RelativeCommonBlowupScheme

variable {A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P (Fin a)}
  {B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P (Fin b)}

@[expose] def valid (W : RelativeCommonBlowupScheme neg A B) (zero : S.carrier .rv) (p : SortedAssignment Z P) : Prop :=
  W.left.valid zero p ∧ W.right.valid zero p

theorem valid_definable (W : RelativeCommonBlowupScheme neg A B) (zero : S.carrier .rv) :
    SortedDefinableOver 𝓜 S.carrier {p | W.valid zero p} :=
  (W.left.valid_definable zero).inter (W.right.valid_definable zero)

theorem glued_common_blowup
    {h t : ℕ} {A : RelativeObjectFamily 𝓜 S (RVVariables (Fin h)) (Fin a)}
    {B : RelativeObjectFamily 𝓜 S (RVVariables (Fin h)) (Fin b)}
    (W : RelativeCommonBlowupScheme neg A B)
    (D : RelativeRVIndex (X := CanonicalSort O) (canonicalStructure (L := L) O hO power) S h t)
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (v : ∀ p ∈ D.labels, W.valid zero (rvTupleAssignment p)) :
    CommonBlowup (ElementaryClassStep O hO power S neg)
      (gluedClass zero hz D A (fun p hp => W.left.valid_source (v p hp).1))
      (gluedClass zero hz D B (fun p hp => W.right.valid_source (v p hp).2)) :=
  ⟨_,W.left.length,W.right.length,
    W.left.glued_steps D zero hz (fun p hp => (v p hp).1),
    W.right.glued_steps D zero hz (fun p hp => (v p hp).2)⟩

end RelativeCommonBlowupScheme

theorem relative_common_blowup_scheme_of_classes
    {A : Fam (Fin a)} {B : Fam (Fin b)}
    (p : SortedAssignment Z P) (zero : S.carrier .rv) (hz : zero.val = 0)
    (sat : ∀ d, let T := (𝓜).termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d))))
    (vA : Valid A zero p) (vB : Valid B zero p)
    (common : let T := (𝓜).termGenerated (namedTuple S p)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      CommonBlowup (ElementaryClassStep O hO power T nT) (fiberClass A zero hz p vA) (fiberClass B zero hz p vB)) :
    ∃ W : RelativeCommonBlowupScheme neg A B, W.valid zero p := by
  obtain ⟨c,n,m,left,right⟩ := common
  obtain ⟨j,C,vC,eq⟩ := positive_class_has_named_family zero hz p sat c
  rw [← eq] at left right
  obtain ⟨L,hL⟩ := relative_blowup_path_scheme_of_steps p zero hz sat vA vC left
  obtain ⟨R,hR⟩ := relative_blowup_path_scheme_of_steps p zero hz sat vB vC right
  exact ⟨⟨j,C,L,R⟩,hL,hR⟩

theorem uniform_relative_common_blowup_schemes {A : Fam (Fin a)} {B : Fam (Fin b)}
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (zero : S.carrier .rv) (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (cover : ∀ p ∈ D, ∃ W : RelativeCommonBlowupScheme neg A B, W.valid zero p) :
    ∃ (C : Finset (RelativeCommonBlowupScheme neg A B)) (pieces : {i // i ∈ C} → Set (SortedAssignment Z P)),
      (∀ i, SortedDefinableOver 𝓜 S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid zero p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D :=
  finite_definable_partition_of_cover sat D defD
    (fun W : RelativeCommonBlowupScheme neg A B => {p | W.valid zero p})
    (fun W => W.valid_definable zero) cover

end GeneralizedEuler.Section5
