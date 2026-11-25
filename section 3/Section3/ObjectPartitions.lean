module

public import Section3.DefinablePartitions
public import Section3.DefinableBoundary
import all Section2.SortedSyntax
import all Section3.DefinableBoundary
import all Section3.DefinablePartitions

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set
universe u
variable {L : Language.{u,u}} {E : Type u} {V X : TCsort → Type u}
    {n m : ℕ} {s : TCsort}

private def withObjectNames (q : TCsort) :
    AddSortedBlock V .vf n q → AddSortedBlock (AddSortedBlock V s m) .vf n q :=
  Sum.elim (fun i => .inl (.inl i)) Sum.inr

abbrev objectBaseAssignment (p : ∀ q, AddSortedBlock V s m q → X q) (q : TCsort) (j : V q) := p q (.inl j)

private theorem oldTest_realize (M : SortedStructure L E X)
    (p : ∀ q, AddSortedBlock V s m q → X q) (a : Fin n → X .vf)
    (φ : SortedFormula L E (AddSortedBlock V .vf n)) :
    (φ.relabel withObjectNames).realize M (appendSortedBlock p a) ↔
      φ.realize M (appendSortedBlock (objectBaseAssignment p) a) := by
  rw [SortedFormula.realize_relabel]
  have he : (fun q => appendSortedBlock p a q ∘ withObjectNames q) = appendSortedBlock (objectBaseAssignment p) a := by
    funext q j
    cases j <;> rfl
  rw [he]

/-- The compactness assertion in 3.16–3.17 for a uniformly presented family
of imaginary objects. The object and failure predicates can be in the
expanded language. Only the specified old-base tests occur in the truth
patterns. The result includes disjointness and a formula for each piece. -/
theorem partition_of_object_types (T : SortedTheory L E)
    (A : SortedFormula L E (AddSortedBlock V .vf n))
    (points : SortedFormula L E (AddSortedBlock (AddSortedBlock V s m) .vf n))
    (bad : SortedFormula L E (AddSortedBlock V s m))
    (tests : Set (SortedFormula L E (AddSortedBlock V .vf n)))
    (typeGood : ∀ P : T.PointedModel (AddSortedBlock V s m),
      (∀ a, points.realize P.model (appendSortedBlock P.point a) →
        A.realize P.model (appendSortedBlock (objectBaseAssignment P.point) a)) →
      (∀ φ ∈ tests, ∀ a b, points.realize P.model (appendSortedBlock P.point a) →
        points.realize P.model (appendSortedBlock P.point b) →
        (φ.realize P.model (appendSortedBlock (objectBaseAssignment P.point) a) ↔
         φ.realize P.model (appendSortedBlock (objectBaseAssignment P.point) b))) → ¬ P.realizes bad) :
    ∃ F : Finset (SortedFormula L E (AddSortedBlock V .vf n)), (↑F : Set _) ⊆ tests ∧
    ∀ (M : SortedStructure L E X) (v : ∀ q, V q → X q) (_ : ∀ q, Nonempty (X q))
      (_ : ∀ φ ∈ T, φ.realize M),
    let dom := {a | A.realize M (appendSortedBlock v a)}
    let pieces := truthCell dom (fun φ => {a | φ.realize M (appendSortedBlock v a)}) F
    (∀ a ∈ dom, ∃! pat, a ∈ pieces pat) ∧
    (∀ pat, BlockDefinable M v .vf (pieces pat)) ∧
    ∀ pat (z : Fin m → X s), (∀ a, points.realize M (appendSortedBlock (appendSortedBlock v z) a) →
      a ∈ pieces pat) → ¬ bad.realize M (appendSortedBlock v z) := by
  classical
  let somePt (φ : SortedFormula L E (AddSortedBlock V .vf n)) :=
    (points.conjunction (φ.relabel withObjectNames)).exBlock .vf n
  let split (φ : SortedFormula L E (AddSortedBlock V .vf n)) := (somePt φ).conjunction (somePt φ.neg)
  have some_iff (P : T.PointedModel (AddSortedBlock V s m)) (φ) :
      P.realizes (somePt φ) ↔ ∃ a, points.realize P.model (appendSortedBlock P.point a) ∧
        φ.realize P.model (appendSortedBlock (objectBaseAssignment P.point) a) := by
    simp only [SortedTheory.PointedModel.realizes,somePt,SortedFormula.realize_exBlock,
      SortedFormula.realize_conjunction,oldTest_realize]
  obtain ⟨S,hS⟩ := T.exists_finite_formula_cover (bad.conjunction (somePt A.neg).neg)
    (fun φ : tests => split φ.val) (by
      intro P h
      obtain ⟨hb,hin⟩ := (SortedFormula.realize_conjunction _ _ _ _).mp h
      rw [SortedFormula.realize_neg] at hin
      by_contra! never
      apply typeGood P _ _ hb
      · intro a ha
        by_contra fail
        exact hin ((some_iff P A.neg).mpr ⟨a,ha,(SortedFormula.realize_neg _ _ _).mpr fail⟩)
      · intro φ hφ a b ha hb'
        have unsplit := never (⟨φ,hφ⟩ : tests)
        have rule (x y) (hx : points.realize P.model (appendSortedBlock P.point x))
            (hy : points.realize P.model (appendSortedBlock P.point y))
            (yes : φ.realize P.model (appendSortedBlock (objectBaseAssignment P.point) x))
            (no : ¬φ.realize P.model (appendSortedBlock (objectBaseAssignment P.point) y)) : False :=
          unsplit ((SortedFormula.realize_conjunction _ _ _ _).mpr
            ⟨(some_iff P φ).mpr ⟨x,hx,yes⟩,(some_iff P φ.neg).mpr ⟨y,hy,(SortedFormula.realize_neg _ _ _).mpr no⟩⟩)
        exact ⟨fun yes => by_contra (rule a b ha hb' yes),fun yes => by_contra (rule b a hb' ha yes)⟩)
  let F := S.image Subtype.val
  refine ⟨F,fun _ h => ?_,?_⟩
  · obtain ⟨φ,_,rfl⟩ := Finset.mem_image.mp h
    exact φ.property
  intro M v hne hT dom pieces
  refine ⟨?_,?_,?_⟩
  · intro a ha
    obtain ⟨p,hp⟩ := mem_truthCell dom _ F ha
    refine ⟨p,hp,fun q hq => by_contra (fun h => disjoint_left.mp (disjoint_truthCells dom _ F h) hq hp)⟩
  · intro pat
    let signed (i : F) := if pat i then i.val else i.val.neg
    refine ⟨A.conjunction (SortedFormula.allOf (Finset.univ.toList.map signed)),fun a => ?_⟩
    rw [SortedFormula.realize_conjunction,SortedFormula.realize_allOf]
    apply and_congr_right
    intro _
    simp only [List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,forall_exists_index,forall_apply_eq_imp_iff]
    apply forall_congr'
    intro i
    cases h : pat i <;> simp [signed,h,SortedFormula.realize_neg]
  · intro pat z sub hb
    let P : T.PointedModel (AddSortedBlock V s m) := ⟨X,M,appendSortedBlock v z,hne,hT⟩
    have base : objectBaseAssignment P.point = v := rfl
    have inside : ¬ P.realizes (somePt A.neg) := by
      intro outside
      obtain ⟨a,ha,hout⟩ := (some_iff P _).mp outside
      exact (SortedFormula.realize_neg _ _ _).mp hout (base.symm ▸ (sub a ha).1)
    obtain ⟨φ,hφ,both⟩ := hS P ((SortedFormula.realize_conjunction _ _ _ _).mpr
      ⟨hb,(SortedFormula.realize_neg _ _ _).mpr inside⟩)
    obtain ⟨yes,no⟩ := (SortedFormula.realize_conjunction _ _ _ _).mp both
    obtain ⟨a,ha,hin⟩ := (some_iff P φ.val).mp yes
    obtain ⟨b,hb',hout⟩ := (some_iff P φ.val.neg).mp no
    have i : φ.val ∈ F := Finset.mem_image_of_mem _ hφ
    rw [base] at hin hout
    exact (SortedFormula.realize_neg _ _ _).mp hout (((sub b hb').2 ⟨_,i⟩).mpr (((sub a ha).2 ⟨_,i⟩).mp hin))

end GeneralizedEuler.Section3
