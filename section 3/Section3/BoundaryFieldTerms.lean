module

public import Section3.DefinableBoundary
import all Section3.DefinableBoundary
import all Section3.FieldBranches

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
universe u
variable {L : Language.{u,u}} {E : Type u} {X V : TCsort → Type u}

abbrev CutLabelVars (V : TCsort → Type u) (n : ℕ) := AddSortedVar (AddSortedBlock V .vf n) .rv

private def sliceNames {n : ℕ} (i : Fin (n+1)) (s : TCsort) :
    AddSortedBlock V .vf (n+1) s → AddSortedVar (CutLabelVars V n) .vf s
  | .inl j => .inl (.inl (.inl j))
  | .inr ⟨j,⟨e⟩⟩ => e ▸ (i.insertNth (α := fun _ => AddSortedVar (CutLabelVars V n) .vf .vf) (.inr ⟨rfl⟩)
      (fun k => .inl (.inl (.inr ⟨k,⟨rfl⟩⟩)))) j

private theorem sliceAssignment {n : ℕ} (v : ∀ s, V s → X s) (i : Fin (n+1)) (a : Fin n → X .vf)
    (t : X .rv) (x : X .vf) :
    (fun s => extendSortedAssignment (extendSortedAssignment (appendSortedBlock v a) t) x s ∘ sliceNames i s) =
      appendSortedBlock v (i.insertNth x a) := by
  funext s j
  rcases j with j | ⟨j,⟨e⟩⟩
  · rfl
  · subst s
    refine i.succAboveCases ?_ (fun k => ?_) j <;>
      simp [sliceNames,extendSortedAssignment,appendSortedBlock,Fin.insertNth]

/-- Corollary 3.21 as used in 3.26: a mixed unary leading-term
fiber contains a representative in the field closure of the fixed field
coordinates. Compactness gives a finite list of branch terms for each
coordinate of the *original* definable set, uniform in the field tuple. -/
theorem coordinate_branches_of_cut_points (T : SortedTheory L E)
    (M : SortedStructure L E X) (v : ∀ s, V s → X s) (hne : ∀ s, Nonempty (X s))
    (hT : ∀ φ ∈ T, φ.realize M)
    (point : ∀ {W : TCsort → Type u} (φ : SortedFormula L E (AddSortedVar W .vf)) (label : W .rv)
      (P : T.PointedModel W), P.realizes (cutFiberFormula φ label) →
      letI := valuedStructureOfSorted P.model ∅
      ∃ z ∈ Substructure.closure (convexLanguage L) (range (P.point .vf)), P.model.rvMap z = P.point .rv label)
    {n : ℕ} (A : Set (Fin (n+1) → X .vf)) (hA : BlockDefinable M v .vf A) (i : Fin (n+1)) :
    ∃ S : Finset (SortedTerm L E (AddSortedBlock V .vf n) .vf), ∀ a y,
      y ∈ rvBoundary M.rvMap {z | i.insertNth z a ∈ A} → ∃ t ∈ S, y = branchAt M v t a := by
  classical
  obtain ⟨α,hα⟩ := hA
  let U := AddSortedBlock V .vf n
  let W := CutLabelVars V n
  let φ := α.relabel (sliceNames i)
  let label : W .rv := .inr ⟨rfl⟩
  let names : U .vf → W .vf := Sum.inl
  have allNames : Function.Surjective names := by
    rintro (j|⟨h⟩)
    · exact ⟨j,rfl⟩
    · exact TCsort.noConfusion h.down
  obtain ⟨S,cover⟩ := finite_boundary_branches T φ label names (by
    intro P hp
    have he : range (P.point .vf ∘ names) = range (P.point .vf) := by
      rw [Set.range_comp,allNames.range_eq,image_univ]
    rw [he]
    exact point φ label P hp)
  let term := fun t : (convexLanguage L).Term (U .vf) => fieldTermAt (E := E) (V := U) id t
  refine ⟨S.image term,fun a y hy => ?_⟩
  let assignment := extendSortedAssignment (appendSortedBlock v a) y
  let P : T.PointedModel W := ⟨X,M,assignment,hne,hT⟩
  have sectionEq : {x | φ.realize M (extendSortedAssignment assignment x)} = {z | i.insertNth z a ∈ A} := by
    ext z
    rw [mem_ofPred_eq,show φ = _ from rfl,SortedFormula.realize_relabel,sliceAssignment]
    exact hα _
  have cut : P.realizes (cutFiberFormula φ label) := by
    apply (cutFiberFormula_realize M assignment φ label).mpr
    rwa [sectionEq]
  obtain ⟨t,ht,he⟩ := cover P cut
  refine ⟨term t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,he.symm.trans ?_⟩
  apply congrArg M.rvMap
  change (liftValuedTerm (fun j => SortedTerm.var (names j)) t).realize M assignment =
    (liftValuedTerm (fun j => SortedTerm.var (id j)) t).realize M (appendSortedBlock v a)
  simp only [realize_liftValuedTerm M (∅ : Set (X .vf)),SortedTerm.realize,id_eq]
  rfl

end GeneralizedEuler.Section3
