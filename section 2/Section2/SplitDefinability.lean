module

public import Section2.SeparatedSets
public import Mathlib.Basic.Finite.Sum
public import Mathlib.ModelTheory.Definability

/-! Substitution into separated predicates preserves the fixed parameter
sets on the two coordinate spaces. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v u' v' a b

abbrev SplitAssignment (G H : Type*) (I : Type*) := (I → G) × (I → H)

@[expose]
def splitRelabel {G H : Type*} {I : Type a} {J : Type b} (r : J → I) :
    SplitAssignment G H I → SplitAssignment G H J :=
  Prod.map (fun x => x ∘ r) (fun x => x ∘ r)

@[expose]
def splitApply {G H : Type*} {I : Type a} {J : Type b}
    (f : J → SplitAssignment G H I → G × H) (x : SplitAssignment G H I) :
    SplitAssignment G H J :=
  (fun j => (f j x).1, fun j => (f j x).2)

/-- The coordinates of the output are written in the final variable. -/
@[expose]
def splitTermGraph {G H : Type*} {I : Type a} (f : SplitAssignment G H I → G × H) :
    Set (SplitAssignment G H (I ⊕ Unit)) :=
  {x | (x.1 (.inr ()), x.2 (.inr ())) = f (splitRelabel Sum.inl x)}

@[expose]
def coordinateTermGraph {G : Type*} {I : Type a} (f : (I → G) → G) :
    Set ((I ⊕ Unit) → G) :=
  {x | x (.inr ()) = f (x ∘ Sum.inl)}

variable (JG : Language.{u, v}) (JH : Language.{u', v'})
  {G H : Type*} [JG.Structure G] [JH.Structure H]
  (A : Set G) (B : Set H)

/-- A finite union of rectangles with each factor definable over its
specified parameters in its own language. -/
abbrev SplitDefinable {I : Type a} (D : Set (SplitAssignment G H I)) :=
  SeparatedSets (A.Definable JG) (B.Definable JH) D

namespace SplitDefinable

variable {JG JH A B} {I : Type a} {J : Type b}

theorem inter {D F : Set (SplitAssignment G H I)}
    (hD : SplitDefinable JG JH A B D) (hF : SplitDefinable JG JH A B F) :
    SplitDefinable JG JH A B (D ∩ F) :=
  SeparatedSets.inter (fun h k => h.inter k) (fun h k => h.inter k) hD hF

theorem compl {D : Set (SplitAssignment G H I)} (hD : SplitDefinable JG JH A B D) :
    SplitDefinable JG JH A B Dᶜ :=
  SeparatedSets.compl Set.definable_univ Set.definable_univ
    (fun h => h.compl) (fun h => h.compl) (fun h k => h.inter k) (fun h k => h.inter k) hD

theorem leftCylinder {D : Set (I → G)} (hD : A.Definable JG D) :
    SplitDefinable JG JH A B (Prod.fst ⁻¹' D : Set (SplitAssignment G H I)) := by
  convert SeparatedSets.rect hD (Set.definable_univ (A := B) (L := JH)) using 1
  ext x
  simp

theorem rightCylinder {D : Set (I → H)} (hD : B.Definable JH D) :
    SplitDefinable JG JH A B (Prod.snd ⁻¹' D : Set (SplitAssignment G H I)) := by
  convert SeparatedSets.rect (Set.definable_univ (A := A) (L := JG)) hD using 1
  ext x
  simp

theorem graph_pair {f : (I → G) → G} {g : (I → H) → H}
    (hf : A.Definable JG (coordinateTermGraph f)) (hg : B.Definable JH (coordinateTermGraph g)) :
    SplitDefinable JG JH A B (splitTermGraph (fun x => (f x.1, g x.2))) := by
  convert SeparatedSets.rect hf hg using 1
  ext x
  exact (Prod.mk.injEq _ _ _ _).to_iff

theorem iInter [Finite J] {D : J → Set (SplitAssignment G H I)}
    (hD : ∀ j, SplitDefinable JG JH A B (D j)) : SplitDefinable JG JH A B (⋂ j, D j) := by
  classical
  let := Fintype.ofFinite J
  have h (U : Finset J) : SplitDefinable JG JH A B (⋂ j ∈ U, D j) := by
    induction U using Finset.induction_on with
    | empty =>
      simpa only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ] using
        (SeparatedSets.univ (A := I → G) (B := I → H) (Set.definable_univ (A := A) (L := JG))
          (Set.definable_univ (A := B) (L := JH)))
    | insert j U _ ih =>
      have eq : (⋂ j' ∈ insert j U, D j') = D j ∩ ⋂ j' ∈ U, D j' := by
        ext x
        simp [Finset.mem_insert]
      rw [eq]
      exact inter (hD j) ih
  simpa only [Finset.mem_univ, Set.iInter_true] using h Finset.univ

theorem preimage_relabel {D : Set (SplitAssignment G H J)} (hD : SplitDefinable JG JH A B D)
    (r : J → I) : SplitDefinable JG JH A B (splitRelabel r ⁻¹' D) :=
  SeparatedSets.preimage _ _ (fun h => h.preimage_comp r) (fun h => h.preimage_comp r) hD

set_option linter.style.haveILetI false in
theorem graph_piecewise {D : Set (SplitAssignment G H I)} (hD : SplitDefinable JG JH A B D)
    {f g : SplitAssignment G H I → G × H}
    (hf : SplitDefinable JG JH A B (splitTermGraph f))
    (hg : SplitDefinable JG JH A B (splitTermGraph g)) :
    letI := Classical.propDecidable
    SplitDefinable JG JH A B (splitTermGraph (fun x => if x ∈ D then f x else g x)) := by
  classical
  have h := (inter (hD.preimage_relabel (Sum.inl : I → I ⊕ Unit)) hf).union
    (inter ((compl hD).preimage_relabel (Sum.inl : I → I ⊕ Unit)) hg)
  convert h using 1
  ext x
  by_cases hx : splitRelabel Sum.inl x ∈ D <;>
    simp [splitTermGraph, hx]

theorem image_relabel [Finite I] [Finite J] {D : Set (SplitAssignment G H I)}
    (hD : SplitDefinable JG JH A B D) (r : J → I) :
    SplitDefinable JG JH A B (splitRelabel r '' D) :=
  SeparatedSets.image _ _ (fun h => h.image_comp r) (fun h => h.image_comp r) hD

theorem definable_coordinate_eq {J : Language} {M : Type*} [J.Structure M]
    {A : Set M} (i j : I) : A.Definable J {x : I → M | x i = x j} := by
  refine ⟨(Language.Term.var i).equal (Language.Term.var j), ?_⟩
  ext x
  rfl

theorem coordinate_eq (i j : I) :
    SplitDefinable JG JH A B {x : SplitAssignment G H I | (x.1 i, x.2 i) = (x.1 j, x.2 j)} := by
  have h := SeparatedSets.rect (definable_coordinate_eq (J := JG) (A := A) i j)
    (definable_coordinate_eq (J := JH) (A := B) i j)
  convert h using 1
  ext x
  exact (Prod.mk.injEq _ _ _ _).to_iff

/-- A variable's graph imposes the corresponding equality independently
on the two sets of coordinates. -/
theorem graph_coordinate (i : I) :
    SplitDefinable JG JH A B (splitTermGraph (fun x => (x.1 i, x.2 i))) :=
  coordinate_eq (.inr () : I ⊕ Unit) (.inl i)

theorem graph_relabel (r : J → I) {f : SplitAssignment G H J → G × H}
    (h : SplitDefinable JG JH A B (splitTermGraph f)) :
    SplitDefinable JG JH A B (splitTermGraph (f ∘ splitRelabel r)) := by
  convert h.preimage_relabel (Sum.map r (id : Unit → Unit)) using 1
  ext x
  rfl

theorem definable_coordinate_eq_param {J : Language} {M : Type*} [J.Structure M]
    {A : Set M} (i : I) (a : A) : A.Definable J {x : I → M | x i = a.val} := by
  refine ⟨(Language.Term.var i).equal (J.con a).term, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Language.Formula.realize_equal, Language.Term.realize_var,
    Language.Term.realize_con]

theorem coordinateTermGraph_const {J : Language} {M : Type*} [J.Structure M]
    {A : Set M} (a : A) : A.Definable J (coordinateTermGraph (fun _ : I → M => a.val)) :=
  definable_coordinate_eq_param (.inr () : I ⊕ Unit) a

theorem graph_constant (g : A) (h : B) :
    SplitDefinable JG JH A B (splitTermGraph (fun _ : SplitAssignment G H I => (g.val, h.val))) := by
  have hh := SeparatedSets.rect (definable_coordinate_eq_param (J := JG) (.inr () : I ⊕ Unit) g)
    (definable_coordinate_eq_param (J := JH) (.inr () : I ⊕ Unit) h)
  convert hh using 1
  ext x
  exact (Prod.mk.injEq _ _ _ _).to_iff

/-- Substitute terms into a separated predicate by pulling their graphs
back to one variable list and projecting away their outputs. -/
theorem preimage_splitApply [Finite I] [Finite J] {D : Set (SplitAssignment G H J)}
    (hD : SplitDefinable JG JH A B D) (f : J → SplitAssignment G H I → G × H)
    (hf : ∀ j, SplitDefinable JG JH A B (splitTermGraph (f j))) :
    SplitDefinable JG JH A B (splitApply f ⁻¹' D) := by
  let p (j : J) : I ⊕ Unit → I ⊕ J := Sum.elim Sum.inl (fun _ => .inr j)
  let domain : Set (SplitAssignment G H (I ⊕ J)) :=
    ((⋂ j, splitRelabel (p j) ⁻¹' splitTermGraph (f j)) ∩ splitRelabel Sum.inr ⁻¹' D)
  have hdomain : SplitDefinable JG JH A B domain :=
    inter (iInter fun j => preimage_relabel (hf j) (p j)) (preimage_relabel hD Sum.inr)
  have heq (x : SplitAssignment G H (I ⊕ J)) :
      x ∈ domain ↔ splitRelabel Sum.inr x = splitApply f (splitRelabel Sum.inl x) ∧
        splitRelabel Sum.inr x ∈ D := by
    simp only [domain, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, splitTermGraph,
      Set.mem_ofPred, splitRelabel, Prod.map_fst, Prod.map_snd, Function.comp_apply, p,
      Sum.elim_inr, splitApply]
    refine and_congr_left' ?_
    constructor
    · intro h
      exact Prod.ext (funext fun j => congrArg Prod.fst (h j)) (funext fun j => congrArg Prod.snd (h j))
    · intro h j
      exact Prod.ext (congrFun (congrArg Prod.fst h) j) (congrFun (congrArg Prod.snd h) j)
  convert image_relabel hdomain Sum.inl using 1
  ext x
  constructor
  · intro hx
    let y := splitApply f x
    let z : SplitAssignment G H (I ⊕ J) := (Sum.elim x.1 y.1, Sum.elim x.2 y.2)
    have hl : splitRelabel Sum.inl z = x := Prod.ext rfl rfl
    have hr : splitRelabel Sum.inr z = y := Prod.ext rfl rfl
    exact ⟨z, (heq z).mpr ⟨hr.trans (congrArg (splitApply f) hl).symm, hr.symm ▸ hx⟩, hl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨he, h⟩ := (heq z).mp hz
    change splitApply f (splitRelabel Sum.inl z) ∈ D
    exact he ▸ h

/-- Composition of term graphs is the substitution of the argument
graphs into the graph of the outer term. -/
theorem graph_comp [Finite I] [Finite J] {f : SplitAssignment G H J → G × H}
    (h : SplitDefinable JG JH A B (splitTermGraph f)) (g : J → SplitAssignment G H I → G × H)
    (hg : ∀ j, SplitDefinable JG JH A B (splitTermGraph (g j))) :
    SplitDefinable JG JH A B (splitTermGraph (f ∘ splitApply g)) := by
  let args : J ⊕ Unit → SplitAssignment G H (I ⊕ Unit) → G × H
    | .inl j => g j ∘ splitRelabel Sum.inl
    | .inr i => fun x => (x.1 (.inr i), x.2 (.inr i))
  have ha (j : J ⊕ Unit) : SplitDefinable JG JH A B (splitTermGraph (args j)) := by
    cases j with
    | inl j => exact graph_relabel Sum.inl (hg j)
    | inr j => exact graph_coordinate (.inr j : I ⊕ Unit)
  convert h.preimage_splitApply args ha using 1
  ext x
  rfl

end SplitDefinable

end GeneralizedEuler.Section2
