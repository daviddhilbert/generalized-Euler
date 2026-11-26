module

public import Section5.GradedScissorRealization
public import Section5.RVFamilyGraphCuts
import all Section4.RVTaggedEquivalence

/-! Combine the degreewise isomorphisms into one fixed-base isomorphism
of the tagged carriers. This keeps the degree of every point. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  (M : SortedStructure L E X) (S : SortedSubstructure M)

@[expose] def taggedGradedFamily {I : Type} [Finite I] (U : I → GradedObject M S) : RVFamily M S where
  Tag := I
  Coord i := Fin (U i).2.arity
  piece i := (U i).2.carrier
  definable i := (U i).2.definable

private def splitDegrees {I : Type} [Finite I] (U : I → GradedObject M S) :
    (taggedGradedFamily M S U).Points ≃ Σ d, (degreeFamily M S U d).Points where
  toFun x := ⟨(U x.1).1,⟨⟨x.1,rfl⟩,x.2⟩⟩
  invFun y := ⟨y.2.1.val,y.2.2⟩
  left_inv _ := rfl
  right_inv y := by
    obtain ⟨d,⟨i,hi⟩,x⟩ := y
    subst d
    rfl

/-- Equality of positive graded classes gives a fixed-base bijection
between the tagged carriers that preserves the degree of each point. -/
theorem equal_graded_classes_tagged_iso {I J : Type} [Fintype I] [Fintype J]
    (U : I → GradedObject M S) (V : J → GradedObject M S)
    (eq : ∑ i, objectClass M S (U i) = ∑ j, objectClass M S (V j)) :
    ∃ e : (taggedGradedFamily M S U).Points ≃ (taggedGradedFamily M S V).Points,
      (∀ x, (V (e x).1).1 = (U x.1).1) ∧
      ∀ i j, isRVSet M S (RVFamily.graphPiece
        (taggedGradedFamily M S U) (taggedGradedFamily M S V) e i j) := by
  classical
  choose e h using equal_graded_scissors_degree_iso M S U V eq
  let F := splitDegrees M S U
  let G := splitDegrees M S V
  let eAll := F.trans ((Equiv.sigmaCongrRight e).trans G.symm)
  have preserve (x : (taggedGradedFamily M S U).Points) : (V (eAll x).1).1 = (U x.1).1 :=
    (e (U x.1).1 ⟨⟨x.1,rfl⟩,x.2⟩).1.property
  refine ⟨eAll,preserve,?_⟩
  intro i j
  by_cases he : (V j).1 = (U i).1
  · let d := (U i).1
    let ii : (degreeFamily M S U d).Tag := ⟨i,rfl⟩
    let jj : (degreeFamily M S V d).Tag := ⟨j,he⟩
    suffices graphs :
        RVFamily.graphPiece (taggedGradedFamily M S U) (taggedGradedFamily M S V) eAll i j =
          RVFamily.graphPiece (degreeFamily M S U d) (degreeFamily M S V d) (e d) ii jj by
      rw [graphs]
      exact h d ii jj
    ext w
    change (∃ (x : (U i).2.carrier) (y : (V j).2.carrier),
      x.val = w ∘ Sum.inl ∧ y.val = w ∘ Sum.inr ∧ eAll ⟨i,x⟩ = ⟨j,y⟩) ↔
      ∃ (x : (U i).2.carrier) (y : (V j).2.carrier),
        x.val = w ∘ Sum.inl ∧ y.val = w ∘ Sum.inr ∧ e d ⟨ii,x⟩ = ⟨jj,y⟩
    have image (x : (U i).2.carrier) :
        G (eAll ⟨i,x⟩) = ⟨d,e d ⟨ii,x⟩⟩ :=
      G.apply_symm_apply _
    have target (y : (V j).2.carrier) : G ⟨j,y⟩ = ⟨d,⟨jj,y⟩⟩ := by
      have anyDegree (d' : ℕ) (eq' : (V j).1 = d') :
          G ⟨j,y⟩ = ⟨d',⟨⟨j,eq'⟩,y⟩⟩ := by
        subst d'
        rfl
      exact anyDegree d he
    constructor
    · rintro ⟨x,y,hx,hy,ex⟩
      have sameness := (image x).symm.trans ((congrArg G ex).trans (target y))
      exact ⟨x,y,hx,hy,(Sigma.mk.inj_iff.mp sameness).2.eq⟩
    · rintro ⟨x,y,hx,hy,ex⟩
      refine ⟨x,y,hx,hy,G.injective ?_⟩
      rw [image,target,ex]
  · have empty : RVFamily.graphPiece (taggedGradedFamily M S U) (taggedGradedFamily M S V) eAll i j = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro _ ⟨x,y,_,_,hxy⟩
      exact he ((congrArg (fun p : (taggedGradedFamily M S V).Points => (V p.1).1) hxy).symm.trans
        (preserve ⟨i,x⟩))
    rw [empty]
    exact ⟨.falsum,fun _ => Iff.rfl⟩

end GeneralizedEuler.Section5
