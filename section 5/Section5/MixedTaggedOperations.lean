module

public import Section5.MixedTaggedEquivalence

/-! Tagged sum and product of mixed families preserve fixed-base
definable isomorphisms. Each tag keeps its own ambient coordinates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.MixedTaggedFamily

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {U V : TCsort → Type} (A B C D : MixedTaggedFamily M S)

@[expose] def single [Finite (U .vf)] [Finite (U .rv)] (P : Set (SortedAssignment X U))
    (defP : SortedDefinableOver M S.carrier P) : MixedTaggedFamily M S where
  Tag := Unit
  coordinates _ := U
  finiteCoordinates _ s := by cases s <;> assumption
  piece _ := P
  definable _ := defP

@[expose] def emptyFamily (M : SortedStructure L E X) (S : SortedSubstructure M) : MixedTaggedFamily M S where
  Tag := Empty
  coordinates _ _ := Empty
  piece t := t.elim
  definable t := t.elim

@[expose] def unitFamily (M : SortedStructure L E X) (S : SortedSubstructure M) : MixedTaggedFamily M S :=
  single (M := M) (S := S) (Set.univ : Set (SortedAssignment X (fun _ => Empty)))
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => trivial⟩⟩

@[expose] def append : MixedTaggedFamily M S where
  Tag := A.Tag ⊕ B.Tag
  coordinates := Sum.elim A.coordinates B.coordinates
  finiteCoordinates i s := by cases i with | inl a => exact A.finiteCoordinates a s | inr b => exact B.finiteCoordinates b s
  piece := fun i => match i with | .inl a => A.piece a | .inr b => B.piece b
  definable i := by cases i with | inl a => exact A.definable a | inr b => exact B.definable b

theorem mixedProduct_definable {P : Set (SortedAssignment X U)} {Q : Set (SortedAssignment X V)}
    (dp : SortedDefinableOver M S.carrier P) (dq : SortedDefinableOver M S.carrier Q) :
    SortedDefinableOver M S.carrier (mixedProduct P Q) :=
  (dp.pullback_relabel (fun _ => Sum.inl)).inter (dq.pullback_relabel (fun _ => Sum.inr))

@[expose] def product : MixedTaggedFamily M S where
  Tag := A.Tag × B.Tag
  coordinates t := SumVariables (A.coordinates t.1) (B.coordinates t.2)
  finiteCoordinates t s := inferInstanceAs (Finite (A.coordinates t.1 s ⊕ B.coordinates t.2 s))
  piece t := mixedProduct (A.piece t.1) (B.piece t.2)
  definable t := mixedProduct_definable (A.definable t.1) (B.definable t.2)

@[expose] def appendPoints : A.Points ⊕ B.Points ≃ (A.append B).Points where
  toFun := Sum.elim (fun a => ⟨.inl a.1,a.2⟩) (fun b => ⟨.inr b.1,b.2⟩)
  invFun x := match x with | ⟨.inl i,p⟩ => .inl ⟨i,p⟩ | ⟨.inr j,p⟩ => .inr ⟨j,p⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by obtain ⟨i,p⟩ := x; cases i <;> rfl

@[expose] def productPoints (P : Set (SortedAssignment X U)) (Q : Set (SortedAssignment X V)) :
    P × Q ≃ mixedProduct P Q where
  toFun ab := ⟨fun s => Sum.elim (ab.1.val s) (ab.2.val s),ab.1.property,ab.2.property⟩
  invFun c := (⟨fun s => c.val s ∘ Sum.inl,c.property.1⟩,⟨fun s => c.val s ∘ Sum.inr,c.property.2⟩)
  left_inv ab := rfl
  right_inv c := by
    apply Subtype.ext
    funext s i
    cases i <;> rfl

@[expose] def cartesianPoints : A.Points × B.Points ≃ (A.product B).Points where
  toFun ab := ⟨(ab.1.1,ab.2.1),productPoints _ _ (ab.1.2,ab.2.2)⟩
  invFun c := (⟨c.1.1,((productPoints _ _).symm c.2).1⟩,⟨c.1.2,((productPoints _ _).symm c.2).2⟩)
  left_inv _ := rfl
  right_inv c := Sigma.ext rfl (heq_of_eq ((productPoints _ _).apply_symm_apply c.2))

theorem append_congr (ab : A.Iso B) (cd : C.Iso D) : (A.append C).Iso (B.append D) := by
  obtain ⟨f,defF⟩ := ab
  obtain ⟨g,defG⟩ := cd
  let e := (A.appendPoints C).symm.trans ((Equiv.sumCongr f g).trans (B.appendPoints D))
  refine ⟨e,fun i j => ?_⟩
  cases i with
  | inl i => cases j with
    | inl j =>
      apply (defF i j).congr
      intro x y
      exact ⟨fun ⟨hx,hy,h⟩ => ⟨hx,hy,congrArg (fun p => B.appendPoints D (.inl p)) h⟩,
        fun ⟨hx,hy,h⟩ => ⟨hx,hy,Sum.inl.inj ((B.appendPoints D).injective h)⟩⟩
    | inr j =>
      exact ⟨.falsum,fun _ => ⟨fun ⟨_,_,eq⟩ => Sum.inl_ne_inr (congrArg Sigma.fst eq),False.elim⟩⟩
  | inr i => cases j with
    | inl j =>
      exact ⟨.falsum,fun _ => ⟨fun ⟨_,_,eq⟩ => Sum.inr_ne_inl (congrArg Sigma.fst eq),False.elim⟩⟩
    | inr j =>
      apply (defG i j).congr
      intro x y
      exact ⟨fun ⟨hx,hy,h⟩ => ⟨hx,hy,congrArg (fun p => B.appendPoints D (.inr p)) h⟩,
        fun ⟨hx,hy,h⟩ => ⟨hx,hy,Sum.inr.inj ((B.appendPoints D).injective h)⟩⟩

theorem product_congr (ab : A.Iso B) (cd : C.Iso D) : (A.product C).Iso (B.product D) := by
  obtain ⟨f,defF⟩ := ab
  obtain ⟨g,defG⟩ := cd
  let e := (A.cartesianPoints C).symm.trans ((Equiv.prodCongr f g).trans (B.cartesianPoints D))
  refine ⟨e,fun ⟨i,s⟩ ⟨j,t⟩ => ?_⟩
  let out := SumVariables ((A.product C).coordinates (i,s)) ((B.product D).coordinates (j,t))
  let left (r : TCsort) : SumVariables (A.coordinates i) (B.coordinates j) r → out r :=
    Sum.map Sum.inl Sum.inl
  let right (r : TCsort) : SumVariables (C.coordinates s) (D.coordinates t) r → out r :=
    Sum.map Sum.inr Sum.inr
  have hf := defF i j
  have hg := defG s t
  unfold DefinableRelation at hf hg ⊢
  convert (hf.pullback_relabel left).inter (hg.pullback_relabel right) using 1
  ext w
  let x : SortedAssignment X ((A.product C).coordinates (i,s)) := fun r => w r ∘ Sum.inl
  let y : SortedAssignment X ((B.product D).coordinates (j,t)) := fun r => w r ∘ Sum.inr
  change (A.product C).graphOver (B.product D) e (i,s) (j,t) x y ↔
    A.graphOver B f i j (fun r => x r ∘ Sum.inl) (fun r => y r ∘ Sum.inl) ∧
    C.graphOver D g s t (fun r => x r ∘ Sum.inr) (fun r => y r ∘ Sum.inr)
  constructor
  · rintro ⟨hx,hy,eq⟩
    have h := congrArg (B.cartesianPoints D).symm eq
    rw [show e ⟨(i,s),⟨x,hx⟩⟩ =
      B.cartesianPoints D (f ⟨i,⟨_,hx.1⟩⟩,g ⟨s,⟨_,hx.2⟩⟩) from rfl,Equiv.symm_apply_apply] at h
    exact ⟨⟨hx.1,hy.1,congrArg Prod.fst h⟩,⟨hx.2,hy.2,congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨hx,hy,ef⟩,hx',hy',eg⟩
    refine ⟨⟨hx,hx'⟩,⟨hy,hy'⟩,(B.cartesianPoints D).symm.injective ?_⟩
    change (B.cartesianPoints D).symm (B.cartesianPoints D (f ⟨i,⟨_,hx⟩⟩,g ⟨s,⟨_,hx'⟩⟩)) = _
    rw [Equiv.symm_apply_apply]
    exact Prod.ext ef eg

end GeneralizedEuler.Section5.MixedTaggedFamily
