module

public import Section5.GeneratedParameterSchemes
public import Section5.UniformFiberBijections

/-! Definable isomorphisms between fibers over the generated bases
glue to a fixed-base definable isomorphism of the total spaces. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U V : TCsort → Type}

private abbrev firstTuple (x : SortedAssignment X (SumVariables P U)) : SortedAssignment X P :=
  fun s => x s ∘ Sum.inl

private abbrev secondTuple (x : SortedAssignment X (SumVariables P U)) : SortedAssignment X U :=
  fun s => x s ∘ Sum.inr

private theorem append_split (x : SortedAssignment X (SumVariables P U)) :
    appendAssignments (firstTuple x) (secondTuple x) = x := by
  funext s i
  cases i <;> rfl

private def fiberedEquiv (D : Set (SortedAssignment X P))
    (A : Set (SortedAssignment X (SumVariables P U))) (support : ∀ a ∈ A, firstTuple a ∈ D) :
    A ≃ Σ p : D, {u : SortedAssignment X U | appendAssignments p.val u ∈ A} where
  toFun x := ⟨⟨firstTuple x.val,support x.val x.property⟩,⟨secondTuple x.val,by
    change appendAssignments (firstTuple x.val) (secondTuple x.val) ∈ A
    rw [append_split]
    exact x.property⟩⟩
  invFun f := ⟨appendAssignments f.1.val f.2.val,f.2.property⟩
  left_inv x := Subtype.ext (append_split x.val)
  right_inv := by
    rintro ⟨p,u⟩
    rfl

/-- A single valid family of graphs glues without changing the retained tuple. -/
theorem total_bijection_of_fiber_scheme [Finite (P .vf)] [Finite (P .rv)]
    (D : Set (SortedAssignment X P)) (hD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U)))
    (B : Set (SortedAssignment X (SumVariables P V)))
    (G' : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (hg : SortedDefinableOver M S.carrier G')
    (supportA : ∀ a ∈ A, (fun s => a s ∘ Sum.inl) ∈ D)
    (supportB : ∀ b ∈ B, (fun s => b s ∘ Sum.inl) ∈ D)
    (valid : ∀ p : D, FiberBijectionScheme A B G' p.val) :
    ∃ e : A ≃ B,
      (∀ a : A, (fun s => (e a).val s ∘ Sum.inl) = (fun s => a.val s ∘ Sum.inl)) ∧
      DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, (e ⟨a,h⟩).val = b) := by
  let W := SumVariables (SumVariables P U) V
  let E₁ := fiberedEquiv D A supportA
  let E₂ := fiberedEquiv D B supportB
  let e := E₁.trans ((Equiv.sigmaCongrRight (fun p : D => (valid p).equiv)).trans E₂.symm)
  have eval (u : A) : (e u).val = appendAssignments (E₁ u).1.val ((valid (E₁ u).1).equiv (E₁ u).2).val := rfl
  refine ⟨e,fun u => ?_,?_⟩
  · rw [eval]
    rfl
  · let Z := SumVariables (SumVariables P U) (SumVariables P V)
    let takeGraph (s : TCsort) : W s → Z s := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
    let takeBase (s : TCsort) : SumVariables P P s → Z s :=
      Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
    have same := (DefinableRelation.diagonal (M := M) (A := S.carrier) (U := P))
    unfold DefinableRelation at same
    have track := (hD.pullback_relabel (fun _ => Sum.inl ∘ Sum.inl)).inter
      ((same.pullback_relabel takeBase).inter (hg.pullback_relabel takeGraph))
    have expr : DefinableRelation M S.carrier (fun a b => firstTuple a = firstTuple b ∧
        appendAssignments a (secondTuple b) ∈ G' ∧ firstTuple a ∈ D) := by
      unfold DefinableRelation
      convert track using 1
      ext x
      let a : SortedAssignment X (SumVariables P U) := fun s => x s ∘ Sum.inl
      let b : SortedAssignment X (SumVariables P V) := fun s => x s ∘ Sum.inr
      have eq : (fun s => x s ∘ takeGraph s) = appendAssignments a (secondTuple b) := by
        funext s i
        rcases i with i | i <;> rfl
      change (firstTuple a = firstTuple b ∧ appendAssignments a (secondTuple b) ∈ G' ∧ firstTuple a ∈ D) ↔
        firstTuple a ∈ D ∧ firstTuple a = firstTuple b ∧ (fun s => x s ∘ takeGraph s) ∈ G'
      rw [eq]
      exact ⟨fun ⟨he,hg,hp⟩ => ⟨hp,he,hg⟩,fun ⟨hp,he,hg⟩ => ⟨he,hg,hp⟩⟩
    refine expr.congr ?_
    intro a b
    constructor
    · rintro ⟨base,hg',hp⟩
      let p : D := ⟨firstTuple a,hp⟩
      have hm := (valid p).1 (secondTuple a)
      have ha' : a ∈ A := by
        rw [append_split] at hm
        exact hm.2 ⟨secondTuple b,by simpa only [append_split] using hg'⟩
      refine ⟨ha',?_⟩
      rw [eval]
      have hpa : appendAssignments p.val (secondTuple a) = a := append_split a
      let au : {u : SortedAssignment X U | appendAssignments p.val u ∈ A} :=
        ⟨secondTuple a,hpa.symm ▸ ha'⟩
      have he := ((valid p).equiv_graph au (secondTuple b)).1 (by rw [hpa]; exact hg')
      change appendAssignments p.val ((valid p).equiv au).val = b
      rw [he]
      change appendAssignments (firstTuple a) (secondTuple b) = b
      rw [base,append_split]
    · rintro ⟨hm,rfl⟩
      rw [eval]
      refine ⟨rfl,?_,supportA _ hm⟩
      have he := ((valid (E₁ ⟨a,hm⟩).1).equiv_graph (E₁ ⟨a,hm⟩).2 _).2 rfl
      have hpa : appendAssignments (E₁ ⟨a,hm⟩).1.val (E₁ ⟨a,hm⟩).2.val = a := append_split a
      rwa [hpa] at he

theorem uniform_total_bijection_of_generated_fibers
    [Finite (P .vf)] [Finite (P .rv)] [Finite (U .vf)] [Finite (U .rv)]
    [Finite (V .vf)] [Finite (V .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (D : Set (SortedAssignment X P)) (hD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (ha : SortedDefinableOver M S.carrier A)
    (B : Set (SortedAssignment X (SumVariables P V))) (hb : SortedDefinableOver M S.carrier B)
    (supportA : ∀ a ∈ A, (fun s => a s ∘ Sum.inl) ∈ D)
    (supportB : ∀ b ∈ B, (fun s => b s ∘ Sum.inl) ∈ D)
    (fibers : ∀ p ∈ D, ∃ e : {u : SortedAssignment X U | appendAssignments p u ∈ A} ≃
        {v : SortedAssignment X V | appendAssignments p v ∈ B},
      DefinableRelation M (M.termGenerated (namedTuple S p)).carrier
        (fun u v => ∃ hu : appendAssignments p u ∈ A, (e ⟨u,hu⟩).val = v)) :
    ∃ e : A ≃ B,
      (∀ a : A, (fun s => (e a).val s ∘ Sum.inl) = (fun s => a.val s ∘ Sum.inl)) ∧
      DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, (e ⟨a,h⟩).val = b) := by
  let W := SumVariables (SumVariables P U) V
  let I := {G : Set (SortedAssignment X W) // SortedDefinableOver M S.carrier G}
  have univ : SortedDefinableOver M S.carrier (Set.univ : Set (SortedAssignment X P)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  obtain ⟨B',G',_,hg,hChoice⟩ := uniform_fiber_bijection_schemes sat D A
    (fun _ : I => B) Subtype.val (fun _ => Set.univ) hD ha (fun _ => hb)
    Subtype.property (fun _ => univ) (by
      intro p hp
      obtain ⟨e,he⟩ := fibers p hp
      obtain ⟨H,hH,h⟩ := definable_relation_fiber_as_scheme p _ he
      exact ⟨⟨H,hH⟩,Set.mem_univ _,fiberBijectionScheme_of_equiv p e h⟩)
  have valid (p : D) : FiberBijectionScheme A B G' p.val := by
    obtain ⟨h,_,_,hb',_⟩ := hChoice p.val p.property
    simpa only [FiberBijectionScheme,hb'] using h
  exact total_bijection_of_fiber_scheme D hD A B G' hg supportA supportB valid

end GeneralizedEuler.Section5
