module

public import Section5.RelativeRVWitnesses
public import Section5.DefinableBijectionSchemes
public import Section5.DefinableRelations

/-! Descend a definable witness through an index map once its
defining data are constant on each fiber of the index. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P Q U V : TCsort → Type}

@[expose] def descendFiberScheme (H : SortedAssignment X P → SortedAssignment X Q → Prop)
    (A : Set (SortedAssignment X (SumVariables P U))) :
    Set (SortedAssignment X (SumVariables Q U)) :=
  {b | ∃ p, H p (fun s => b s ∘ Sum.inl) ∧ appendAssignments p (fun s => b s ∘ Sum.inr) ∈ A}

theorem descendFiberScheme_definable [Finite (P .vf)] [Finite (P .rv)]
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H)
    {A : Set (SortedAssignment X (SumVariables P U))} (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier (descendFiberScheme H A) := by
  let T := SumVariables (SumVariables Q U) P
  let hVars (s : TCsort) : SumVariables P Q s → T s :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)
  let aVars (s : TCsort) : SumVariables P U s → T s :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  unfold DefinableRelation at defH
  convert definable_project_mixed ((defH.pullback_relabel hVars).inter (defA.pullback_relabel aVars)) using 1
  ext b
  have aEq (p : SortedAssignment X P) :
      (fun s => appendAssignments b p s ∘ aVars s) =
        appendAssignments p (fun s => b s ∘ Sum.inr) := by
    funext s i
    cases i <;> rfl
  change (∃ p, H p (fun s => b s ∘ Sum.inl) ∧ appendAssignments p (fun s => b s ∘ Sum.inr) ∈ A) ↔
    (∃ p, H p (fun s => b s ∘ Sum.inl) ∧ (fun s => appendAssignments b p s ∘ aVars s) ∈ A)
  simp only [aEq]

theorem descendFiberScheme_at
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    {A : Set (SortedAssignment X (SumVariables P U))}
    {p : SortedAssignment X P} {q : SortedAssignment X Q} (hp : H p q)
    (constant : ∀ p', H p' q → ∀ u,
      appendAssignments p u ∈ A ↔ appendAssignments p' u ∈ A)
    (u : SortedAssignment X U) :
    appendAssignments q u ∈ descendFiberScheme H A ↔ appendAssignments p u ∈ A :=
  ⟨fun ⟨p',hq,hA⟩ => (constant p' hq u).2 hA, fun h => ⟨p,hp,h⟩⟩

@[expose] def descendRelationScheme (H : SortedAssignment X P → SortedAssignment X Q → Prop)
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))) :
    Set (SortedAssignment X (SumVariables (SumVariables Q U) V)) :=
  {b | ∃ p, H p (fun s => b s ∘ Sum.inl ∘ Sum.inl) ∧
    appendAssignments (appendAssignments p (fun s => b s ∘ Sum.inl ∘ Sum.inr)) (fun s => b s ∘ Sum.inr) ∈ G}

theorem descendRelationScheme_definable [Finite (P .vf)] [Finite (P .rv)]
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H)
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defG : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier (descendRelationScheme H G) := by
  let T := SumVariables (SumVariables (SumVariables Q U) V) P
  let hVars (s : TCsort) : SumVariables P Q s → T s :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inl ∘ Sum.inl)
  let gVars (s : TCsort) : SumVariables (SumVariables P U) V s → T s :=
    Sum.elim (Sum.elim Sum.inr (Sum.inl ∘ Sum.inl ∘ Sum.inr)) (Sum.inl ∘ Sum.inr)
  unfold DefinableRelation at defH
  convert definable_project_mixed ((defH.pullback_relabel hVars).inter (defG.pullback_relabel gVars)) using 1
  ext b
  let q : SortedAssignment X Q := fun s => b s ∘ Sum.inl ∘ Sum.inl
  let u : SortedAssignment X U := fun s => b s ∘ Sum.inl ∘ Sum.inr
  let v : SortedAssignment X V := fun s => b s ∘ Sum.inr
  have gEq (p : SortedAssignment X P) :
      (fun s => appendAssignments b p s ∘ gVars s) = appendAssignments (appendAssignments p u) v := by
    funext s i
    rcases i with (i | i) | i <;> rfl
  change (∃ p, H p q ∧ appendAssignments (appendAssignments p u) v ∈ G) ↔
    (∃ p, H p q ∧ (fun s => appendAssignments b p s ∘ gVars s) ∈ G)
  simp only [gEq]

theorem descendRelationScheme_at
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {p : SortedAssignment X P} {q : SortedAssignment X Q} (hp : H p q)
    (constant : ∀ p', H p' q → ∀ u v,
      appendAssignments (appendAssignments p u) v ∈ G ↔ appendAssignments (appendAssignments p' u) v ∈ G)
    (u : SortedAssignment X U) (v : SortedAssignment X V) :
    appendAssignments (appendAssignments q u) v ∈ descendRelationScheme H G ↔
      appendAssignments (appendAssignments p u) v ∈ G :=
  ⟨fun ⟨p',hq,hG⟩ => (constant p' hq u v).2 hG, fun h => ⟨p,hp,h⟩⟩

theorem relativeRVWitness_descends {m k : ℕ}
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    {D : Set (SortedAssignment X (SumVariables P (RVVariables (Fin m))))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P (RVVariables (Fin m))) (RVVariables (Fin k))))}
    {p : SortedAssignment X P} {q : SortedAssignment X Q} (hp : H p q)
    (constD : ∀ p', H p' q → ∀ u, appendAssignments p u ∈ D ↔ appendAssignments p' u ∈ D)
    (constG : ∀ p', H p' q → ∀ u v,
      appendAssignments (appendAssignments p u) v ∈ G ↔ appendAssignments (appendAssignments p' u) v ∈ G)
    {zero : X .rv} {bound : ℕ} (valid : RelativeRVWitness D G zero bound p) :
    RelativeRVWitness (descendFiberScheme H D) (descendRelationScheme H G) zero bound q := by
  simpa only [RelativeRVWitness,descendFiberScheme_at hp constD,descendRelationScheme_at hp constG] using valid

theorem fiberBijectionScheme_descends
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    {A : Set (SortedAssignment X (SumVariables P U))}
    {B : Set (SortedAssignment X (SumVariables P V))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {p : SortedAssignment X P} {q : SortedAssignment X Q} (hp : H p q)
    (constA : ∀ p', H p' q → ∀ u, appendAssignments p u ∈ A ↔ appendAssignments p' u ∈ A)
    (constB : ∀ p', H p' q → ∀ v, appendAssignments p v ∈ B ↔ appendAssignments p' v ∈ B)
    (constG : ∀ p', H p' q → ∀ u v,
      appendAssignments (appendAssignments p u) v ∈ G ↔ appendAssignments (appendAssignments p' u) v ∈ G)
    (valid : FiberBijectionScheme A B G p) :
    FiberBijectionScheme (descendFiberScheme H A) (descendFiberScheme H B) (descendRelationScheme H G) q := by
  simpa only [FiberBijectionScheme,descendFiberScheme_at hp constA,descendFiberScheme_at hp constB,
    descendRelationScheme_at hp constG] using valid

end GeneralizedEuler.Section5
