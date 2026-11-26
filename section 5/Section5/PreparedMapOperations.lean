module

public import Section5.PreparedMaps

/-! Composition of preparations and extension by RV tags that stay
fixed. All graph constructions retain the original parameter base. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n m p : ℕ} {I J R H : Type}

theorem mixedTuple_surjective :
    Function.Surjective (mixedTuple (X := CanonicalSort O) (n := n) (R := I)) := by
  intro p
  let a : SortedAssignment (CanonicalSort O) (MixedVariables n I)
    | .vf => p.1
    | .rv => p.2
  exact ⟨a, rfl⟩

namespace PointMapDefinable

theorem comp [Finite J]
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin m) J}
    {g : PreparationPoint O (Fin m) J → PreparationPoint O (Fin p) R}
    (hf : PointMapDefinable M S f) (hg : PointMapDefinable M S g) :
    PointMapDefinable M S (g ∘ f) := by
  unfold PointMapDefinable at hf hg ⊢
  exact (DefinableRelation.comp hf hg).congr fun x y => by
    constructor
    · rintro ⟨z, hz, hy⟩
      exact (congrArg g hz).trans hy
    · intro he
      obtain ⟨z,hz⟩ := mixedTuple_surjective (f (mixedTuple x))
      exact ⟨z, hz.symm, (congrArg g hz).trans he⟩

end PointMapDefinable

/-- Attach independent RV tags temporarily to a point while a map
operates on its original coordinates. -/
@[expose] def mapKeepingTags
    (f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin m) J)
    (a : PreparationPoint O (Fin n) (I ⊕ H)) : PreparationPoint O (Fin m) (J ⊕ H) :=
  let b := f (a.1, a.2 ∘ Sum.inl)
  (b.1, Sum.elim b.2 (a.2 ∘ Sum.inr))

theorem mapKeepingTags_injective
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin m) J}
    (hf : Function.Injective f) : Function.Injective (mapKeepingTags (H := H) f) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have he : (x.1,x.2 ∘ Sum.inl) = (y.1,y.2 ∘ Sum.inl) := by
    apply hf
    exact Prod.ext h₁ (funext fun j => congrFun h₂ (.inl j))
  obtain ⟨hf, haux⟩ := Prod.mk.inj he
  refine Prod.ext hf ?_
  funext i
  cases i with
  | inl i => exact congrFun haux i
  | inr j => exact congrFun h₂ (.inr j)

theorem PointMapDefinable.keepTags [Finite H]
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin m) J}
    (hf : PointMapDefinable M S f) : PointMapDefinable M S (mapKeepingTags (H := H) f) := by
  let Old := SumVariables (MixedVariables n I) (MixedVariables m J)
  let New := SumVariables (MixedVariables n (I ⊕ H)) (MixedVariables m (J ⊕ H))
  let rename : ∀ s, Old s → New s
    | .vf => id
    | .rv => Sum.map Sum.inl Sum.inl
  unfold PointMapDefinable DefinableRelation at hf ⊢
  have hf' := hf.pullback_relabel rename
  have ht := SortedDefinableOver.iInter (fun j : H =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := New)
      .rv (.inl (.inr j)) (.inr (.inr j)))
  convert hf'.inter ht using 1
  ext a
  let p : PreparationPoint O (Fin n) I := (a .vf ∘ Sum.inl, a .rv ∘ Sum.inl ∘ Sum.inl)
  let q : PreparationPoint O (Fin m) J := (a .vf ∘ Sum.inr, a .rv ∘ Sum.inr ∘ Sum.inl)
  change ((f p).1, Sum.elim (f p).2 (a .rv ∘ Sum.inl ∘ Sum.inr)) =
      (a .vf ∘ Sum.inr, a .rv ∘ Sum.inr) ↔
    f p = q ∧ a ∈ ⋂ j : H, {a | a .rv (.inl (.inr j)) = a .rv (.inr (.inr j))}
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro eq
    obtain ⟨ha, hb⟩ := Prod.mk.inj eq
    exact ⟨Prod.ext ha (funext fun i => congrFun hb (.inl i)), fun j => congrFun hb (.inr j)⟩
  · rintro ⟨he, h⟩
    rw [he]
    refine Prod.ext rfl ?_
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact h j

end GeneralizedEuler.Section5
