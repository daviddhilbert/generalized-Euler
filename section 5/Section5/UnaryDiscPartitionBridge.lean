module

public import Section5.UnaryNormalization
public import Section3.MixedPartitions

/-! The fixed-base mixed disc partition from Section 3 gives the
chart input for normalizing a unary bijection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  [DenselyOrdered O.ValueGroup] {m n : ℕ}
  {A : Set (K × (Fin m → RV0 O))} {B : Set (K × (Fin n → RV0 O))} (e : A ≃ B)

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem unary_chart_partition_of_mixed_disc_partition {I J : Type} [Finite I] [Finite J]
    (f : K × (Fin m → RV0 O) → K × (Fin n → RV0 O))
    (g : K × (Fin n → RV0 O) → K × (Fin m → RV0 O))
    (evalF : ∀ x : A, f x.val = (e x).val) (evalG : ∀ y : B, g y.val = (e.symm y).val)
    (graph : UnaryMixedGraphDefinable O hO power S e)
    (leftIndex : K × (Fin m → RV0 O) → (Fin n → RV0 O) → I)
    (rightIndex : K × (Fin n → RV0 O) → (Fin m → RV0 O) → J)
    (dLeft : ∀ i, SortedDefinableOver 𝓜 S.carrier {v : SortedAssignment (CanonicalSort O) (MixedGraphVars m n) |
      leftIndex (mixedInput v) (mixedOutput v).2 = i})
    (dRight : ∀ j, SortedDefinableOver 𝓜 S.carrier {v : SortedAssignment (CanonicalSort O) (MixedGraphVars m n) |
      rightIndex (mixedOutput v) (mixedInput v).2 = j})
    (forward : ∀ t s i c r, r ≠ 0 → openDisc O c r ⊆
      {x | (x,t) ∈ A ∧ (f (x,t)).2 = s ∧ leftIndex (x,t) s = i} →
      IsPointOrOpen O ((fun x => (f (x,t)).1) '' openDisc O c r))
    (back : ∀ s t j c r, r ≠ 0 → openDisc O c r ⊆
      {y | (y,s) ∈ B ∧ (g (y,s)).2 = t ∧ rightIndex (y,s) t = j} →
      IsPointOrOpen O ((fun y => (g (y,s)).1) '' openDisc O c r)) :
    Nonempty (UnaryChartPartition O hO power S e (I × J)) := by
  have maps : Set.MapsTo f A B := by
    intro x hx
    rw [evalF ⟨x,hx⟩]
    exact (e ⟨x,hx⟩).property
  have backMaps : Set.MapsTo g B A := by
    intro y hy
    rw [evalG ⟨y,hy⟩]
    exact (e.symm ⟨y,hy⟩).property
  have on : Set.BijOn f A B := by
    refine ⟨maps,?_,?_⟩
    · intro x hx y hy he
      exact congrArg Subtype.val (e.injective (Subtype.ext ((evalF ⟨x,hx⟩).symm.trans
        (he.trans (evalF ⟨y,hy⟩)))))
    · intro y hy
      obtain ⟨x,hx⟩ := e.surjective ⟨y,hy⟩
      exact ⟨x.val,x.property,(evalF x).trans (congrArg Subtype.val hx)⟩
  have inv : Set.InvOn g f A B := by
    constructor
    · intro x hx
      have hx' : f x ∈ B := maps hx
      have e₁ : e ⟨x,hx⟩ = ⟨f x,hx'⟩ := Subtype.ext (evalF ⟨x,hx⟩).symm
      change g (f x) = x
      rw [evalG ⟨f x,hx'⟩,← e₁,e.symm_apply_apply]
    · intro y hy
      have hy' : g y ∈ A := backMaps hy
      have e₂ : e.symm ⟨y,hy⟩ = ⟨g y,hy'⟩ := Subtype.ext (evalG ⟨y,hy⟩).symm
      change f (g y) = y
      rw [evalF ⟨g y,hy'⟩,← e₂,e.apply_symm_apply]
  let W := SumVariables (MixedVariables 1 (Fin m)) (MixedVariables 1 (Fin n))
  let vars : ∀ s, W s → MixedGraphVars m n s
    | .vf => Sum.elim (fun _ => .inl ()) (fun _ => .inr ⟨rfl⟩)
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)
  have defG : SortedDefinableOver 𝓜 S.carrier
      {w : SortedAssignment (CanonicalSort O) (MixedGraphVars m n) | mixedInput w ∈ A ∧ f (mixedInput w) = mixedOutput w} := by
    unfold UnaryMixedGraphDefinable DefinableRelation at graph
    convert graph.pullback_relabel vars using 1
    ext w
    change (mixedInput w ∈ A ∧ f (mixedInput w) = mixedOutput w) ↔
      ∃ ha : mixedInput w ∈ A, (e ⟨mixedInput w,ha⟩).val = mixedOutput w
    exact ⟨fun ⟨h,eq⟩ => ⟨h,(evalF ⟨_,h⟩).symm.trans eq⟩,
      fun ⟨h,eq⟩ => ⟨h,(evalF ⟨_,h⟩).trans eq⟩⟩
  obtain ⟨P,cover,defP,chart⟩ := definable_mixed_discToDisc_partition 𝓜 S.carrier O A B f g on inv defG
    leftIndex rightIndex dLeft dRight forward back
  refine ⟨⟨P,fun x => (cover x.val x.property).exists,?_,?_⟩⟩
  · intro i
    let ren : ∀ s, MixedVars m s → MixedVariables 1 (Fin m) s
      | .vf => fun _ => 0
      | .rv => id
    exact (defP i).2.pullback_relabel ren
  · intro i t s
    let D := {x | (x,t) ∈ P i ∧ (f (x,t)).2 = s}
    let F := fun x => (f (x,t)).1
    let G := fun y => (g (y,s)).1
    refine ⟨D,F '' D,F,G,chart i t s,?_⟩
    intro x hx ht hs
    have eq : (x.val.1,t) = x.val := Prod.ext rfl ht.symm
    constructor
    · exact ⟨eq.symm ▸ hx,by rw [eq,evalF x]; exact hs⟩
    · change (f (x.val.1,t)).1 = (e x).val.1
      rw [eq,evalF x]

end GeneralizedEuler.Section5
