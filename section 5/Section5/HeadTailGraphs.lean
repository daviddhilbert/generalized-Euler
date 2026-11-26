module

public import Section5.PreparedMapOperations
public import Section5.PreparationGraph

/-! Definable graphs for lifting a tail map and applying a varying head
preparation. These are the three maps used in the successor step. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type}

/-- Separate the first field coordinate. The entire auxiliary tuple
belongs to the tail data. -/
@[expose] def tailPoint (a : PreparationPoint O (Fin (n+1)) I) :
    PreparationPoint O (Fin n) I :=
  (a.1 ∘ Fin.succ, a.2)

/-- Extend a tail map to the first coordinate by keeping that coordinate fixed. -/
@[expose] def liftTailMap
    (f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J)
    (a : PreparationPoint O (Fin (n+1)) I) : PreparationPoint O (Fin (n+1)) J :=
  (Fin.cons (a.1 0) (f (tailPoint a)).1, (f (tailPoint a)).2)

theorem PointMapDefinable.liftTail
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J}
    (hf : PointMapDefinable M S f) : PointMapDefinable M S (liftTailMap f) := by
  let V := SumVariables (MixedVariables (n+1) I) (MixedVariables (n+1) J)
  let rename : ∀ s, SumVariables (MixedVariables n I) (MixedVariables n J) s → V s
    | .vf => Sum.map Fin.succ Fin.succ
    | .rv => id
  unfold PointMapDefinable DefinableRelation at hf ⊢
  have hhead := SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V)
    .vf (.inl 0) (.inr 0)
  convert (hf.pullback_relabel rename).inter hhead using 1
  ext a
  let b : PreparationPoint O (Fin n) I := (fun j => a .vf (.inl j.succ), a .rv ∘ Sum.inl)
  let c : PreparationPoint O (Fin n) J := (fun j => a .vf (.inr j.succ), a .rv ∘ Sum.inr)
  change (Fin.cons (a .vf (.inl 0)) (f b).1, (f b).2) =
      (a .vf ∘ Sum.inr, a .rv ∘ Sum.inr) ↔
    f b = c ∧ a .vf (.inl 0) = a .vf (.inr 0)
  constructor
  · intro eq
    obtain ⟨hfield, htags⟩ := Prod.mk.inj eq
    refine ⟨Prod.ext ?_ htags, ?_⟩
    · funext i
      exact congrFun hfield i.succ
    · exact congrFun hfield 0
  · rintro ⟨he, hz⟩
    rw [he]
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases hz (fun j => ?_) i
    rfl

/-- Apply the head preparation and append its complete history to the
existing auxiliary tuple. The tail field coordinates are unchanged. -/
@[expose] def headMap {k : ℕ}
    (P : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) k))
    (a : PreparationPoint O (Fin (n+1)) I) :
    PreparationPoint O (Fin (n+1)) (I ⊕ HistoryIndex k) :=
  let y := (P (a.1 ∘ Fin.succ)).map (a.1 0)
  (Fin.cons y.1 (a.1 ∘ Fin.succ), Sum.elim a.2 (encodeHistory O k y.2))

theorem headMap_definable [Finite I] {k : ℕ}
    (P : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) k))
    (hP : SortedDefinableOver M S.carrier
      {v : SortedAssignment (CanonicalSort O) (HistoryGraphVariables n k) |
        (P (v .vf ∘ Sum.inr)).map (v .vf (.inl 0)) =
          (v .vf (.inl 1), decodeHistory O k (v .rv))}) :
    PointMapDefinable M S (headMap (I := I) P) := by
  let V := SumVariables (MixedVariables (n+1) I) (MixedVariables (n+1) (I ⊕ HistoryIndex k))
  let rename : ∀ s, HistoryGraphVariables n k s → V s
    | .vf => Sum.elim (Fin.cases (.inl 0) (fun _ => .inr 0)) (fun i => .inl i.succ)
    | .rv => fun i => .inr (.inr i)
  unfold PointMapDefinable DefinableRelation
  have htail := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V)
      .vf (.inl i.succ) (.inr i.succ))
  have htags := SortedDefinableOver.iInter (fun i : I =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V)
      .rv (.inl i) (.inr (.inl i)))
  convert ((hP.pullback_relabel rename).inter htail).inter htags using 1
  ext a
  let y := (P (fun i => a .vf (.inl i.succ))).map (a .vf (.inl 0))
  let t := fun i => a .rv (.inr (.inr i))
  change (Fin.cons y.1 (fun i => a .vf (.inl i.succ)),
      Sum.elim (a .rv ∘ Sum.inl) (encodeHistory O k y.2)) =
      (a .vf ∘ Sum.inr, a .rv ∘ Sum.inr) ↔
    (y = (a .vf (.inr 0), decodeHistory O k t) ∧
      a ∈ ⋂ j : Fin n, {a | a .vf (.inl j.succ) = a .vf (.inr j.succ)}) ∧
      a ∈ ⋂ i : I, {a | a .rv (.inl i) = a .rv (.inr (.inl i))}
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro he
    obtain ⟨hv, hr⟩ := Prod.mk.inj he
    have ht : encodeHistory O k y.2 = t := funext fun i => congrFun hr (.inr i)
    refine ⟨⟨Prod.ext (congrFun hv 0) ?_, fun i => congrFun hv i.succ⟩, fun i => congrFun hr (.inl i)⟩
    rw [← ht, decode_encode_history]
  · rintro ⟨⟨he, ht⟩, hr⟩
    rw [he]
    apply Prod.ext
    · funext i
      exact Fin.cases rfl ht i
    · funext i
      cases i with
      | inl i => exact hr i
      | inr i => exact congrFun (encode_decode_history O k t) i

end GeneralizedEuler.Section5
