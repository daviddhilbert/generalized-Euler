module

public import Section5.HeadContractionFamilies
public import Section5.DefinableRelations
public import Section5.PreparedMapOperations

/-! Lifting a head contraction reinstates the full leading-term fiber
in its field coordinate. The other field and RV coordinates are
carried through by a fixed-base definable bijection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ} {A : RetainedFieldFamily M S (n+1) k}

namespace HeadContractionData

variable (H : HeadContractionData A)

@[expose] def liftedCarrier : Set (PreparationPoint O (Fin (n+1)) H.target.tags) :=
  {q | (q.1 ∘ Fin.succ,q.2) ∈ H.target.carrier ∧ rv O (q.1 0) = q.2 (.inl (lastIndex H.length))}

@[expose] def liftPoint (p : PreparationPoint O (Fin (n+1)) A.tags) :
    PreparationPoint O (Fin (n+1)) H.target.tags :=
  let T := H.preparation (p.1 ∘ Fin.succ)
  let x := p.1 0
  (Fin.cons (T.map x).1 (p.1 ∘ Fin.succ),Sum.elim (encodeHistory O H.length (T.label x)) p.2)

omit [Field K] in
private theorem splitField (p : Fin (n+1) → K) : Fin.cons (p 0) (p ∘ Fin.succ) = p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem liftPoint_image : H.liftPoint '' A.carrier = H.liftedCarrier := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    let b := p.1 ∘ Fin.succ
    let T := H.preparation b
    let x := p.1 0
    have lead := H.finalLead b (encodeHistory O H.length (T.label x))
    rw [decode_encode_history] at lead
    refine ⟨⟨x,?_,(decode_encode_history O H.length (T.label x)).symm⟩,?_⟩
    · change (Fin.cons x b,p.2) ∈ A.carrier
      rw [splitField]
      exact hp
    · change rv O (T.map x).1 = encodeHistory O H.length (T.label x) (lastIndex H.length)
      rw [← lead]
      exact T.leading x
  · rintro ⟨⟨x,hx,hlabel⟩,hlead⟩
    let b := q.1 ∘ Fin.succ
    let T := H.preparation b
    let y := q.1 0 + T.offset (T.label x)
    have diff : y - T.offset (T.label x) = q.1 0 := add_sub_cancel_right _ _
    have lead : T.lead (T.label x) = q.2 (.inl (lastIndex H.length)) := by
      rw [hlabel]
      exact H.finalLead b (q.2 ∘ Sum.inl)
    have same : T.label y = T.label x := T.constant_label (by rw [diff,hlead,lead])
    have hy : (Fin.cons y b,q.2 ∘ Sum.inr) ∈ A.carrier :=
      (H.constant b y x (q.2 ∘ Sum.inr) same).2 hx
    refine ⟨(Fin.cons y b,q.2 ∘ Sum.inr),hy,Prod.ext ?_ ?_⟩
    · change Fin.cons (y - T.offset (T.label y)) b = q.1
      rw [same,diff,splitField]
    · change Sum.elim (encodeHistory O H.length (T.label y)) (q.2 ∘ Sum.inr) = q.2
      rw [same,hlabel,encode_decode_history]
      funext i
      cases i <;> rfl

theorem liftPoint_injective : Function.Injective H.liftPoint := by
  intro p q e
  let b := p.1 ∘ Fin.succ
  let b' := q.1 ∘ Fin.succ
  have sameTail : b = b' := funext (fun i => congrFun (congrArg Prod.fst e) i.succ)
  have sameTags : p.2 = q.2 := funext (fun i => congrFun (congrArg Prod.snd e) (.inr i))
  have sameHead : (H.preparation b).map (p.1 0) = (H.preparation b).map (q.1 0) := by
    have hv := congrFun (congrArg Prod.fst e) 0
    have hrv := congrArg (fun u => decodeHistory O H.length (u ∘ Sum.inl)) (congrArg Prod.snd e)
    change decodeHistory O H.length (encodeHistory O H.length ((H.preparation b).label (p.1 0))) =
      decodeHistory O H.length (encodeHistory O H.length ((H.preparation b').label (q.1 0))) at hrv
    rw [decode_encode_history,decode_encode_history,← sameTail] at hrv
    refine Prod.ext ?_ hrv
    change ((H.preparation b).map (p.1 0)).1 = ((H.preparation b').map (q.1 0)).1 at hv
    rwa [← sameTail] at hv
  have x := (H.preparation b).map_injective sameHead
  exact Prod.ext (by rw [← splitField p.1,← splitField q.1]; exact congrArg₂ Fin.cons x sameTail) sameTags

theorem liftPoint_preserves_selected (p : PreparationPoint O (Fin (n+1)) A.tags) :
    (H.liftPoint p).2 ∘ H.target.select ∘ Fin.castSucc = p.2 ∘ A.select := by
  funext i
  simp only [Function.comp_apply,target,Fin.lastCases_castSucc,liftPoint,Sum.elim_inr]

theorem liftPoint_definable :
    DefinableRelation M S.carrier
      (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) A.tags))
        (b : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) H.target.tags)) =>
        H.liftPoint (mixedTuple a) = mixedTuple b) := by
  let U := MixedVariables (n+1) A.tags
  let V := MixedVariables (n+1) H.target.tags
  let W := SumVariables U V
  let take : (s : TCsort) → HistoryGraphVariables n H.length s → W s
    | .vf => Sum.elim (fun j => if j = 0 then .inl 0 else .inr 0) (Sum.inl ∘ Fin.succ)
    | .rv => Sum.inr ∘ Sum.inl
  have tail := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .vf (.inl i.succ) (.inr i.succ))
  let := A.finiteTags
  have tags := SortedDefinableOver.iInter (fun i : A.tags =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .rv (.inl i) (.inr (.inr i)))
  unfold DefinableRelation
  convert (H.mapGraph.pullback_relabel take).inter (tail.inter tags) using 1
  ext w
  let p : PreparationPoint O (Fin (n+1)) A.tags := (w .vf ∘ Sum.inl,w .rv ∘ Sum.inl)
  let q : PreparationPoint O (Fin (n+1)) H.target.tags := (w .vf ∘ Sum.inr,w .rv ∘ Sum.inr)
  let T := H.preparation (p.1 ∘ Fin.succ)
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change H.liftPoint p = q ↔ T.map (p.1 0) = (q.1 0,decodeHistory O H.length (q.2 ∘ Sum.inl)) ∧
    (∀ i : Fin n, p.1 i.succ = q.1 i.succ) ∧ (∀ i : A.tags, p.2 i = q.2 (.inr i))
  constructor
  · intro eq
    rw [← eq]
    constructor
    · exact Prod.ext rfl (decode_encode_history O H.length (T.label (p.1 0))).symm
    · exact ⟨fun _ => rfl,fun _ => rfl⟩
  · rintro ⟨hh,ht,hr⟩
    have lead : encodeHistory O H.length (T.label (p.1 0)) = q.2 ∘ Sum.inl := by
      rw [show T.label (p.1 0) = decodeHistory O H.length (q.2 ∘ Sum.inl) from congrArg Prod.snd hh,
        encode_decode_history]
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ht j) i
      exact congrArg Prod.fst hh
    · funext i
      rcases i with j | j
      · exact congrFun lead j
      · exact hr j

theorem liftedCarrier_definable :
    SortedDefinableOver M S.carrier
      {b : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) H.target.tags) | mixedTuple b ∈ H.liftedCarrier} := by
  let := A.finiteTags
  have defImage := H.liftPoint_definable.image A.definable
  convert defImage using 1
  ext y
  change mixedTuple y ∈ H.liftedCarrier ↔ ∃ x : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) A.tags),
    mixedTuple x ∈ A.carrier ∧ H.liftPoint (mixedTuple x) = mixedTuple y
  rw [← H.liftPoint_image]
  constructor
  · rintro ⟨p,hp,he⟩
    obtain ⟨x,rfl⟩ := mixedTuple_surjective p
    exact ⟨x,hp,he⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨mixedTuple x,hx,he⟩

/-- The lifted family retains the selected leading term together
with the old head start. -/
@[expose] def liftedFamily : RetainedFieldFamily M S (n+1) (k+1) where
  tags := H.target.tags
  finiteTags := H.target.finiteTags
  select := H.target.select
  carrier := H.liftedCarrier
  definable := H.liftedCarrier_definable
  finiteFibers b v := (H.target.finiteFibers (b ∘ Fin.succ) v).subset fun _ h => ⟨h.1.1,h.2⟩

end HeadContractionData

end GeneralizedEuler.Section5
