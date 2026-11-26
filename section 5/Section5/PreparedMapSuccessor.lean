module

public import Section5.SuccessorTags
public import Section5.UnaryLifting
public import Section5.FinitePreparationFibers

/-! The proof of the field-arity successor step for a definable
preparation with a full image and all tests contractible. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder UnaryPreparation

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ} {I J R : Type}

variable (P : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) k))
  (first : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) R)

@[expose] def transportedTailTest (G : PointTests O (n+1) I J) :
    PointTests O n (R ⊕ HistoryIndex k) J :=
  {q | ∃ p, mapKeepingTags first p = q.1 ∧ (p,q.2) ∈ descendedTest O P G}

theorem transportedTailTest_definable [Finite I]
    {G : PointTests O (n+1) I J} (hG : PointTestsDefinable M S (descendedTest O P G))
    (hfirst : PointMapDefinable M S first) :
    PointTestsDefinable M S (transportedTailTest P first G) :=
  PointTestsDefinable.transport hfirst.keepTags hG

private theorem complete_label_fibers {X Q : Type*} (q : X → Q) (A : Set X)
    (h : ∀ x y, q x = q y → (x ∈ A ↔ y ∈ A)) :
    A = q ⁻¹' (q '' A) := by
  ext x
  exact ⟨fun hx => ⟨x,hx,rfl⟩, fun ⟨y,hy,he⟩ => (h y x he).1 hy⟩

-- The test for the full original ambient domain ensures that the
-- relative final image is still a pullback after both tail maps.
set_option maxHeartbeats 1100000 in
/-- Assemble the successor preparation from the two smaller-arity
preparations and the uniform head graph. -/
@[expose] def PreparedMap.successor [Finite I] [Finite R]
    (G : PointTests O (n+1) I J)
    (firstDef : PointMapDefinable M S first) (firstInj : Function.Injective first)
    (firstFinite : FiniteFieldPreimages first)
    (oldIndex : I ↪ R) (oldAux : ∀ p i, (first p).2 (oldIndex i) = p.2 i)
    (headGraph : PointMapDefinable M S (headMap (I := I) P))
    (headFinite : FiniteFieldPreimages (headMap (I := I) P))
    (historyIndex : HistoryIndex k)
    (hLead : ∀ b t, (P b).lead t = encodeHistory O k t historyIndex)
    (hG : ∀ b x y ξ t, (P b).label x = (P b).label y →
      (((Fin.cons x b, ξ),t) ∈ G ↔ ((Fin.cons y b, ξ),t) ∈ G))
    (last : PreparedMap M S
      (flagTests (transportedTailTest P first (Set.univ : PointTests O (n+1) I J))
        (transportedTailTest P first G))) :
    PreparedMap M S G := by
  letI := last.finiteTags
  let f := liftTailMap last.map ∘
    liftTailMap (mapKeepingTags (H := HistoryIndex k) first) ∘ headMap (I := I) P
  let lastTail := last.map ∘ (packHistory (O := O) (n := n) (I := R) (k := k))
  let vmap := verticalSuccessorMap (P ∘ Prod.fst) first lastTail
  have join_commutes (p : PreparationPoint O (Fin n) I × K) : f (joinHead p) = joinHead (vmap p) := rfl
  have hinj : Function.Injective f := by
    intro p q he
    let a := (tailPoint p, p.1 0)
    let b := (tailPoint q, q.1 0)
    have ha : joinHead a = p := joinHead_separate p
    have hb : joinHead b = q := joinHead_separate q
    have he' : joinHead (vmap a) = joinHead (vmap b) := by
      simpa only [← join_commutes, ha, hb] using he
    have hs : a = b := verticalSuccessorMap_injective (P ∘ Prod.fst) first lastTail
      firstInj (last.injective.comp packHistory.injective) (joinHead_injective he')
    exact ha.symm.trans ((congrArg joinHead hs).trans hb)

  let htag := last.oldIndex (.inr historyIndex)
  let tailLabel := preparationLabel (O := O) (F := Fin n) (R := last.tags)
  let headLead (q : (Fin n → RV0 O) × (last.tags → RV0 O)) := q.2 htag
  have fixedHead (b : PreparationPoint O (Fin n) I) (t : PreparationLabels O (RV0 O) k) :
      headLead (tailLabel (lastTail (first b,t))) = (P b.1).lead t := by
    have h := last.oldAux (packHistory (first b,t)) (.inr historyIndex)
    exact h.trans (hLead b.1 t).symm

  let select (b : Bool) : PointTests O (n+1) I J := if b then G else Set.univ
  let flag (b : Bool) (s : J → RV0 O) : Option J → RV0 O :=
    fun i => i.elim (if b then 1 else 0) s
  have hflag (b : Bool) (s : J → RV0 O) :
      {p | (p,flag b s) ∈ flagTests (transportedTailTest P first (Set.univ : PointTests O (n+1) I J))
          (transportedTailTest P first G)} =
        {p | (p,s) ∈ transportedTailTest P first (select b)} := by
    ext p
    have hOne : (1 : RV0 O) ≠ 0 := by
      rw [← map_one (rv O)]
      exact (rv_eq_zero_iff O).not.mpr one_ne_zero
    cases b <;> simp [flag, select, flagTests, Function.comp_def, hOne]
  have htests (b : Bool) (s : J → RV0 O) :
      ∀ a c, tailLabel a = tailLabel c →
        (a ∈ last.map '' {p | (p,s) ∈ transportedTailTest P first (select b)} ↔
          c ∈ last.map '' {p | (p,s) ∈ transportedTailTest P first (select b)}) := by
    intro a c heq
    rw [← hflag]
    exact last.test_image_whole (flag b s) heq

  let original (b : Bool) : Set (PreparationPoint O (Fin n) I × K × (J → RV0 O)) :=
    {p | (joinHead (p.1,p.2.1), p.2.2) ∈ select b}
  let imageLabels (b : Bool) (s : J → RV0 O) :=
    tailLabel '' (last.map '' {p | (p,s) ∈ transportedTailTest P first (select b)})
  have htail (b : Bool) (s : J → RV0 O) :
      lastTail '' succeededTailTest (P ∘ Prod.fst) first (original b) s =
        tailLabel ⁻¹' imageLabels b s := by
    have hpacked := image_succeededTailTest P first (select b) s
    change packHistory '' succeededTailTest (P ∘ Prod.fst) first (original b) s =
      {p | (p,s) ∈ transportedTailTest P first (select b)} at hpacked
    change (last.map ∘ packHistory) '' succeededTailTest (P ∘ Prod.fst) first (original b) s = _
    calc
      _ = last.map '' (packHistory '' succeededTailTest (P ∘ Prod.fst) first (original b) s) := by
        simp only [Set.image_image, Function.comp_def]
      _ = _ := by
        rw [hpacked]
        exact complete_label_fibers tailLabel _ (htests b s)
  have hconst (b : Bool) : ∀ p x y s, ((P ∘ Prod.fst) p).label x = ((P ∘ Prod.fst) p).label y →
      ((p,x,s) ∈ original b ↔ (p,y,s) ∈ original b) := by
    intro p x y s he
    cases b
    · exact Iff.rfl
    · exact hG p.1 x y p.2 s he
  have himage (b : Bool) (s : J → RV0 O) :
      vmap '' {p | (p.1,p.2,s) ∈ original b} =
        {q | tailLabel q.1 ∈ imageLabels b s ∧ rv O q.2 = headLead (tailLabel q.1)} :=
    verticalSuccessor_pullback (P ∘ Prod.fst) first lastTail tailLabel (original b)
      (hconst b) headLead fixedHead (imageLabels b) (htail b) s
  have himage' (b : Bool) (s : J → RV0 O) (q : PreparationPoint O (Fin (n+1)) last.tags) :
      q ∈ f '' {p | (p,s) ∈ select b} ↔
        tailLabel (tailPoint q) ∈ imageLabels b s ∧
          rv O (q.1 0) = headLead (tailLabel (tailPoint q)) := by
    have he :
        (tailPoint q, q.1 0) ∈ vmap '' {p | (p.1,p.2,s) ∈ original b} ↔
        tailLabel (tailPoint q) ∈ imageLabels b s ∧
          rv O (q.1 0) = headLead (tailLabel (tailPoint q)) :=
      Set.ext_iff.mp (himage b s) _
    refine Iff.trans ?_ he
    constructor
    · rintro ⟨p,hp,hq⟩
      let r := (tailPoint p,p.1 0)
      have hr : joinHead r = p := joinHead_separate p
      have he : joinHead (vmap r) = joinHead (tailPoint q,q.1 0) :=
        (join_commutes r).symm.trans ((congrArg f hr).trans (hq.trans (joinHead_separate q).symm))
      have hm : (joinHead r,s) ∈ select b := by rwa [hr]
      exact ⟨r, hm, joinHead_injective he⟩
    · rintro ⟨r,hr,hq⟩
      exact ⟨joinHead r,hr,(join_commutes r).trans ((congrArg joinHead hq).trans (joinHead_separate q))⟩

  have same (u v : PreparationPoint O (Fin (n+1)) last.tags) (he : preparationLabel u = preparationLabel v) :
      tailLabel (tailPoint u) = tailLabel (tailPoint v) ∧ rv O (u.1 0) = rv O (v.1 0) := by
    obtain ⟨hVF,hRV⟩ := Prod.mk.inj he
    refine ⟨Prod.ext ?_ hRV, congrFun hVF 0⟩
    funext i
    exact congrFun hVF i.succ

  refine ⟨last.tags,last.finiteTags,oldIndex.trans (Function.Embedding.inl.trans last.oldIndex),
    f,hinj,(headGraph.comp firstDef.keepTags.liftTail).comp last.definable.liftTail,?_,?_,?_,
    (headFinite.comp firstFinite.keepTags.liftTail).comp last.finiteFieldPreimages.liftTail⟩
  · intro p i
    exact (last.oldAux _ (.inl (oldIndex i))).trans (oldAux (tailPoint p) i)
  · intro u v he
    let s : J → RV0 O := fun _ => 0
    have hu := himage' false s u
    have hv := himage' false s v
    change u ∈ f '' Set.univ ↔ _ at hu
    change v ∈ f '' Set.univ ↔ _ at hv
    rw [Set.image_univ] at hu hv
    rw [hu,hv,(same u v he).1,(same u v he).2]
  · intro p q he s
    have mem (x : PreparationPoint O (Fin (n+1)) I) :
        (x,s) ∈ G ↔ f x ∈ f '' {p | (p,s) ∈ select true} := by
      constructor
      · intro hx
        exact ⟨x,hx,rfl⟩
      · rintro ⟨y,hy,hyx⟩
        exact (hinj hyx) ▸ hy
    rw [mem p,mem q,himage' true,himage' true,(same _ _ he).1,(same _ _ he).2]

end GeneralizedEuler.Section5
