module

public import Section4.RVProducts
public import Section4.ValueFactorMap
public import Section4.PositivePresentations
import all Section4.Scissors

/-! Cartesian products of actual RV objects, with the field degree added
and the two structure maps concatenated. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k l : ℕ}

namespace RVObject

variable (U : RVObject M S k) (V : RVObject M S l)

@[expose] def productCarrier : Set (Fin (U.arity + V.arity) → X .rv) :=
  {w | w ∘ finSumFinEquiv ∘ Sum.inl ∈ U.carrier ∧
    w ∘ finSumFinEquiv ∘ Sum.inr ∈ V.carrier}

@[expose] def productLeft (x : productCarrier U V) : U.carrier :=
  ⟨x.val ∘ finSumFinEquiv ∘ Sum.inl,x.property.1⟩

@[expose] def productRight (x : productCarrier U V) : V.carrier :=
  ⟨x.val ∘ finSumFinEquiv ∘ Sum.inr,x.property.2⟩

@[expose] def productLabel (x : productCarrier U V) : Fin (k+l) → X .rv :=
  Sum.elim (U.label (productLeft U V x)) (V.label (productRight U V x)) ∘
    finSumFinEquiv.symm

theorem productCarrier_definable : isRVSet M S (productCarrier U V) :=
  (isRVSet_precomp (finSumFinEquiv ∘ Sum.inl) U.definable).inter
    (isRVSet_precomp (finSumFinEquiv ∘ Sum.inr) V.definable)

theorem productLabel_definable :
    SortedDefinableOver M S.carrier (rvGraph (productLabel U V)) := by
  let p : Fin U.arity → Fin (U.arity + V.arity) := finSumFinEquiv ∘ Sum.inl
  let q : Fin V.arity → Fin (U.arity + V.arity) := finSumFinEquiv ∘ Sum.inr
  let i : Fin k → Fin (k+l) := finSumFinEquiv ∘ Sum.inl
  let j : Fin l → Fin (k+l) := finSumFinEquiv ∘ Sum.inr
  have left : isRVSet M S
      {w : Fin (U.arity + V.arity) ⊕ Fin (k+l) → X .rv |
        ∃ u : U.carrier, u.val = w ∘ Sum.inl ∘ p ∧ U.label u = w ∘ Sum.inr ∘ i} :=
    isRVSet_precomp (Sum.map p i)
      (show isRVSet M S {w | ∃ u : U.carrier, u.val = w ∘ Sum.inl ∧ U.label u = w ∘ Sum.inr}
        from U.graph)
  have right : isRVSet M S
      {w : Fin (U.arity + V.arity) ⊕ Fin (k+l) → X .rv |
        ∃ v : V.carrier, v.val = w ∘ Sum.inl ∘ q ∧ V.label v = w ∘ Sum.inr ∘ j} :=
    isRVSet_precomp (Sum.map q j)
      (show isRVSet M S {w | ∃ v : V.carrier, v.val = w ∘ Sum.inl ∧ V.label v = w ∘ Sum.inr}
        from V.graph)
  convert left.inter right using 1
  ext w
  change (∃ x : productCarrier U V, x.val = w .rv ∘ Sum.inl ∧
    productLabel U V x = w .rv ∘ Sum.inr) ↔
    (∃ u : U.carrier, u.val = w .rv ∘ Sum.inl ∘ p ∧ U.label u = w .rv ∘ Sum.inr ∘ i) ∧
    (∃ v : V.carrier, v.val = w .rv ∘ Sum.inl ∘ q ∧ V.label v = w .rv ∘ Sum.inr ∘ j)
  constructor
  · rintro ⟨x,hx,hy⟩
    refine ⟨⟨productLeft U V x,congrArg (· ∘ p) hx,?_⟩,
      ⟨productRight U V x,congrArg (· ∘ q) hx,?_⟩⟩
    · funext d
      simpa only [productLabel,i,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
        using congrFun hy (i d)
    · funext d
      simpa only [productLabel,j,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
        using congrFun hy (j d)
  · rintro ⟨⟨u,hu,hl⟩,v,hv,hr⟩
    let x : productCarrier U V := ⟨w .rv ∘ Sum.inl, hu ▸ u.property,hv ▸ v.property⟩
    have eu : productLeft U V x = u := Subtype.ext hu.symm
    have ev : productRight U V x = v := Subtype.ext hv.symm
    refine ⟨x,rfl,?_⟩
    funext d
    obtain ⟨d,rfl⟩ := finSumFinEquiv.surjective d
    rw [productLabel,Function.comp_apply,Equiv.symm_apply_apply,eu,ev]
    cases d with
    | inl d => exact congrFun hl d
    | inr d => exact congrFun hr d

@[expose] def cartesianProduct : RVObject M S (k+l) where
  arity := U.arity + V.arity
  carrier := productCarrier U V
  definable := productCarrier_definable U V
  label := productLabel U V
  graph := productLabel_definable U V
  nonzero x d := by
    obtain ⟨d,rfl⟩ := finSumFinEquiv.surjective d
    rw [productLabel,Function.comp_apply,Equiv.symm_apply_apply]
    cases d with
    | inl i => exact U.nonzero _ i
    | inr j => exact V.nonzero _ j
  finiteFibers t := by
    let left := U.label ⁻¹' {t ∘ finSumFinEquiv ∘ Sum.inl}
    let right := V.label ⁻¹' {t ∘ finSumFinEquiv ∘ Sum.inr}
    let pair (x : productCarrier U V) := (productLeft U V x, productRight U V x)
    apply ((U.finiteFibers _).prod (V.finiteFibers _) : (left ×ˢ right).Finite).of_injOn (f := pair)
    · intro x hx
      change productLabel U V x = t at hx
      change U.label (productLeft U V x) = _ ∧ V.label (productRight U V x) = _
      constructor
      · funext i
        simpa only [productLabel,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
          using congrFun hx (finSumFinEquiv (.inl i))
      · funext j
        simpa only [productLabel,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
          using congrFun hx (finSumFinEquiv (.inr j))
    · intro x _ y _ eq
      apply Subtype.ext
      funext d
      obtain ⟨d,rfl⟩ := finSumFinEquiv.surjective d
      cases d with
      | inl i => exact congrFun (congrArg (fun w => w.1.val) eq) i
      | inr j => exact congrFun (congrArg (fun w => w.2.val) eq) j

theorem cartesianProduct_class :
    objectClass M S ⟨k+l,cartesianProduct U V⟩ =
      objectClass M S ⟨k,U⟩ * objectClass M S ⟨l,V⟩ := by
  unfold objectClass
  rw [← map_mul]
  apply scissors_sound M S
  apply RVRelation.prod
  exact rv_reindex_equivalent M S finSumFinEquiv.symm _
    (rv_product_definable U.definable V.definable)

end RVObject

end GeneralizedEuler.Section5
