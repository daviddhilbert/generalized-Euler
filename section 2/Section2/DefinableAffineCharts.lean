module

public import Section2.RVMonomials
public import Section2.RVDefinableEquivalence
public import Mathlib.Data.Set.Lattice.Disjoint

/-! Definable affine charts in RV and their tagged disjoint union. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a

section MonomialChart

variable {L : Language.{u, v}} {E : Type w} {K : Type z}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O)
  {A : ∀ s, Set (CanonicalSort O s)} {I : Type} {n m : ℕ}

@[expose]
def rvAffineMonomial (coeff : Fin n → Fin m → E) (u : Fin n → RV0 O)
    (t : Fin m → RV0 O) (i : Fin n) : RV0 O :=
  u i * (((Finset.univ : Finset (Fin m)).toList).map
    (fun j => P (coeff i j) (t j))).prod

/-- Divide the omitted coordinates by their monomial lifts and retain
the selected coordinates. -/
@[expose]
def affineChartTuple (selected : Fin m → I) (omitted : Fin n → I)
    (coeff : Fin n → Fin m → E) (u : Fin n → RV0 O)
    (x : I → RV0 O) : Fin n ⊕ Fin m → RV0 O :=
  Sum.elim (fun i => x (omitted i) / rvAffineMonomial O P coeff u (x ∘ selected) i)
    (fun j => x (selected j))

theorem definable_affineChartTuple_graph (D : Set (I → RV0 O))
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      {a : ∀ s, RVVariables I s → CanonicalSort O s | a .rv ∈ D})
    (selected : Fin m → I) (omitted : Fin n → I) (coeff : Fin n → Fin m → E) (u : Fin n → A .rv) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      (rvGraph (fun x : D => affineChartTuple O P selected omitted coeff (fun i => (u i).val) x.val)) := by
  let M := canonicalStructure (L := L) O hO P
  let Var := RVVariables (I ⊕ (Fin n ⊕ Fin m))
  let rename : ∀ s, RVVariables I s → Var s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let domain : Set (∀ s, Var s → CanonicalSort O s) := {a | (a .rv ∘ Sum.inl) ∈ D}
  let select (j : Fin m) : Set (∀ s, Var s → CanonicalSort O s) :=
    {a | a .rv (.inr (.inr j)) = a .rv (.inl (selected j))}
  let divide (i : Fin n) : Set (∀ s, Var s → CanonicalSort O s) :=
    {a | a .rv (.inr (.inl i)) = a .rv (.inl (omitted i)) /
      ((u i).val * (((Finset.univ : Finset (Fin m)).toList).map
        (fun j => P (coeff i j) (a .rv (.inl (selected j))))).prod)}
  have hDom : SortedDefinableOver M A domain := hD.pullback_relabel rename
  have hSelect (j : Fin m) : SortedDefinableOver M A (select j) :=
    SortedDefinableOver.coordinate_eq (M := M) (A := A) (Var := Var) .rv
      (.inr (.inr j)) (.inl (selected j))
  have hDivide (i : Fin n) : SortedDefinableOver M A (divide i) :=
    definable_affine_division_coordinate (L := L) (Var := Var) O hO P
      (Finset.univ : Finset (Fin m)).toList (coeff i) (fun j => .inl (selected j))
      (u i) (.inl (omitted i)) (.inr (.inl i))
  have h := (hDom.inter (SortedDefinableOver.iInter hSelect)).inter (SortedDefinableOver.iInter hDivide)
  convert h using 1
  ext a
  simp only [rvGraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, domain, select, divide]
  constructor
  · rintro ⟨x, hx, he⟩
    have h (i : Fin n) := (congrFun he (.inl i)).symm
    have hk (j : Fin m) := (congrFun he (.inr j)).symm
    have hd : a .rv ∘ Sum.inl ∈ D := hx ▸ x.property
    refine ⟨⟨hd, fun j => ?_⟩, fun i => ?_⟩
    · change a .rv (.inr (.inr j)) = _
      simpa only [affineChartTuple, Sum.elim_inr, hx, Function.comp_apply] using hk j
    · change a .rv (.inr (.inl i)) = _
      simpa only [affineChartTuple, rvAffineMonomial, Sum.elim_inl, hx, Function.comp_apply] using h i
  · rintro ⟨⟨hd, hk⟩, h⟩
    refine ⟨⟨a .rv ∘ Sum.inl, hd⟩, rfl, ?_⟩
    funext i
    cases i with
    | inl j => exact (h j).symm
    | inr j => exact (hk j).symm

end MonomialChart

section TaggedUnion

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X} {A : ∀ s, Set (X s)}
  {I J : Type a} {l : ℕ}

/-- A finite disjoint union of RV sets with one extra label coordinate. -/
@[expose]
def taggedRVUnion (pieces : Fin l → Set (J → X .rv)) (tag : Fin l ↪ X .rv) :
    Set (J ⊕ Unit → X .rv) :=
  {x | ∃ j, x ∘ Sum.inl ∈ pieces j ∧ x (.inr ()) = tag j}

private def taggedRVUnionEquiv (pieces : Fin l → Set (J → X .rv)) (tag : Fin l ↪ X .rv) :
    (Σ j, pieces j) ≃ taggedRVUnion pieces tag := by
  let f (x : Σ j, pieces j) : taggedRVUnion pieces tag :=
    ⟨Sum.elim x.2.val (fun _ => tag x.1), x.1, x.2.property, rfl⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have ht : i = j := tag.injective (congrFun (congrArg Subtype.val h) (.inr ()))
    subst j
    congr 1
    exact Subtype.ext (funext fun k => congrFun (congrArg Subtype.val h) (.inl k))
  · intro y
    obtain ⟨i, hi, ht⟩ := y.property
    refine ⟨⟨i, ⟨y.val ∘ Sum.inl, hi⟩⟩, Subtype.ext (funext fun j => ?_)⟩
    cases j with
    | inl j => rfl
    | inr j => cases j; exact ht.symm

/-- Finite definable chart bijections assemble into a definable
bijection with the tagged union of their ranges. -/
theorem rvDefinablyEquivalent_tagged_union (source : Fin l → Set (I → X .rv))
    (target : Fin l → Set (J → X .rv)) (tag : Fin l ↪ X .rv) (htag : ∀ j, tag j ∈ A .rv)
    (hdisj : Pairwise (fun i j => Disjoint (source i) (source j)))
    (h : ∀ j, RVDefinablyEquivalent M A (source j) (target j)) :
    RVDefinablyEquivalent M A (⋃ j, source j) (taggedRVUnion target tag) := by
  classical
  choose e he using h
  let split := Set.unionEqSigmaOfDisjoint hdisj
  let combine := taggedRVUnionEquiv target tag
  let bij : (⋃ j, source j) ≃ taggedRVUnion target tag :=
    split.trans ((Equiv.sigmaCongrRight e).trans combine)
  refine ⟨bij, ?_⟩
  let Var := RVVariables (I ⊕ (J ⊕ Unit))
  let rename : ∀ s, RVVariables (I ⊕ J) s → Var s
    | .vf => PEmpty.elim
    | .rv => Sum.map id Sum.inl
  let chart (j : Fin l) : Set (∀ s, Var s → X s) :=
    ((fun a : ∀ s, Var s → X s => fun s => a s ∘ rename s) ⁻¹'
      rvGraph (fun x : source j => (e j x).val)) ∩
      {a | a .rv (.inr (.inr ())) = tag j}
  have hc (j : Fin l) : SortedDefinableOver M A (chart j) :=
    ((he j).pullback_relabel rename).inter
      (SortedDefinableOver.coordinate_eq_parameter (M := M) (A := A) (Var := Var) .rv
        (.inr (.inr ())) ⟨tag j, htag j⟩)
  have hcdef := SortedDefinableOver.iUnion hc
  have hpack (x : (⋃ j, source j)) (k : J ⊕ Unit) :
      (bij x).val k = Sum.elim (e (split x).1 (split x).2).val (fun _ => tag (split x).1) k := rfl
  convert hcdef using 1
  ext a
  simp only [rvGraph, Set.mem_ofPred_eq, Set.mem_iUnion, chart, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, hb⟩
    refine ⟨(split x).1, ⟨(split x).2, ?_, ?_⟩, ?_⟩
    · exact (Set.coe_snd_unionEqSigmaOfDisjoint hdisj x).trans hx
    · funext j
      exact (hpack x (.inl j)).symm.trans (congrFun hb (.inl j))
    · exact (congrFun hb (.inr ())).symm.trans (hpack x (.inr ()))
  · rintro ⟨j, ⟨x, hx, heq⟩, ht⟩
    let t : (⋃ j, source j) := split.symm ⟨j, x⟩
    refine ⟨t, hx, ?_⟩
    have hs : split t = ⟨j, x⟩ := split.apply_symm_apply _
    funext k
    rw [hpack, hs]
    cases k with
    | inl k => exact congrFun heq k
    | inr k => cases k; exact ht.symm

end TaggedUnion

end GeneralizedEuler.Section2
