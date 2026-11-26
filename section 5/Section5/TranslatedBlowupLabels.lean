module

public import Section5.PositiveBlowupObject

/-! The new leading term produced by a focus translation is the
multiplier times the old leading term. This change of auxiliary
coordinates is definable over the original base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k m : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))
  (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (j : Fin (k+1))

local notation "𝓜" => canonicalStructure (L := L) O hO power

abbrev blowupOldIndices {a m : ℕ} (idx : Fin m ≃ Fin a ⊕ Fin 1) := idx.symm ∘ Sum.inl
abbrev blowupExtraIndex {a m : ℕ} (idx : Fin m ≃ Fin a ⊕ Fin 1) := idx.symm (Sum.inr 0)

@[expose] def translatedPositiveCarrier : Set (Fin m → RV0 O) :=
  {y | ∃ a : U.carrier, a.val = y ∘ blowupOldIndices idx ∧
    unsignedValue O (y (blowupExtraIndex idx)) < unsignedValue O (U.label a j) ∧
    y (blowupExtraIndex idx) ≠ 0}

private theorem pack_compose_old (a : Fin U.arity → RV0 O) (s : RV0 O) :
    (Sum.elim a (fun _ : Fin 1 => s) ∘ idx) ∘ blowupOldIndices idx = a := by
  funext i
  simp only [blowupOldIndices,Function.comp_apply,Equiv.apply_symm_apply,Sum.elim_inl]

private theorem pack_at_extra (a : Fin U.arity → RV0 O) (s : RV0 O) :
    (Sum.elim a (fun _ : Fin 1 => s) ∘ idx) (blowupExtraIndex idx) = s := by
  simp only [blowupExtraIndex,Function.comp_apply,Equiv.apply_symm_apply,Sum.elim_inr]

private theorem packed_ext (x y : Fin m → RV0 O)
    (h : x ∘ blowupOldIndices idx = y ∘ blowupOldIndices idx)
    (hs : x (blowupExtraIndex idx) = y (blowupExtraIndex idx)) : x = y := by
  funext i
  obtain ⟨d,rfl⟩ := idx.symm.surjective i
  cases d with
  | inl d => exact congrFun h d
  | inr d =>
    have he : d = 0 := Subsingleton.elim _ _
    subst d
    exact hs

def translatedPositiveEquiv :
    positiveBlowupCarrier O hO power S U idx ≃ translatedPositiveCarrier O hO power S U idx j := by
  let q := blowupExtraIndex idx
  let p := blowupOldIndices idx
  let A (x : positiveBlowupCarrier O hO power S U idx) : U.carrier :=
    ⟨x.val ∘ p,x.property.1⟩
  let f (x : positiveBlowupCarrier O hO power S U idx) :
      translatedPositiveCarrier O hO power S U idx j := by
    let a := A x
    let v := x.val q * U.label a j
    refine ⟨Sum.elim a.val (fun _ : Fin 1 => v) ∘ idx,a,?_,?_,?_⟩
    · exact (pack_compose_old O hO power S U idx a.val v).symm
    · rw [pack_at_extra]
      change unsignedValue O (x.val q * U.label a j) < _
      rw [map_mul (unsignedValue O)]
      have hpos : 0 < unsignedValue O (U.label a j) :=
        pos_iff_ne_zero.mpr ((map_ne_zero _).mpr (U.nonzero a j))
      exact mul_lt_of_lt_one_left hpos x.property.2.1
    · rw [pack_at_extra]
      exact mul_ne_zero x.property.2.2 (U.nonzero a j)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro x y eq
    have h : x.val ∘ p = y.val ∘ p := by
      have eq' := congrArg (fun w : translatedPositiveCarrier O hO power S U idx j => w.val ∘ p) eq
      exact (pack_compose_old O hO power S U idx (A x).val _).symm.trans
        (eq'.trans (pack_compose_old O hO power S U idx (A y).val _))
    have tag : A x = A y := Subtype.ext h
    have same := congrArg (fun w : translatedPositiveCarrier O hO power S U idx j => w.val q) eq
    change (Sum.elim (A x).val (fun _ : Fin 1 => x.val q * U.label (A x) j) ∘ idx) q =
      (Sum.elim (A y).val (fun _ : Fin 1 => y.val q * U.label (A y) j) ∘ idx) q at same
    rw [pack_at_extra,pack_at_extra,tag] at same
    let t : RV0 O := U.label (A y) j
    have ht : t ≠ 0 := U.nonzero _ j
    have hx : (x.val q * t) / t = x.val q := (div_eq_iff (G₀ := RV0 O) ht).2 rfl
    have hy : (x.val q * t) / t = y.val q := (div_eq_iff (G₀ := RV0 O) ht).2 same
    exact Subtype.ext (packed_ext O hO power S U idx x.val y.val h (hx.symm.trans hy))
  · rintro ⟨y,a,ha,hval,hn⟩
    let t : RV0 O := U.label a j
    let s : RV0 O := y q / t
    have ht : t ≠ 0 := U.nonzero a j
    have hpos : 0 < unsignedValue O t := pos_iff_ne_zero.mpr ((map_ne_zero _).mpr ht)
    have hs : unsignedValue O s < 1 := by
      change unsignedValue O (y q / t) < 1
      rw [show unsignedValue O (y q / t) = unsignedValue O (y q) / unsignedValue O t from
        map_div₀ (unsignedValue O) (y q) t,div_lt_one₀ hpos]
      exact hval
    let w := Sum.elim a.val (fun _ : Fin 1 => s) ∘ idx
    let x : positiveBlowupCarrier O hO power S U idx :=
      ⟨w,by
        change w ∘ p ∈ U.carrier ∧ unsignedValue O (w q) < 1 ∧ w q ≠ 0
        unfold w
        rw [pack_compose_old,pack_at_extra]
        exact ⟨a.property,hs,div_ne_zero (G₀ := RV0 O) hn ht⟩⟩
    have hA : A x = a := Subtype.ext (pack_compose_old O hO power S U idx a.val s)
    refine ⟨x,Subtype.ext (packed_ext O hO power S U idx (f x).val y ?_ ?_)⟩
    · change (Sum.elim (A x).val (fun _ : Fin 1 => x.val q * U.label (A x) j) ∘ idx) ∘ p = y ∘ p
      rw [pack_compose_old,hA]
      exact ha
    · change (Sum.elim (A x).val (fun _ : Fin 1 => x.val q * U.label (A x) j) ∘ idx) q = y q
      rw [pack_at_extra,hA]
      change (Sum.elim a.val (fun _ : Fin 1 => s) ∘ idx) q * t = y q
      rw [pack_at_extra]
      exact div_mul_cancel₀ (G₀ := RV0 O) _ ht

theorem translatedPositiveEquiv_apply (x : positiveBlowupCarrier O hO power S U idx) :
    let a : U.carrier := ⟨x.val ∘ blowupOldIndices idx,x.property.1⟩
    (translatedPositiveEquiv O hO power S U idx j x).val ∘ blowupOldIndices idx = a.val ∧
      (translatedPositiveEquiv O hO power S U idx j x).val (blowupExtraIndex idx) =
        x.val (blowupExtraIndex idx) * U.label a j := by
  intro a
  exact ⟨pack_compose_old O hO power S U idx a.val _,pack_at_extra O hO power S U idx a.val _⟩

/-- The raw translated label and the elementary multiplier give
definably isomorphic positive-degree carriers. -/
theorem translatedPositiveEquiv_definable (hneg : rv O (-1) ∈ S.carrier .rv) :
    SortedDefinableOver 𝓜 S.carrier (rvGraph (fun x =>
      (translatedPositiveEquiv O hO power S U idx j x).val)) := by
  let V := RVVariables (Fin m ⊕ Fin m)
  let W := SumVariables V (RVVariables (Fin (k+1)))
  let p := blowupOldIndices idx
  let q := blowupExtraIndex idx
  let rename : ∀ s, RVVariables (Fin U.arity ⊕ Fin (k+1)) s → W s
    | .vf => PEmpty.elim
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl ∘ p) Sum.inr
  have tag := U.graph.pullback_relabel rename
  let args := WithBase S.carrier W
  let product : SortedTerm L E args .rv :=
    rvMulTerm (.var (.inr (.inl (.inl q)))) (.var (.inr (.inr j)))
  have mult := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inl (.inr q)) product
  have raw := definable_project_mixed (tag.inter mult)
  have keep := SortedDefinableOver.iInter (fun i : Fin U.arity =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := V)
      .rv (.inl (p i)) (.inr (p i)))
  let renameIn : ∀ s, RVVariables (Fin m) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  have source := (positiveBlowupCarrier_definable O hO power S U idx hneg).pullback_relabel renameIn
  convert source.inter (keep.inter raw) using 1
  ext w
  let x := w .rv ∘ Sum.inl
  let y := w .rv ∘ Sum.inr
  have test (t : SortedAssignment (CanonicalSort O) (RVVariables (Fin (k+1)))) :
      product.realize 𝓜 (fun s => Sum.elim Subtype.val (Sum.elim (w s) (t s))) =
        x q * t .rv j := by
    dsimp only [product]
    rw [realize_rvMulTerm O hO power]
    rfl
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter]
  change (∃ a : positiveBlowupCarrier O hO power S U idx, a.val = x ∧
      (translatedPositiveEquiv O hO power S U idx j a).val = y) ↔
    x ∈ positiveBlowupCarrier O hO power S U idx ∧
      (∀ i : Fin U.arity, x (p i) = y (p i)) ∧
      ∃ t : SortedAssignment (CanonicalSort O) (RVVariables (Fin (k+1))),
        (∃ a : U.carrier, a.val = x ∘ p ∧ U.label a = t .rv) ∧
        y q = product.realize 𝓜 (fun s => Sum.elim Subtype.val (Sum.elim (w s) (t s)))
  simp only [test]
  constructor
  · rintro ⟨a,ha,hy⟩
    have hm := translatedPositiveEquiv_apply O hO power S U idx j a
    let b : U.carrier := ⟨a.val ∘ p,a.property.1⟩
    refine ⟨ha ▸ a.property,fun i => ?_,rvTupleAssignment (U.label b),⟨b,congrArg (· ∘ p) ha,rfl⟩,?_⟩
    · exact (congrFun ha (p i)).symm.trans ((congrFun hm.1 i).symm.trans (congrFun hy (p i)))
    · exact (congrFun hy q).symm.trans (hm.2.trans (congrArg (· * U.label b j) (congrFun ha q)))
  · rintro ⟨hx,hkeep,t,⟨b,hb,ht⟩,hm⟩
    let a : positiveBlowupCarrier O hO power S U idx := ⟨x,hx⟩
    have he : (⟨a.val ∘ p,a.property.1⟩ : U.carrier) = b := Subtype.ext hb.symm
    have ap := translatedPositiveEquiv_apply O hO power S U idx j a
    refine ⟨a,rfl,packed_ext O hO power S U idx _ y (ap.1.trans (funext hkeep)) ?_⟩
    change (translatedPositiveEquiv O hO power S U idx j a).val q = y q
    rw [ap.2,he,ht]
    exact hm.symm

end GeneralizedEuler.Section5
