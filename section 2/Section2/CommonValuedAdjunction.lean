module

public import Section2.CanonicalEmbedding
public import Section2.PrescribedValueComparison
public import Section2.WilkieRVStep

/-! The common field adjunction in Theorem 2.16, with the rank and
natural residue embeddings supplied by the cited T-convex results. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w} [Field E]
  {J K F : Type*} [Field J] [LinearOrder J] [IsStrictOrderedRing J] [L.Structure J]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  (I I' : ValuationSubring J) (O : ValuationSubring K) (Q : ValuationSubring F)
  [L.Structure (Residue I)] [L.Structure (Residue O)] [L.Structure (Residue Q)]
  (hO : IsOrderConvex O) (hQ : IsOrderConvex Q)
  (PI : E → RV0 I → RV0 I) (PI' : E → RV0 I' → RV0 I')
  (PO : E → RV0 O → RV0 O) (PQ : E → RV0 Q → RV0 Q)
  {W : Set (RV0 O)}
  (A : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) W)
  (B : L.Substructure K) (field : B ↪[L] F)
  (hbase : A.source.carrier .vf ⊆ B)
  (hfield : ∀ x : A.source.carrier .vf, field ⟨x.val, hbase x.property⟩ = A.embedding.toEmbedding .vf x)
  (rep : B → J)
  (p : J ↪ₑ[L] K) (q : J ↪ₑ[L] F)
  (hleft : ∀ x : B, p (rep x) = x.val) (hright : ∀ x : B, q (rep x) = field x)
  (f : J →+* K) (f' : J →+* F)
  (hp : ∀ x, p x = f x) (hq : ∀ x, q x = f' x)
  (hMono : StrictMono f) (hMono' : StrictMono f')
  (hpVal : RespectsValuationRing I O f) (hqVal : RespectsValuationRing I' Q f')
  (D : Subfield J)
  (hD : Set.range (fun c : A.source.carrier .vf => rep ⟨c.val, hbase c.property⟩) = (D : Set J))
  (g : E → PositiveField J →* PositiveField J)
  (gO : E → PositiveField K →* PositiveField K) (gQ : E → PositiveField F →* PositiveField F)
  (hPI : ∀ e, AgreesWithFieldPower I (g e) (PI e))
  (hPI' : ∀ e, AgreesWithFieldPower I' (g e) (PI' e))
  (hPO : ∀ e, AgreesWithFieldPower O (gO e) (PO e))
  (hPQ : ∀ e, AgreesWithFieldPower Q (gQ e) (PQ e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField J), I.valuation (x : J) = 1 → I.valuation (g e x : J) = 1)
  (hunit' : ∀ e (x : PositiveField J), I'.valuation (x : J) = 1 → I'.valuation (g e x : J) = 1)
  (hStable : ∀ e (x : PositiveField J), (x : J) ∈ D → (g e x : J) ∈ D)

include hfield hleft hright hp hq hMono hMono' hpVal hqVal hD hPI hPI' hPO hPQ
  hzero hone hadd hmul hunit hunit' hStable

/-- The two pulled-back rings coincide by the rank bound and the
old-value test. The induced residue embeddings and uniform power
graphs then give the canonical embeddings used by both rank cases. -/
theorem exists_fixedRVExtension_of_common_valued_adjunction {T : L.Theory}
    [T.IsUniversal] [Residue I ⊨ T] (hQE : EliminatesQuantifiers T)
    (minusOne : A.source.carrier .vf) (hminus : minusOne.val = -1)
    (hminus' : A.embedding.toEmbedding .vf minusOne = -1)
    (a : PositiveField J) (t : A.source.carrier .rv)
    (ht : t.val ∉ rv O '' A.source.carrier .vf)
    (ha : rv O (p a.val) = t.val) (hb : rv Q (q a.val) = A.embedding.toEmbedding .rv t)
    (hRank : RelativeValueRankLEOne I g hzero hone hadd hmul D hStable PI hPI hunit)
    (hRank' : RelativeValueRankLEOne I' g hzero hone hadd hmul D hStable PI' hPI' hunit')
    (hValue : I.valuation a.val ∈ I.valuation '' (D : Set J) →
      ∀ x : J, I.valuation x ∈ I.valuation '' (D : Set J))
    (hValue' : I'.valuation a.val ∈ I'.valuation '' (D : Set J) →
      ∀ x : J, I'.valuation x ∈ I'.valuation '' (D : Set J))
    (hResidue : I.valuation a.val ∉ I.valuation '' (D : Set J) →
      ∀ x : J, I.valuation x = 1 → rv I x ∈ rv I '' (D : Set J))
    (old : Set (Residue I)) (hold : ∀ r, r ∈ old ↔ residueRV I r ∈ rv I '' (D : Set J))
    (M : Matroid (Residue I)) (hFull : M.E = Set.univ)
    (hResRank : I.valuation a.val ∈ I.valuation '' (D : Set J) → M.eRk M.E ≤ 1)
    (hNonloop : ∀ r, r ∉ old → M.IsNonloop r)
    (hClosure : ∀ r x, x ∈ M.closure {r} → ∃ φ : L.Formula ((old ⊕ Unit) ⊕ Unit),
      ∀ y : Residue I, φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => r)) (fun _ => y)) ↔ y = x)
    (resO : Residue I ↪[L] Residue O) (hResO : ∀ r, resO r = mapResidue I O f hpVal r)
    (hResQ : ∀ h : RespectsValuationRing I Q f', ∃ resQ : Residue I ↪[L] Residue Q,
      ∀ r, resQ r = mapResidue I Q f' h r)
    (graph : E → L.Formula (Fin 2))
    (hGraph : ∀ e (v : Fin 2 → J), (graph e).Realize v ↔ totalFieldPower (g e) (v 0) = v 1)
    (hGraphO : ∀ e (v : Fin 2 → K), (graph e).Realize v ↔ totalFieldPower (gO e) (v 0) = v 1)
    (hGraphQ : ∀ e (v : Fin 2 → F), (graph e).Realize v ↔ totalFieldPower (gQ e) (v 0) = v 1)
    (hOff : ∀ e r, ¬IsPositiveRV I r → PI e r = 0)
    (hOffO : ∀ e r, ¬IsPositiveRV O r → PO e r = 0)
    (hOffQ : ∀ e r, ¬IsPositiveRV Q r → PQ e r = 0) :
    ∃ C : FixedRVLift (canonicalStructure (L := L) O hO PO) (canonicalStructure Q hQ PQ) W,
      A ≤ C ∧ C.source.carrier .vf = (B : Set K) ∧
        ∀ (x : B) (hx : x.val ∈ C.source.carrier .vf),
          C.embedding.toEmbedding .vf ⟨x.val, hx⟩ = field x := by
  let d (c : A.source.carrier .vf) := rep ⟨c.val, hbase c.property⟩
  have hLeft (c : A.source.carrier .vf) : f (d c) = c.val := (hp _).symm.trans (hleft _)
  have hRight (c : A.source.carrier .vf) : f' (d c) = A.embedding.toEmbedding .vf c :=
    (hq _).symm.trans ((hright _).trans (hfield c))
  have ha' : rv O (f a.val) = t.val := (congrArg (rv O) (hp _)).symm.trans ha
  have hb' : rv Q (f' a.val) = A.embedding.toEmbedding .rv t := (congrArg (rv Q) (hq _)).symm.trans hb
  have hOld := pulledValuations_agree_on_old_value O Q hO hQ PO PQ A.source A.embedding f f'
    I I' hpVal hqVal D d hD hLeft hRight a.val t ha' hb'
  have hBase := pulledValuations_agree_on_old_ring O Q hO hQ PO PQ A.source A.embedding f f'
    I I' hpVal hqVal D d hD hLeft hRight minusOne hminus hminus'
  have hI : IsOrderConvex I := by
    have he : I = O.comap f := by
      ext x
      exact (hpVal x).symm
    rw [he]
    exact convex_comap_valuationRing O f hO hMono.monotone
  have hI' : IsOrderConvex I' := by
    have he : I' = Q.comap f' := by
      ext x
      exact (hqVal x).symm
    rw [he]
    exact convex_comap_valuationRing Q f' hQ hMono'.monotone
  have hEq := eq_convexValuationRing_of_wilkie_value_cases I g hzero hone hadd hmul D hStable PI hPI hunit
    I' PI' hPI' hunit' hI hI' hBase hRank hRank' a hOld
    (fun h u => by obtain ⟨x, rfl⟩ := I.valuation_surjective u; exact hValue h x)
    (fun h u => by obtain ⟨x, rfl⟩ := I'.valuation_surjective u; exact hValue' h x)
  have hqVal' : RespectsValuationRing I Q f' := hEq.symm ▸ hqVal
  obtain ⟨resQ, hResQ⟩ := hResQ hqVal'
  obtain ⟨left, hL, _⟩ := exists_canonicalEmbedding_of_elementary_field I O hI hO PI PO p f hp hpVal
    hMono resO hResO g gO graph hGraph hGraphO hPI hPO hOff hOffO
  obtain ⟨right, hR, _⟩ := exists_canonicalEmbedding_of_elementary_field I Q hI hQ PI PQ q f' hq hqVal'
    hMono' resQ hResQ g gQ graph hGraph hGraphQ hPI hPQ hOff hOffQ
  exact exists_fixedRVExtension_of_wilkie_cases A left right B field hbase hfield rep
    (fun x => (hL _).trans (hleft x)) (fun x => (hR _).trans (hright x))
    D hD g hPI hzero hone hadd hmul hunit hStable hQE a t ht
    ((congrArg (rv O) (hL _)).trans ha) ((congrArg (rv Q) (hR _)).trans hb)
    hRank hValue hResidue old hold M hFull hResRank hNonloop hClosure

end GeneralizedEuler.Section2
