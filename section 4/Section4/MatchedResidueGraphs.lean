module

public import Section4.IndependentRectangleMatches
public import Section4.OldValuePair
public import Section4.RVParameterSlices
import all Section4.IndependentRectangleMatches
import all Section4.WholeMatchRectangles
import all Section4.RectangleMatchGraph
import all Section4.MixedMatchFactors
import all Section4.RectangleFiberFamilies
import all Section4.RepresentedFiberMatches
import all Section4.NormalRectangles
import all Section4.ResidueWeights
import all Section4.DefinableResidueMatrices
import all Section4.CanonicalChartMaps
import all Section4.SignedShears
import all Section4.FiniteScissors
import all Section2.RVSplitCoordinates

/-! Recover a matched residue graph as an actual fixed-base RV set by
specializing the free coordinates at one old pair in its value cell. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k l : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S l)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

def residueGraphCode {m n : ℕ} (R : Set ((Fin m → Residue O) × (Fin n → Residue O))) :
    Set (Fin m ⊕ Fin n → RV0 O) :=
  {z | ∃ u w, (u,w) ∈ R ∧ residueRV O ∘ u = z ∘ Sum.inl ∧ residueRV O ∘ w = z ∘ Sum.inr}

include hv hs in
theorem matched_residues_in_units (i : I) (j : H) (a b u w)
    (h : ((a,b),u,w) ∈ labelMatching c pull (linearValueSection v hv s hs) d f i j) :
    (∃ l ∈ (c i).units, kernelResidue v ∘ l = u) ∧ (∃ r ∈ (d j).units, kernelResidue v ∘ r = w) := by
  obtain ⟨hx,hy,_⟩ := (RVFamily.mem_representedMatches _ _ _ _ _ _ _).mp h
  obtain ⟨l,hl,el⟩ := hx.1
  obtain ⟨r,hr,er⟩ := hy.1
  exact ⟨⟨l,hl,funext fun t => residueRV_injective O ((residueRV_kernel hv s hs _).trans (congrFun el t))⟩,
    ⟨r,hr,funext fun t => residueRV_injective O ((residueRV_kernel hv s hs _).trans (congrFun er t))⟩⟩

include hv hs in
theorem matched_values_in_domains (i : I) (j : H) (a b u w)
    (h : ((a,b),u,w) ∈ labelMatching c pull (linearValueSection v hv s hs) d f i j) :
    (Additive.ofMul ∘ a) ∈ (c i).values ∧ (Additive.ofMul ∘ b) ∈ (d j).values := by
  obtain ⟨hx,hy,_⟩ := (RVFamily.mem_representedMatches _ _ _ _ _ _ _).mp h
  have read {r} (D : Set (Fin r → Additive O.ValueGroupˣ)) (z : Fin r → O.ValueGroupˣ)
      (hz : (linearValueSection v hv s hs).representative ∘ z ∈ positiveSharp O v D) :
      Additive.ofMul ∘ z ∈ D := by
    obtain ⟨x,hx,e⟩ := hz
    have eq : x = s ∘ Additive.ofMul ∘ z := codeTuple_injective O e
    have values : v ∘ x = Additive.ofMul ∘ z := by rw [eq]; exact funext fun t => DFunLike.congr_fun hs _
    exact values ▸ hx
  exact ⟨read _ _ hx.2,read _ _ hy.2⟩

variable (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j))
  (old : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (rep : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)

include graph old rep witness in
theorem residue_match_definable (i : I) (j : H)
    {D : Set ((Fin (c i).r → Additive O.ValueGroupˣ) × (Fin (d j).r → Additive O.ValueGroupˣ))}
    (hd : (G : Set _).Definable JG (pairedSet D)) (ne : D.Nonempty)
    (R : Set ((Fin (c i).m → Residue O) × (Fin (d j).m → Residue O)))
    (slice : ∀ a b, (a,b) ∈ D → ∀ u w, (u,w) ∈ R ↔ ((a,b),u,w) ∈
      labelMatching c pull (linearValueSection v hv s hs) d f i j) :
    isRVSet _ S (residueGraphCode R) := by
  let sec := linearValueSection v hv s hs
  obtain ⟨a,b,hab,ha,hb⟩ := old_value_pair v hv s hs S G pull old witness hd ne
  let E := Fin (c i).m ⊕ Fin (d j).m
  let V := Fin (c i).r ⊕ Fin (d j).r
  let reindex : (Fin (c i).m ⊕ Fin (c i).r) ⊕ (Fin (d j).m ⊕ Fin (d j).r) → E ⊕ V :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
  let t : V → RV0 O := Sum.elim (sec.representative ∘ a) (sec.representative ∘ b)
  have ht : ∀ j, t j ∈ S.carrier .rv := Sum.rec (fun n => rep ⟨_,ha n⟩) (fun n => rep ⟨_,hb n⟩)
  let M := RVFamily.representedMatches (rvFamily c pull) (rvFamily d pull)
    (a := pointLabel c pull) (b := pointLabel d pull) f i j
  have test := rv_slice_at_base (isRVSet_precomp reindex (whole_graph_definable c pull d f graph i j)) t ht
  convert test using 1
  ext z
  let x := Sum.elim (z ∘ Sum.inl) (sec.representative ∘ a)
  let y := Sum.elim (z ∘ Sum.inr) (sec.representative ∘ b)
  have eq : Sum.elim z t ∘ reindex = Sum.elim x y := by funext n; rcases n with (n|n)|(n|n) <;> rfl
  change z ∈ residueGraphCode R ↔ Sum.elim z t ∘ reindex ∈ M
  rw [eq]
  have mixed {u w} (hu : residueRV O ∘ u = z ∘ Sum.inl) (hw : residueRV O ∘ w = z ∘ Sum.inr) :
      ((a,b),u,w) ∈ labelMatching c pull sec d f i j ↔ Sum.elim x y ∈ M := by
    change Sum.elim (Sum.elim (residueRV O ∘ u) _) (Sum.elim (residueRV O ∘ w) _) ∈ M ↔ _
    rw [hu,hw]
  constructor
  · rintro ⟨u,w,h,hu,hw⟩
    exact (mixed hu hw).mp ((slice a b hab u w).mp h)
  · intro h
    obtain ⟨hx,hy,_⟩ := (RVFamily.mem_representedMatches _ _ _ _ _ _ _).mp h
    obtain ⟨l,_,eqL⟩ := hx.1
    obtain ⟨r,_,eqR⟩ := hy.1
    have left : residueRV O ∘ (kernelResidue v ∘ l) = z ∘ Sum.inl :=
      (funext fun n => residueRV_kernel hv s hs (l n)).trans eqL
    have right : residueRV O ∘ (kernelResidue v ∘ r) = z ∘ Sum.inr :=
      (funext fun n => residueRV_kernel hv s hs (r n)).trans eqR
    exact ⟨_,_,(slice a b hab _ _).mpr ((mixed left right).mpr h),left,right⟩

end GeneralizedEuler.Section4.NormalRectangle
