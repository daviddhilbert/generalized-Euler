module

public import Section4.NormalRectangles
import all Section4.NormalRectangles
import all Section4.RectangleGeneration
import all Section4.CanonicalChartMaps
import all Section4.ResidueWeights
import all Section4.RectangleClasses
import all Section4.RectangleDecomposition

/-! Fixed-base partitions by actual definable bijections to homogeneous rectangles. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)}
variable (lang : ValueLanguage (J := JG) G)
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (base : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))

def HasRectangleCover {I : Type} (k : ℕ) (U : Set (I → RV0 O)) : Prop :=
  ∃ (l : ℕ) (A : Fin l → Set (I → RV0 O)) (c : Fin l → NormalRectangle (JG := JG) (G := G) O v hO P S k),
    Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (⋃ i, A i) = U ∧
    ∀ i, RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (A i) (c i).points

theorem standard_coded_residues {n r m} (A : ValueFrame G r n) (e : Fin m ≃ A.dependent) (B : Set (A.dependent → v.ker)) :
    unitSet O v (Equiv.refl _) {z | z ∘ e.symm ∈ B} = codedResidues O v A e B := by
  ext x; constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z ∘ e.symm,hz,funext fun j => by simp [unitTuple,codeTuple]⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨b ∘ e,by simpa [Function.comp_def] using hb,rfl⟩

include powers hs base in
theorem normal_chart_piece {n r m} (A : ValueFrame G r n) (e : Fin m ≃ A.dependent) (degree : m+r=n)
    (B : Set (A.dependent → v.ker)) (D : Set (Fin r → Additive O.ValueGroupˣ))
    (hd : (G : Set _).Definable JG D) (ne : D.Nonempty)
    (U : Set (Fin n → RV0 O)) (hu : isRVSet _ S U)
    (image : U = (fun w => codeTuple O (A.assemble v s w.1 w.2)) '' ({z | v ∘ z ∈ D} ×ˢ B)) :
    ∃ c : NormalRectangle (JG := JG) (G := G) O v hO P S n,
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier U c.points := by
  let W := {z : Fin r → Additive (PositiveRV O) | v ∘ z ∈ D} ×ˢ B
  have eqv := chart_definably_equivalent O P powers v s A e hO S W (fun i => base (A.shift i)) (image ▸ hu)
  have target := rectangle_image O v A e {z | v ∘ z ∈ D} B
  change codeRectangle O v A e '' W = productSet (codedResidues O v A e B) (positiveSharp O v D) at target
  rw [target,← image,← standard_coded_residues O v A e B] at eqv
  have hb := first_factor_definable (rv_equivalent_target_definable eqv) (positiveSharp_nonempty O v s hs D ne)
  exact ⟨⟨m,r,degree,_,D,hb,hd⟩,eqv⟩

include hs powers base lang pull in
theorem positive_rectangle_cover {n l} (U : Set (Fin n → RV0 O)) (hU : isRVSet _ S U)
    (pos : ∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) {Q : Set (Fin n → v.ker) → Prop}
    (p : Fin l → PositivePiece v G (fun _ D => (G : Set _).Definable JG D) Q)
    (supports : ∀ γ, ∃! i, γ ∈ (p i).value.support)
    (charts : ∀ i, ∃ e : (p i).rectangle ≃ (p i).carrier ((codeTuple O) ⁻¹' U), ∀ z,
      (e z).val = (p i).value.frame.assemble v s z.1.val z.2.val) :
    HasRectangleCover (JG := JG) (G := G) O v hO P S n U := by
  classical
  obtain ⟨C,hc,_,dj,cv,images⟩ := positive_partition_sets O v s hO P S lang @pull U hU pos p supports charts
  have model i : ∃ c : NormalRectangle (JG := JG) (G := G) O v hO P S n,
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (C i) c.points := by
    let A := (p i).value.frame
    let idx := (Fintype.equivFinOfCardEq (complement_count A.free)).symm
    have le := Fintype.card_le_of_injective A.free A.free.injective
    simp only [Fintype.card_fin] at le
    exact normal_chart_piece O v hO P powers S s hs base A idx (Nat.sub_add_cancel le) _ _
      (p i).value.definable ⟨_,(p i).value.independent.choose_spec.1⟩ _ (hc i) (images i)
  choose c h using model
  exact ⟨l,C,c,dj,cv,h⟩

end GeneralizedEuler.Section4
